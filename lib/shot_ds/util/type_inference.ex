defmodule ShotDs.Util.TypeInference do
  @moduledoc false
  # Contains functionality for type inference given a set of type constraints.
  # Utilizes Robinson's unification algorithm for type unification.

  alias ShotDs.Data.Type

  @typedoc """
  A substitution map mapping type variable references to resolved types.
  """
  @type type_substitution :: %{reference() => Type.t() | atom() | reference()}

  @typep general_type() :: Type.t() | reference() | atom()

  @doc """
  Tries to solve a list of type constraints by unification. Returns the
  computed substitution.
  """
  @spec solve([{Type.t(), Type.t()}]) :: type_substitution()
  def solve(constraints) do
    Enum.reduce(constraints, %{}, fn {t1, t2}, subst ->
      unify(apply_subst(t1, subst), apply_subst(t2, subst), subst)
    end)
  end

  @doc """
  Applies a type substitution to a given type or reference.
  """
  @spec apply_subst(general_type(), type_substitution()) :: general_type()
  def apply_subst(%Type{goal: g, args: args}, subst) do
    resolved_goal =
      if is_reference(g) do
        Map.get(subst, g, g) |> apply_subst(subst)
      else
        g
      end

    resolved_args = Enum.map(args, &apply_subst(&1, subst))

    Type.new(resolved_goal, resolved_args)
  end

  def apply_subst(ref, subst) when is_map_key(subst, ref),
    do: apply_subst(Map.get(subst, ref), subst)

  def apply_subst(other, _subst), do: other

  #############################################################################
  # UNIFICATION LOGIC
  #############################################################################

  @spec unify(general_type(), general_type(), type_substitution()) :: type_substitution()
  defp unify(%Type{goal: g1, args: a1} = t1, %Type{goal: g2, args: a2} = t2, subst) do
    len1 = length(a1)
    len2 = length(a2)

    cond do
      t1 == t2 ->
        subst

      len1 == len2 ->
        if !is_reference(g1) && !is_reference(g2) && g1 != g2 do
          raise "Type Error: Cannot unify concrete goals #{g1} and #{g2}."
        end

        subst_after_goal = unify_terms(g1, g2, subst)

        Enum.zip(a1, a2)
        |> Enum.reduce(subst_after_goal, fn {arg1, arg2}, acc_subst ->
          unify(apply_subst(arg1, acc_subst), apply_subst(arg2, acc_subst), acc_subst)
        end)

      len1 < len2 ->
        unify_partial(g1, a1, g2, a2, subst)

      len1 > len2 ->
        unify_partial(g2, a2, g1, a1, subst)
    end
  end

  # Fallbacks for raw variables/atoms directly
  defp unify(ref, %Type{} = t, subst) when is_reference(ref), do: bind(ref, t, subst)
  defp unify(%Type{} = t, ref, subst) when is_reference(ref), do: bind(ref, t, subst)
  defp unify(t1, t2, subst), do: unify_terms(t1, t2, subst)

  # Helper for unifying bases (atoms or references)
  defp unify_terms(t, t, subst), do: subst
  defp unify_terms(ref, t, subst) when is_reference(ref), do: bind(ref, t, subst)
  defp unify_terms(t, ref, subst) when is_reference(ref), do: bind(ref, t, subst)

  defp unify_terms(t1, t2, _subst) do
    raise "Type Error: Cannot unify #{inspect(t1)} with #{inspect(t2)}"
  end

  # Handles partial application unification
  defp unify_partial(g_short, a_short, g_long, a_long, subst) do
    if is_reference(g_short) do
      diff = length(a_long) - length(a_short)

      {extra_a_long, shared_a_long} = Enum.split(a_long, diff)

      subst_after_args =
        Enum.zip(a_short, shared_a_long)
        |> Enum.reduce(subst, fn {a1, a2}, acc ->
          unify(apply_subst(a1, acc), apply_subst(a2, acc), acc)
        end)

      tail_type = Type.new(g_long, extra_a_long)

      unify(
        apply_subst(g_short, subst_after_args),
        apply_subst(tail_type, subst_after_args),
        subst_after_args
      )
    else
      raise "Type Error: Cannot unify strict function types of different arities."
    end
  end

  # --- BINDING AND OCCURS CHECK ---

  defp bind(ref, type, subst) do
    if occurs?(ref, type) do
      raise "Type Error: Recursive type check failed (Occurs check on #{inspect(ref)})."
    end

    updated_subst =
      Map.new(subst, fn {k, v} ->
        {k, apply_subst(v, %{ref => type})}
      end)

    Map.put(updated_subst, ref, type)
  end

  defp occurs?(ref, %Type{goal: g, args: args}) do
    ref == g or Enum.any?(args, &occurs?(ref, &1))
  end

  defp occurs?(ref, term), do: ref == term
end

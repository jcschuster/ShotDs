defmodule ShotDs.Util.TypeInference do
  @moduledoc false
  # Robinson first-order unification for the rank-1 HM type system.
  # Used by the parser in W-style: each application/connective node calls
  # unify/3 immediately during the AST traversal, threading the running
  # substitution. The legacy constraint-set entry points (solve/solve!) are
  # kept as deprecated wrappers.

  alias ShotDs.Data.Type

  @typedoc """
  A substitution map mapping type variable references to resolved types.
  """
  @type type_substitution :: %{reference() => Type.t() | atom() | reference()}

  @typedoc """
  A type-shaped value accepted by `unify/3` and `apply_subst/2`: a full
  `Type.t()` struct, a bare reference (type variable), or an atom (concrete
  base type).
  """
  @type general_type() :: Type.t() | reference() | atom()

  defmodule TypeError do
    @moduledoc """
    An exception raised when type inference fails.
    """
    defexception message: "type error"
  end

  @doc """
  Unifies two types under the given substitution. Returns either an updated
  substitution that reconciles `t1` with `t2`, or an error.

  Both arguments are first resolved through the current substitution, so
  callers do not need to pre-apply themselves. Standard Robinson first-order
  unification with occurs check.

  This is the W-style entry point: the parser calls `unify/3` directly during
  AST traversal rather than collecting deferred constraints.
  """
  @spec unify(general_type(), general_type(), type_substitution()) ::
          {:ok, type_substitution()} | {:error, String.t()}
  def unify(t1, t2, subst) do
    do_unify(apply_subst(t1, subst), apply_subst(t2, subst), subst)
  end

  @doc """
  Unifies two types, raising a `TypeError` on failure.
  """
  @spec unify!(general_type(), general_type(), type_substitution()) :: type_substitution()
  def unify!(t1, t2, subst) do
    case unify(t1, t2, subst) do
      {:ok, new_subst} -> new_subst
      {:error, reason} -> raise TypeError, message: reason
    end
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
  # UNIFICATION LOGIC (internal)
  #############################################################################
  # The do_unify family assumes its inputs have already had the current
  # substitution applied. The public `unify/3` is responsible for that
  # apply_subst step.

  @spec do_unify(general_type(), general_type(), type_substitution()) ::
          {:ok, type_substitution()} | {:error, String.t()}
  defp do_unify(%Type{goal: g1, args: a1} = t1, %Type{goal: g2, args: a2} = t2, subst) do
    len1 = length(a1)
    len2 = length(a2)

    cond do
      t1 == t2 ->
        {:ok, subst}

      len1 == len2 ->
        unify_same_arity(g1, a1, g2, a2, subst)

      len1 < len2 ->
        unify_partial(g1, a1, g2, a2, subst)

      len1 > len2 ->
        unify_partial(g2, a2, g1, a1, subst)
    end
  end

  # Fallbacks for raw variables/atoms directly
  defp do_unify(ref, %Type{} = t, subst) when is_reference(ref), do: bind(ref, t, subst)
  defp do_unify(%Type{} = t, ref, subst) when is_reference(ref), do: bind(ref, t, subst)
  defp do_unify(t1, t2, subst), do: unify_terms(t1, t2, subst)

  # Helper for unifying bases (atoms or references)
  defp unify_terms(t, t, subst), do: {:ok, subst}
  defp unify_terms(ref, t, subst) when is_reference(ref), do: bind(ref, t, subst)
  defp unify_terms(t, ref, subst) when is_reference(ref), do: bind(ref, t, subst)

  defp unify_terms(t1, t2, _subst) do
    {:error, "Type Error: Cannot unify #{inspect(t1)} with #{inspect(t2)}"}
  end

  defp unify_same_arity(g1, a1, g2, a2, subst)
       when is_reference(g1) or is_reference(g2) or g1 == g2 do
    with {:ok, subst_after_goal} <- unify_terms(g1, g2, subst) do
      Enum.zip(a1, a2)
      |> Enum.reduce_while({:ok, subst_after_goal}, &reducer/2)
    end
  end

  defp unify_same_arity(g1, _, g2, _, _),
    do: {:error, "Type Error: Cannot unify concrete goals #{g1} and #{g2}."}

  defp reducer({arg1, arg2}, {:ok, acc_subst}) do
    case do_unify(apply_subst(arg1, acc_subst), apply_subst(arg2, acc_subst), acc_subst) do
      {:ok, new_subst} -> {:cont, {:ok, new_subst}}
      {:error, _} = err -> {:halt, err}
    end
  end

  # Handles partial application unification
  defp unify_partial(g_short, a_short, g_long, a_long, subst) when is_reference(g_short) do
    {shared_a_long, extra_a_long} = Enum.split(a_long, length(a_short))

    subst_after_args_result =
      Enum.zip(a_short, shared_a_long)
      |> Enum.reduce_while({:ok, subst}, fn {a1, a2}, {:ok, acc} ->
        case do_unify(apply_subst(a1, acc), apply_subst(a2, acc), acc) do
          {:ok, new_acc} -> {:cont, {:ok, new_acc}}
          {:error, _} = err -> {:halt, err}
        end
      end)

    case subst_after_args_result do
      {:ok, subst_after_args} ->
        tail_type = Type.new(g_long, extra_a_long)

        do_unify(
          apply_subst(g_short, subst_after_args),
          apply_subst(tail_type, subst_after_args),
          subst_after_args
        )

      {:error, _} = err ->
        err
    end
  end

  defp unify_partial(_, _, _, _, _),
    do: {:error, "Type Error: Cannot unify strict function types of different arities."}

  # --- BINDING AND OCCURS CHECK ---

  defp bind(ref, type, subst) do
    if occurs?(ref, type) do
      {:error, "Type Error: Recursive type check failed (Occurs check on #{inspect(ref)})."}
    else
      updated_subst =
        Map.new(subst, fn {k, v} ->
          {k, apply_subst(v, %{ref => type})}
        end)

      {:ok, Map.put(updated_subst, ref, type)}
    end
  end

  defp occurs?(ref, %Type{goal: g, args: args}) do
    ref == g or Enum.any?(args, &occurs?(ref, &1))
  end

  defp occurs?(ref, term), do: ref == term
end

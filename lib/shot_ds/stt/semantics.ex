defmodule ShotDs.Stt.Semantics do
  @moduledoc """
  Implements the semantics of Church's simple type theory. The most important
  functions are `subst/2` and `subst!/2`, which apply substitutions to a given
  term.
  """

  alias ShotDs.Data.{Type, Declaration, Term, Substitution}
  alias ShotDs.Stt.TermFactory, as: TF
  import ShotDs.Util.TermTraversal

  ##############################################################################
  # SUBSTITUTION LOGIC
  ##############################################################################

  @doc """
  Applies a singular substitution or a list of substitutions left to right to
  the term with the given id, propagating any lookup or type errors.
  """
  @spec subst([Substitution.t()] | Substitution.t(), Term.term_id()) ::
          {:ok, Term.term_id()} | TF.lookup_error_t() | {:error, :incompatible_types}
  def subst(substitutions, term_id)

  def subst([s | ss], term_id) do
    with {:ok, next_id} <- subst(s, term_id), do: subst(ss, next_id)
  end

  def subst([], term_id), do: {:ok, term_id}

  def subst(%Substitution{fvar: fvar, term_id: replacement_id}, term_id) do
    update_env = fn term, depth -> depth + length(term.bvars) end
    short_circuit = fn term, _depth -> fvar not in term.fvars end

    transform = fn term, new_args, depth, acc_cache ->
      if term.head == fvar do
        subst_matched(term, new_args, depth, replacement_id, fvar, acc_cache)
      else
        subst_unmatched(term, new_args, acc_cache)
      end
    end

    case map_term(term_id, 0, update_env, transform, short_circuit) do
      {:ok, {new_id, _cache}} -> {:ok, new_id}
      error -> error
    end
  end

  defp subst_matched(
         %Term{fvars: fvars, bvars: bvars},
         new_args,
         depth,
         replacement_id,
         fvar,
         acc_cache
       ) do
    shift_cache = Map.get(acc_cache, {:shift_cache, depth}, %{})

    with {:ok, {shifted_replacement_id, next_shift_cache}} <-
           shift(replacement_id, depth, 0, shift_cache),
         {:ok, reduced_id} <- TF.fold_apply(shifted_replacement_id, new_args),
         {:ok, %Term{bvars: red_bvars, fvars: red_fvars} = reduced_body} <-
           TF.get_term(reduced_id),
         shifted_bvars = Enum.map(bvars, fn bv -> %{bv | name: bv.name + length(red_bvars)} end),
         combined_bvars = shifted_bvars ++ red_bvars,
         {:ok, new_max_num} <-
           calc_new_max_num(reduced_body.head, reduced_body.args, combined_bvars) do
      final_fvars = Enum.uniq(List.delete(fvars, fvar) ++ red_fvars)
      new_type = Type.new(reduced_body.type, Enum.map(bvars, & &1.type))

      wrapped_term = %Term{
        reduced_body
        | bvars: combined_bvars,
          fvars: final_fvars,
          type: new_type,
          max_num: new_max_num
      }

      final_acc_cache = Map.put(acc_cache, {:shift_cache, depth}, next_shift_cache)

      {{:ok, TF.memoize(wrapped_term)}, final_acc_cache}
    else
      error -> {error, acc_cache}
    end
  end

  defp subst_unmatched(term, new_args, acc_cache) do
    with {:ok, new_fvars} <- calc_new_fvars(term.head, new_args),
         {:ok, new_max_num} <- calc_new_max_num(term.head, new_args, term.bvars) do
      new_term = %{term | args: new_args, fvars: new_fvars, max_num: new_max_num}
      {{:ok, TF.memoize(new_term)}, acc_cache}
    else
      error -> {error, acc_cache}
    end
  end

  @doc """
  Applies a singular substitution or a list of substitutions left to right to
  the term with the given id, erroring out if it encounters an invalid ID.
  """
  @spec subst!([Substitution.t()] | Substitution.t(), Term.term_id()) :: Term.term_id()
  def subst!(substitutions, term_id) do
    case subst(substitutions, term_id) do
      {:ok, new_id} -> new_id
      {:error, reason} -> raise ArgumentError, message: inspect(reason)
    end
  end

  @doc """
  Adds a new substitution to a list of substitutions by applying it to every
  member and prepending it, propagating errors.
  """
  @spec add_subst([Substitution.t()], Substitution.t()) ::
          {:ok, [Substitution.t()]} | TF.lookup_error_t()
  def add_subst(substs, %Substitution{} = new_subst) do
    Enum.reduce_while(substs, {:ok, [new_subst]}, fn s, {:ok, acc} ->
      case subst(new_subst, s.term_id) do
        {:ok, new_id} -> {:cont, {:ok, [%{s | term_id: new_id} | acc]}}
        error -> {:halt, error}
      end
    end)
    |> case do
      {:ok, rev_acc} -> {:ok, Enum.reverse(rev_acc)}
      error -> error
    end
  end

  @doc """
  Adds a new substitution to a list of substitutions by applying it to every
  member and prepending it, raising on errors.
  """
  @spec add_subst!([Substitution.t()], Substitution.t()) :: [Substitution.t()]
  def add_subst!(substs, %Substitution{} = new_subst) do
    applied =
      Enum.map(substs, fn %Substitution{term_id: t_id} = s ->
        %{s | term_id: subst!(new_subst, t_id)}
      end)

    [new_subst | applied]
  end

  ##############################################################################
  # SHIFT AND INSTANTIATION
  ##############################################################################

  @doc """
  Applies a *d*-shift above cutoff *c* to the term with the given id.
  """
  @spec shift(Term.term_id(), integer(), non_neg_integer(), map()) ::
          {:ok, {Term.term_id(), map()}} | TF.lookup_error_t()
  def shift(term_id, d, c \\ 0, cache \\ %{}) do
    update_env = fn term, current_c -> current_c + length(term.bvars) end

    transform = fn %Term{head: head, bvars: bvars} = term, new_args, current_c, acc_cache ->
      new_head =
        case head do
          %Declaration{kind: :bv, name: index, type: type} when index > current_c ->
            Declaration.new_bound_var(index + d, type)

          decl ->
            decl
        end

      case calc_new_max_num(new_head, new_args, bvars) do
        {:ok, new_max_num} ->
          new_term = %Term{term | head: new_head, args: new_args, max_num: new_max_num}
          {{:ok, TF.memoize(new_term)}, acc_cache}

        error ->
          {error, acc_cache}
      end
    end

    short_circuit = fn term, current_c -> term.max_num <= current_c end

    map_term(term_id, c, update_env, transform, short_circuit, cache)
  end

  @doc """
  Applies a *d*-shift above cutoff *c* to the term with the given id, raising on
  invalid IDs.
  """
  @spec shift!(Term.term_id(), integer(), non_neg_integer(), map()) :: {Term.term_id(), map()}
  def shift!(term_id, d, c \\ 0, cache \\ %{}) do
    case shift(term_id, d, c, cache) do
      {:ok, {new_id, final_cache}} -> {new_id, final_cache}
      {:error, reason} -> raise ArgumentError, message: inspect(reason)
    end
  end

  @doc """
  Instantiates the bound variable with index *k* with the replacement term
  corresponding to the given id, safely propagating errors.
  """
  @spec instantiate(Term.term_id(), pos_integer(), Term.term_id(), map()) ::
          {:ok, {Term.term_id(), map()}} | TF.lookup_error_t() | {:error, :incompatible_types}
  def instantiate(term_id, k, replacement_id, cache \\ %{}) do
    update_env = fn term, current_k -> current_k + length(term.bvars) end

    transform = fn term, new_args, current_k, acc_cache ->
      instantiate_transform(term, new_args, current_k, acc_cache, k, replacement_id)
    end

    map_term(term_id, k, update_env, transform, fn _, _ -> false end, cache)
  end

  defp instantiate_transform(
         %Term{head: %Declaration{kind: :bv, name: index}, bvars: bvars},
         new_args,
         current_k,
         acc_cache,
         k,
         replacement_id
       )
       when index == current_k do
    shift_amount = current_k - k
    shift_cache = Map.get(acc_cache, {:shift_cache, shift_amount}, %{})

    with {:ok, {shifted_replacement_id, next_shift_cache}} <-
           shift(replacement_id, shift_amount, 0, shift_cache),
         {:ok, reduced_body_id} <- TF.fold_apply(shifted_replacement_id, new_args),
         {:ok, %Term{bvars: red_bvars, max_num: red_max} = reduced_body} <-
           TF.get_term(reduced_body_id) do
      shifted_bvars = Enum.map(bvars, fn bv -> %{bv | name: bv.name + length(red_bvars)} end)
      combined_bvars = shifted_bvars ++ red_bvars

      new_type = Type.new(reduced_body.type, Enum.map(bvars, & &1.type))

      bvar_maxes = Enum.map(combined_bvars, & &1.name)
      new_max_num = Enum.max([red_max | bvar_maxes], fn -> 0 end)

      wrapped_term = %Term{
        reduced_body
        | bvars: combined_bvars,
          type: new_type,
          max_num: new_max_num
      }

      final_acc_cache = Map.put(acc_cache, {:shift_cache, shift_amount}, next_shift_cache)

      {{:ok, TF.memoize(wrapped_term)}, final_acc_cache}
    else
      error -> {error, acc_cache}
    end
  end

  defp instantiate_transform(
         %Term{head: %Declaration{kind: :bv, name: index, type: type}, bvars: bvars} = term,
         new_args,
         current_k,
         acc_cache,
         _k,
         _replacement_id
       )
       when index > current_k do
    new_head = Declaration.new_bound_var(index - 1, type)

    with {:ok, new_max_num} <- calc_new_max_num(new_head, new_args, bvars),
         {:ok, new_fvars} <- calc_new_fvars(new_head, new_args) do
      new_term = %Term{
        term
        | head: new_head,
          args: new_args,
          fvars: new_fvars,
          max_num: new_max_num
      }

      {{:ok, TF.memoize(new_term)}, acc_cache}
    else
      error -> {error, acc_cache}
    end
  end

  defp instantiate_transform(
         %Term{head: head_decl, bvars: bvars} = term,
         new_args,
         _current_k,
         acc_cache,
         _k,
         _replacement_id
       ) do
    with {:ok, new_max_num} <- calc_new_max_num(head_decl, new_args, bvars),
         {:ok, new_fvars} <- calc_new_fvars(head_decl, new_args) do
      new_term = %Term{term | args: new_args, fvars: new_fvars, max_num: new_max_num}
      {{:ok, TF.memoize(new_term)}, acc_cache}
    else
      error -> {error, acc_cache}
    end
  end

  @doc """
  Instantiates the bound variable with index *k* with the replacement term
  corresponding to the given id, raising on errors. Uses caching for efficient
  computation.
  """
  @spec instantiate!(Term.term_id(), pos_integer(), Term.term_id(), map()) ::
          {Term.term_id(), map()}
  def instantiate!(term_id, k, replacement_id, cache \\ %{}) do
    case instantiate(term_id, k, replacement_id, cache) do
      {:ok, {new_id, final_cache}} -> {new_id, final_cache}
      {:error, reason} -> raise ArgumentError, message: inspect(reason)
    end
  end

  ##############################################################################
  # HELPERS
  ##############################################################################

  defp calc_new_max_num(head_decl, arg_ids, bvars) do
    head_max =
      case head_decl do
        %Declaration{kind: :bv, name: n} -> n
        _ -> 0
      end

    bvar_maxes = Enum.map(bvars, & &1.name)

    Enum.reduce_while(arg_ids, {:ok, []}, fn id, {:ok, acc} ->
      case TF.get_term(id) do
        {:ok, term} -> {:cont, {:ok, [term.max_num | acc]}}
        error -> {:halt, error}
      end
    end)
    |> case do
      {:ok, arg_maxes} -> {:ok, Enum.max([head_max | arg_maxes ++ bvar_maxes], fn -> 0 end)}
      error -> error
    end
  end

  defp calc_new_fvars(head_decl, arg_ids) do
    head_fvars =
      case head_decl do
        %Declaration{kind: :fv} -> [head_decl]
        _ -> []
      end

    Enum.reduce_while(arg_ids, {:ok, []}, fn id, {:ok, acc} ->
      case TF.get_term(id) do
        {:ok, term} -> {:cont, {:ok, [term.fvars | acc]}}
        error -> {:halt, error}
      end
    end)
    |> case do
      {:ok, nested_fvars} -> {:ok, Enum.uniq(head_fvars ++ List.flatten(nested_fvars))}
      error -> error
    end
  end
end

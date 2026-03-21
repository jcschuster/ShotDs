defmodule ShotDs.Stt.Semantics do
  @moduledoc """
  Implements the semantics of Church's simple type theory. The most important
  function is `subst/2`, which applies substitutions to a given term.
  """

  alias ShotDs.Data.{Type, Declaration, Term, Substitution}
  alias ShotDs.Stt.TermFactory, as: TF
  import ShotDs.Util.TermTraversal

  ##############################################################################
  # SUBSTITUTION LOGIC
  ##############################################################################

  @doc """
  Applies a singular substitution or a list of substitutions left to right to
  the term with the given id.
  """
  @spec subst([Substitution.t()] | Substitution.t(), Term.term_id()) :: Term.term_id()
  def subst(substitutions, term_id)

  def subst([s | ss], term_id), do: subst(ss, subst(s, term_id))
  def subst([], term_id), do: term_id

  def subst(%Substitution{fvar: fvar, term_id: replacement_id}, term_id) do
    update_env = fn term, depth -> depth + length(term.bvars) end

    short_circuit = fn term, _depth -> fvar not in term.fvars end

    transform = fn %Term{head: head, fvars: fvars, bvars: bvars} = term,
                   new_args,
                   depth,
                   acc_cache ->
      if head == fvar do
        {shifted_replacement_id, acc_cache} = shift(replacement_id, depth, 0, acc_cache)

        reduced_id = TF.fold_apply(shifted_replacement_id, new_args)

        %Term{bvars: red_bvars, fvars: red_fvars} = reduced_body = TF.get_term(reduced_id)

        combined_bvars = bvars ++ red_bvars
        final_fvars = Enum.uniq(List.delete(fvars, fvar) ++ red_fvars)
        new_type = Type.new(reduced_body.type, Enum.map(bvars, & &1.type))

        new_max_num = calc_new_max_num(reduced_body.head, reduced_body.args, combined_bvars)

        wrapped_term = %Term{
          reduced_body
          | bvars: combined_bvars,
            fvars: final_fvars,
            type: new_type,
            max_num: new_max_num
        }

        {TF.memoize(wrapped_term), acc_cache}
      else
        new_fvars = calc_new_fvars(head, new_args)
        new_max_num = calc_new_max_num(term.head, new_args, term.bvars)

        new_term = %Term{term | args: new_args, fvars: new_fvars, max_num: new_max_num}
        {TF.memoize(new_term), acc_cache}
      end
    end

    {new_id, _cache} = map_term(term_id, 0, update_env, transform, short_circuit)
    new_id
  end

  @doc """
  Adds a new substitution to a list of substitutions by applying it to every
  member and prepending it.
  """
  @spec add_subst([Substitution.t()], Substitution.t()) :: [Substitution.t()]
  def add_subst(substs, %Substitution{} = new_subst) do
    applied =
      Enum.map(substs, fn %Substitution{term_id: t_id} = s ->
        %Substitution{s | term_id: subst(new_subst, t_id)}
      end)

    [new_subst | applied]
  end

  ##############################################################################
  # SHIFT AND INSTANTIATION
  ##############################################################################

  @doc """
  Applies a *d*-shift above cutoff *c* to the term with the given id, i.e., all
  bound variables with index > *c* are shifted by *d*.
  """
  @spec shift(Term.term_id(), integer(), non_neg_integer(), map()) :: {Term.term_id(), map()}
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

      new_max_num = calc_new_max_num(new_head, new_args, bvars)

      new_term = %Term{term | head: new_head, args: new_args, max_num: new_max_num}
      {TF.memoize(new_term), acc_cache}
    end

    short_circuit = fn term, current_c -> term.max_num <= current_c end

    map_term(term_id, c, update_env, transform, short_circuit, cache)
  end

  @doc """
  Instantiates the bound variable with index *k* with the replacement term
  corresponding to the given id. Uses caching for efficient computation.
  """
  @spec instantiate(Term.term_id(), pos_integer(), Term.term_id(), map()) ::
          {Term.term_id(), map()}
  def instantiate(term_id, k, replacement_id, cache \\ %{}) do
    update_env = fn term, current_k -> current_k + length(term.bvars) end

    transform = fn
      %Term{head: %Declaration{kind: :bv, name: index}, bvars: bvars},
      new_args,
      current_k,
      acc_cache
      when index == current_k ->
        shift_amount = current_k - k
        {shifted_replacement_id, acc_cache} = shift(replacement_id, shift_amount, 0, acc_cache)

        reduced_body_id = TF.fold_apply(shifted_replacement_id, new_args)

        %Term{bvars: red_bvars, max_num: red_max} = reduced_body = TF.get_term(reduced_body_id)
        combined_bvars = bvars ++ red_bvars

        bvar_maxes = Enum.map(combined_bvars, & &1.name)
        new_max_num = Enum.max([red_max | bvar_maxes], fn -> 0 end)

        wrapped_term = %Term{reduced_body | bvars: combined_bvars, max_num: new_max_num}
        {TF.memoize(wrapped_term), acc_cache}

      %Term{head: %Declaration{kind: :bv, name: index, type: type}, bvars: bvars} = term,
      new_args,
      current_k,
      acc_cache
      when index > current_k ->
        new_head = Declaration.new_bound_var(index - 1, type)
        new_max_num = calc_new_max_num(new_head, new_args, bvars)
        new_fvars = calc_new_fvars(new_head, new_args)

        new_term = %Term{
          term
          | head: new_head,
            args: new_args,
            fvars: new_fvars,
            max_num: new_max_num
        }

        {TF.memoize(new_term), acc_cache}

      %Term{head: head_decl, bvars: bvars} = term, new_args, _, acc_cache ->
        new_max_num = calc_new_max_num(head_decl, new_args, bvars)
        new_fvars = calc_new_fvars(head_decl, new_args)

        new_term = %Term{term | args: new_args, fvars: new_fvars, max_num: new_max_num}
        {TF.memoize(new_term), acc_cache}
    end

    map_term(term_id, k, update_env, transform, fn _, _ -> false end, cache)
  end

  defp calc_new_max_num(head_decl, arg_ids, bvars) do
    head_max =
      case head_decl do
        %Declaration{kind: :bv, name: n} -> n
        _ -> 0
      end

    arg_maxes = Enum.map(arg_ids, fn id -> TF.get_term(id).max_num end)
    bvar_maxes = Enum.map(bvars, & &1.name)
    Enum.max([head_max | arg_maxes ++ bvar_maxes], fn -> 0 end)
  end

  defp calc_new_fvars(head_decl, arg_ids) do
    head_fvars =
      case head_decl do
        %Declaration{kind: :fv} -> [head_decl]
        _ -> []
      end

    arg_fvars = Enum.flat_map(arg_ids, fn id -> TF.get_term(id).fvars end)
    Enum.uniq(head_fvars ++ arg_fvars)
  end
end

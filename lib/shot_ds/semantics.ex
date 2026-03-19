defmodule ShotDs.Semantics do
  @moduledoc """
  Implements the semantics of Church's simple type theory.

  The most important functions are `subst/2`, `make_abstr_term/2` and
  `make_appl_term/2` which handle memoization and beta-eta normalization.
  """

  alias ShotDs.Data.{Type, Declaration, Term, Substitution}
  alias ShotDs.TermFactory, as: TF
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

        reduced_id = fold_apply(shifted_replacement_id, new_args)

        %Term{bvars: red_bvars, fvars: red_fvars} = reduced_body = TF.get_term(reduced_id)

        combined_bvars = bvars ++ red_bvars
        final_fvars = Enum.uniq(List.delete(fvars, fvar) ++ red_fvars)

        new_max_num = calc_new_max_num(reduced_body.head, reduced_body.args, combined_bvars)

        wrapped_term = %Term{
          reduced_body
          | bvars: combined_bvars,
            fvars: final_fvars,
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

  def add_subst(
        substs,
        %Substitution{fvar: %Declaration{name: name}} = new_subst,
        fvar_tags_blacklist \\ []
      ) do
    applied =
      Enum.map(substs, fn %Substitution{term_id: t_id} = s ->
        %Substitution{s | term_id: subst(new_subst, t_id)}
      end)

    if is_tuple(name) and elem(name, 1) in fvar_tags_blacklist do
      applied
    else
      [new_subst | applied]
    end
  end

  # Binds all occurrences of fvar in the term with id term_id
  @spec bind_var(Declaration.free_var_t(), Term.term_id()) :: Term.term_id()
  defp bind_var(%Declaration{kind: :fv} = fvar, term_id) do
    update_env = fn term, depth -> depth + length(term.bvars) end
    short_circuit = fn term, _depth -> fvar not in term.fvars end

    transform = fn %Term{head: head, fvars: fvars} = term, new_args, depth, acc_cache ->
      new_fvars = List.delete(fvars, fvar)
      new_head = if head == fvar, do: Declaration.new_bound_var(depth + 1, fvar.type), else: head

      new_max_num = calc_new_max_num(new_head, new_args, term.bvars)

      new_term = %Term{
        term
        | head: new_head,
          args: new_args,
          fvars: new_fvars,
          max_num: new_max_num
      }

      {TF.memoize(new_term), acc_cache}
    end

    {new_id, _cache} = map_term(term_id, 0, update_env, transform, short_circuit)
    new_id
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

        reduced_body_id = fold_apply(shifted_replacement_id, new_args)

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

  ##############################################################################
  # ABSTRACTION & APPLICATION
  ##############################################################################

  @doc """
  Abstracts the term corresponding to the given id over the given variable. If
  the variable is already bound, adds it to the list of bound variables.
  """
  @spec make_abstr_term(Term.term_id(), Declaration.t()) :: Term.term_id()
  def make_abstr_term(term_id, %Declaration{kind: var_kind, name: var_name, type: var_type} = var) do
    %Term{bvars: bvars, type: term_type, fvars: fvars, max_num: max_num} =
      draft_term = TF.get_term(term_id)

    case var_kind do
      :fv ->
        bv = Declaration.new_bound_var(max_num + 1, var_type)
        substituted = if var in fvars, do: bind_var(var, term_id), else: term_id
        make_abstr_term(substituted, bv)

      :bv ->
        new_type = Type.new(term_type, var_type)
        new_max = max(var_name, max_num)

        %Term{draft_term | bvars: [var | bvars], type: new_type, max_num: new_max}
        |> TF.memoize()
    end
  end

  @doc """
  Applies the term corresponding to `left_id` to the term corresponding to
  `right_id`.
  """
  @spec make_appl_term(Term.term_id(), Term.term_id()) :: Term.term_id()
  def make_appl_term(left_id, right_id) do
    %Term{} = left_term = TF.get_term(left_id)
    right_term = TF.get_term(right_id)

    %Type{goal: goal_type, args: [arg1 | rest_types]} = left_term.type

    # This will throw an error if the types are not compatible
    ^arg1 = TF.get_term(right_id).type

    new_type = Type.new(goal_type, rest_types)

    case left_term.bvars do
      [] ->
        new_args = left_term.args ++ [right_id]
        new_fvars = Enum.uniq(left_term.fvars ++ right_term.fvars)
        new_max_num = max(left_term.max_num, right_term.max_num)

        %Term{left_term | args: new_args, type: new_type, fvars: new_fvars, max_num: new_max_num}
        |> TF.memoize()

      [_b | bs] ->
        body_term = %Term{left_term | bvars: bs, type: new_type, max_num: left_term.max_num - 1}
        body_id = TF.memoize(body_term)
        {reduced_id, _cache} = instantiate(body_id, 1, right_id)
        reduced_id
    end
  end

  @doc """
  Applies the term corresponding to `head_id` to the list of terms
  corresponding to `arg_ids`.
  """
  @spec fold_apply(Term.term_id(), [Term.term_id()]) :: Term.term_id()
  def fold_apply(head_id, arg_ids) do
    Enum.reduce(arg_ids, head_id, &make_appl_term(&2, &1))
  end
end

defmodule ShotDs.TermFactory do
  @moduledoc groups: [:"Term Cache", :"Term Construction API"]
  @moduledoc """
  Contains functionality of creating, memoizing and accessing terms using an
  ETS cache.

  In Hol, terms often share sub-expressions, meaning they form Directed Acyclic
  Graphs (DAGs) rather than simple abstract syntax trees (ASTs). Hence,
  representing terms as nested sturctures has the big disadvantage of needing
  to store the same sub-expression multiple times in memory. ETS, the Erlang
  Term Storage offers an efficient caching mechanism which we can utilize to
  ensure that a specific term is created exactly once. Furthermore, Elixir's
  immutability ensures pointers to the terms being static, i.e., a term can not
  be altered once it is memoized.
  """

  alias ShotDs.Data.Declaration
  alias ShotDs.Data.Term
  alias ShotDs.Data.Type
  import ShotDs.Semantics
  import ShotDs.Util.TermTraversal

  @table :term_pool
  @dummy_id 0

  @doc group: :"Term Cache"
  @doc """
  Memoizes the given term in the module's `:ets` table. Terms will be
  identified if they share the same *signature*, e.g., all fields but `id`.

  Returns the looked up or generated ID of the term. ID's are generated as
  positive integers in a concurrency-safe way.

  ## Example:

      iex> id = memoize(t)
      iex> {t | id: id} == get_term(id)
      true
  """
  @spec memoize(Term.t()) :: Term.term_id()
  def memoize(%Term{} = draft_term) do
    signature = get_signature(draft_term)

    case :ets.lookup(@table, signature) do
      [{^signature, existing_id}] ->
        existing_id

      [] ->
        new_id = :ets.update_counter(@table, :id_counter, {2, 1})

        if :ets.insert_new(@table, {signature, new_id}) do
          term = %Term{draft_term | id: new_id}
          :ets.insert(@table, {new_id, term})
          new_id
        else
          # Another process inserted this signature in between
          [{^signature, winning_id}] = :ets.lookup(@table, signature)
          winning_id
        end
    end
  end

  defp get_signature(%Term{bvars: b, head: h, args: a, type: t, fvars: f, max_num: m}) do
    {b, h, a, t, f, m}
  end

  @doc group: :"Term Cache"
  @doc """
  Looks up and returns the concrete `ShotDs.Data.Term` struct for the given
  ID. Terms are ensured to exist in the module's ETS cache if they are solely
  generated via the provided API in this module.
  """
  @spec get_term(Term.term_id()) :: Term.t()
  def get_term(id) do
    case :ets.lookup(@table, id) do
      [] ->
        raise "Terms should only be constructed via the TermFactory module, not via struct initialization!"

      [{^id, term}] ->
        term
    end
  end

  ##############################################################################
  # TERM CONSTRUCTION API
  ##############################################################################

  @doc group: :"Term Construction API"
  @doc """
  Creates and memoizes a term representing a single free variable, bound
  variable or constant. Handles eta-expansion automatically.

  ## Example:

      iex> co = ShotDs.Data.Declaration.fresh_const(Type.new(:o))
      iex> id = make_term(co)
  """
  @spec make_term(Declaration.t()) :: Term.term_id()
  def make_term(%Declaration{kind: kind, type: type} = decl) do
    fvars = if kind == :fv, do: [decl], else: []

    case type do
      %Type{args: []} ->
        %Term{id: @dummy_id, head: decl, type: type, fvars: fvars}
        |> memoize()

      %Type{goal: goal_type, args: arg_types} ->
        new_vars = Enum.map(arg_types, &Declaration.fresh_var/1)
        new_arg_ids = Enum.map(new_vars, &make_term/1)

        max_num =
          new_arg_ids
          |> Enum.map(fn id -> get_term(id).max_num end)
          |> Enum.max(fn -> 0 end)

        base_term = %Term{
          id: @dummy_id,
          head: decl,
          args: new_arg_ids,
          type: Type.new(goal_type),
          fvars: fvars ++ new_vars,
          max_num: max_num
        }

        base_term_id = memoize(base_term)

        List.foldr(new_vars, base_term_id, &make_abstr_term(&2, &1))
    end
  end

  @doc group: :"Term Construction API"
  @doc """
  Creates a free variable with the corresponding name and type and returns the
  ID for its term representation. Short for
  `ShotDs.Data.Declaration.new_free_var(name, type) |> make_term()`.
  """
  @spec make_free_var_term(String.t() | reference(), Type.t()) :: Term.term_id()
  def make_free_var_term(name, %Type{} = type) do
    Declaration.new_free_var(name, type) |> make_term()
  end

  @doc group: :"Term Construction API"
  @doc """
  Creates a fresh variable of the given type and returns the ID for its term
  representation. Short for
  `ShotDs.Data.Declaration.fresh_var(type) |> make_term()`.
  """
  @spec make_fresh_var_term(Type.t()) :: Term.term_id()
  def make_fresh_var_term(%Type{} = type) do
    Declaration.fresh_var(type) |> make_term()
  end

  @doc group: :"Term Construction API"
  @doc """
  Creates a constant with the corresponding name and type and returns the ID
  for its term representation. Short for
  `ShotDs.Data.Declaration.new_const(name, type) |> make_term()`.
  """
  @spec make_const_term(String.t() | reference(), Type.t()) :: Term.term_id()
  def make_const_term(name, %Type{} = type) do
    Declaration.new_const(name, type) |> make_term()
  end

  @doc group: :"Term Construction API"
  @doc """
  Creates a fresh constant of the given type and returns the ID for its term
  representation. Short for
  `ShotDs.Data.Declaration.fresh_const(type) |> make_term()`.
  """
  @spec make_fresh_const_term(Type.t()) :: Term.term_id()
  def make_fresh_const_term(%Type{} = type) do
    Declaration.fresh_const(type) |> make_term()
  end

  ##############################################################################
  # ABSTRACTION & APPLICATION
  ##############################################################################

  @doc """
  Abstracts the term corresponding to the given id over the given variable. If
  the variable is already bound, adds it to the list of bound variables.

  #### Note {: .info}

  Consider using `ShotDs.Hol.Dsl.lambda/2` instead as it is more expressive and
  robust.
  """
  @spec make_abstr_term(Term.term_id(), Declaration.t()) :: Term.term_id()
  def make_abstr_term(term_id, %Declaration{kind: var_kind, name: var_name, type: var_type} = var) do
    %Term{bvars: bvars, type: term_type, fvars: fvars, max_num: max_num} =
      draft_term = get_term(term_id)

    case var_kind do
      :fv ->
        bv = Declaration.new_bound_var(max_num + 1, var_type)
        substituted = if var in fvars, do: bind_var(var, term_id), else: term_id
        make_abstr_term(substituted, bv)

      :bv ->
        new_type = Type.new(term_type, var_type)
        new_max = max(var_name, max_num)

        %Term{draft_term | bvars: [var | bvars], type: new_type, max_num: new_max}
        |> memoize()
    end
  end

  @doc """
  Applies the term corresponding to `left_id` to the term corresponding to
  `right_id`.

  #### Note {: .info}

  Consider using `ShotDs.Hol.Dsl.app/2` instead as it is more expressive and
  robust.
  """
  @spec make_appl_term(Term.term_id(), Term.term_id()) :: Term.term_id()
  def make_appl_term(left_id, right_id) do
    %Term{} = left_term = get_term(left_id)
    right_term = get_term(right_id)

    %Type{goal: goal_type, args: [arg1 | rest_types]} = left_term.type

    # This will throw an error if the types are not compatible
    ^arg1 = get_term(right_id).type

    new_type = Type.new(goal_type, rest_types)

    case left_term.bvars do
      [] ->
        new_args = left_term.args ++ [right_id]
        new_fvars = Enum.uniq(left_term.fvars ++ right_term.fvars)
        new_max_num = max(left_term.max_num, right_term.max_num)

        %Term{left_term | args: new_args, type: new_type, fvars: new_fvars, max_num: new_max_num}
        |> memoize()

      [_b | bs] ->
        body_term = %Term{left_term | bvars: bs, type: new_type, max_num: left_term.max_num - 1}
        body_id = memoize(body_term)
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

      {memoize(new_term), acc_cache}
    end

    {new_id, _cache} = map_term(term_id, 0, update_env, transform, short_circuit)
    new_id
  end

  defp calc_new_max_num(head_decl, arg_ids, bvars) do
    head_max =
      case head_decl do
        %Declaration{kind: :bv, name: n} -> n
        _ -> 0
      end

    arg_maxes = Enum.map(arg_ids, fn id -> get_term(id).max_num end)
    bvar_maxes = Enum.map(bvars, & &1.name)
    Enum.max([head_max | arg_maxes ++ bvar_maxes], fn -> 0 end)
  end
end

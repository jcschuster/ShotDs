defmodule ShotDs.Stt.TermFactory do
  @moduledoc groups: [:"Term Cache", :"Term Scratchpad", :"Term Construction API"]
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

  > #### Note {: .info}
  >
  > Consider using the more expressive API defined in `ShotDs.Hol.Dsl` ontop of
  > this module.
  """

  alias ShotDs.Data.Declaration
  alias ShotDs.Data.Term
  alias ShotDs.Data.Type
  import ShotDs.Stt.Semantics
  import ShotDs.Util.TermTraversal

  @table :term_pool
  @dummy_id 0

  @doc group: :"Term Scratchpad"
  @doc """
  Creates a local "scratchpad" ETS table for the current process. Can be used to
  cleanup temporary free variable terms e.g., when creating abstraction terms.

  Puts the reference to the ETS table in the processes memory under the
  `:term_scratchpad` key.
  """
  def start_scratchpad do
    table = :ets.new(:scratchpad, [:set, :private])
    :ets.insert(table, {:id_counter, 0})
    Process.put(:term_scratchpad, table)
  end

  @doc group: :"Term Scratchpad"
  @doc """
  Destroys the processes ephemeral ETS table explicitly.

  > #### Note {: .info}
  >
  > The scratchpad ETS table also dies with the process automatically.
  """
  def stop_scratchpad do
    if table = Process.get(:term_scratchpad) do
      :ets.delete(table)
      Process.delete(:term_scratchpad)
    end
  end

  @doc group: :"Term Scratchpad"
  @doc """
  Commits the term with the given ID (which might be local) to the global ETS
  table. Returns the new global ID.

  Also ensures recursively that the arguments are memoized.
  """
  def commit_to_global(id) when id > 0, do: id

  def commit_to_global(id) when id < 0 do
    %Term{} = term = get_term(id)

    committed_args = Enum.map(term.args, &commit_to_global/1)

    draft_term = %Term{term | args: committed_args}

    signature = get_signature(draft_term)

    case :ets.lookup(@table, signature) do
      [{^signature, existing_id}] -> existing_id
      [] -> generate_concurrent_id(draft_term)
    end
  end

  @doc group: :"Term Scratchpad"
  @doc """
  Wraps the given function and executes it with an active scratchpad. Commits
  the final result to the global ETS table Cleans up the scratchpad afterwards
  if it didn't exist previously. Acts as a concurrency-safe garbage collector.
  """
  def with_scratchpad(fun) do
    my_responsibility? = is_nil(Process.get(:term_scratchpad))

    if my_responsibility? do
      start_scratchpad()
    end

    try do
      result_id = fun.()

      if my_responsibility? do
        commit_to_global(result_id)
      else
        result_id
      end
    after
      if my_responsibility? do
        stop_scratchpad()
      end
    end
  end

  @doc group: :"Term Cache"
  @doc """
  Memoizes the given term in the module's `:ets` table. Terms will be
  identified if they share the same *signature*, e.g., all fields but `id`.

  Returns the looked up or generated ID of the term. ID's are generated as
  positive integers in a concurrency-safe way.

  > #### Note {: .info}
  >
  > If a scratchpad is active, the term is written to the local ETS table.
  > Otherwise, it writes globally.

  ## Example:

      iex> id = memoize(t)
      iex> %{t | id: id} == get_term(id)
      true
  """
  @spec memoize(Term.t()) :: Term.term_id()
  def memoize(%Term{} = draft_term) do
    signature = get_signature(draft_term)

    case :ets.lookup(@table, signature) do
      [{^signature, existing_id}] ->
        existing_id

      [] ->
        if local_table = Process.get(:term_scratchpad) do
          memoize_local(draft_term, signature, local_table)
        else
          generate_concurrent_id(draft_term)
        end
    end
  end

  defp memoize_local(%Term{} = draft_term, signature, local_table) do
    case :ets.lookup(local_table, signature) do
      [{^signature, existing_id}] ->
        existing_id

      [] ->
        new_id = :ets.update_counter(local_table, :id_counter, {2, -1})
        term = %Term{draft_term | id: new_id}
        :ets.insert(local_table, {new_id, term})
        :ets.insert(local_table, {signature, new_id})
        new_id
    end
  end

  defp generate_concurrent_id(%Term{} = draft_term) do
    signature = get_signature(draft_term)
    new_id = :ets.update_counter(@table, :id_counter, {2, 1})

    term = %Term{draft_term | id: new_id}

    :ets.insert(@table, {new_id, term})

    link_signature_or_rollback(signature, new_id, draft_term)
  end

  defp link_signature_or_rollback(signature, new_id, draft_term) do
    if :ets.insert_new(@table, {signature, new_id}) do
      new_id
    else
      case :ets.lookup(@table, signature) do
        [{^signature, winning_id}] ->
          winning_id

        [] ->
          link_signature_or_rollback(signature, new_id, draft_term)
      end
    end
  end

  defp get_signature(%Term{bvars: b, head: h, args: a, type: t, fvars: f, max_num: m}) do
    {b, h, a, t, f, m}
  end

  @doc group: :"Term Cache"
  @doc """
  Looks up and returns the concrete `ShotDs.Data.Term` struct for the given ID.
  Terms are ensured to exist in the module's ETS cache if they are solely
  generated via the provided API in this module.

  Routes to global or local ETS table based on the sign of the ID.
  """
  @spec get_term(Term.term_id()) :: Term.t()
  def get_term(id) when id > 0 do
    [{^id, term}] = :ets.lookup(@table, id)
    term
  end

  def get_term(id) when id < 0 do
    local_table = Process.get(:term_scratchpad) || raise "Scratchpad missing for local ID #{id}!"
    [{^id, term}] = :ets.lookup(local_table, id)
    term
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

    if Enum.empty?(type.args) do
      max_num =
        case decl do
          %Declaration{kind: :bv, name: n} -> n
          _ -> 0
        end

      memoize(%Term{id: @dummy_id, head: decl, type: type, fvars: fvars, max_num: max_num})
    else
      with_scratchpad(fn ->
        make_eta_expanded(decl, fvars)
      end)
    end
  end

  defp make_eta_expanded(%Declaration{type: type} = decl, fvars) do
    new_vars = Enum.map(type.args, &Declaration.fresh_var/1)
    new_arg_ids = Enum.map(new_vars, &make_term/1)

    max_num =
      case decl do
        %Declaration{kind: :bv, name: n} -> n
        _ -> 0
      end

    base_term = %Term{
      id: @dummy_id,
      head: decl,
      args: new_arg_ids,
      type: Type.new(type.goal),
      fvars: fvars ++ new_vars,
      max_num: max_num
    }

    base_term_id = memoize(base_term)

    List.foldr(new_vars, base_term_id, &make_abstr_term(&2, &1))
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

  > #### Note {: .info}
  >
  > Consider wrapping functions using this to create temporary free variables
  > with `with_scratchpad/1` for garbage collection.
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

  @doc group: :"Term Construction API"
  @doc """
  Abstracts the term corresponding to the given id over the given variable. If
  the variable is already bound, adds it to the list of bound variables.

  > #### Note {: .info}
  >
  > Consider using `ShotDs.Hol.Dsl.lambda/2` instead as it is more expressive
  > and robust.
  """
  @spec make_abstr_term(Term.term_id(), Declaration.t()) :: Term.term_id()
  def make_abstr_term(term_id, %Declaration{kind: var_kind, name: var_name, type: var_type} = var) do
    %Term{bvars: bvars, type: term_type, fvars: fvars, max_num: max_num} =
      draft_term = get_term(term_id)

    case var_kind do
      :fv ->
        bv = Declaration.new_bound_var(length(bvars) + 1, var_type)
        substituted = if var in fvars, do: bind_var(var, term_id), else: term_id
        make_abstr_term(substituted, bv)

      :bv ->
        new_type = Type.new(term_type, var_type)
        new_max = max(var_name, max_num)

        %Term{draft_term | bvars: [var | bvars], type: new_type, max_num: new_max}
        |> memoize()
    end
  end

  @doc group: :"Term Construction API"
  @doc """
  Applies the term corresponding to `left_id` to the term corresponding to
  `right_id`.

  > #### Note {: .info}
  >
  > Consider using `ShotDs.Hol.Dsl.app/2` instead as it is more expressive and
  > robust.
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

  @doc group: :"Term Construction API"
  @doc """
  Applies the term corresponding to `head_id` to the list of terms
  corresponding to `arg_ids`, folding left to right.
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

      new_head =
        case head do
          ^fvar ->
            Declaration.new_bound_var(depth + 1, fvar.type)

          %Declaration{kind: :bv, name: n} when n > depth ->
            Declaration.new_bound_var(n + 1, head.type)

          _ ->
            head
        end

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

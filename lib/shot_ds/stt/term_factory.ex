defmodule ShotDs.Stt.TermFactory do
  @moduledoc groups: [:"Term Cache", :"Term Scratchpad", :"Term Construction API"]
  @moduledoc """
  Contains functionality of creating, memoizing and accessing terms using an
  ETS cache.

  In HOL, terms often share sub-expressions, meaning they form Directed Acyclic
  Graphs (DAGs) rather than simple abstract syntax trees (ASTs). Hence,
  representing terms as nested sturctures has the big disadvantage of needing
  to store the same sub-expression multiple times in memory. ETS, the Erlang
  term storage offers an efficient caching mechanism which we can utilize to
  ensure that a specific term is created exactly once. Furthermore, Elixir's
  immutability ensures pointers to the terms being static, i.e., a term can not
  be altered once it is memoized.

  > #### Error Handling {: .info}
  >
  > All functions that can fail return a tuple `{:ok, result}` or
  > `{:error, reason}` per default to facilitate error handling. These functions
  > also come in a "bang" variant (with an "!") that raises errors instead of
  > propagating that. This behavior can be useful for quick prototyping or when
  > it is guaranteed that the function calls will succeed.

  > #### Note {: .neutral}
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

  @signature ~w(⊤ ⊥ ¬ ∨ ∧ ⊃ ≡ = ∀ ∃)

  @typedoc """
  There are two error scenarios when looking up a term via its ID. The ID might
  not correspond to `ShotDs.Data.Term.global_term_id()` or
  `ShotDs.Data.Term.local_term_id()`. If it does, it may not be pointing to any
  term. Lastly, the ID can be a _local_ ID, i.e., points to a sketchpad, but no
  sketchpad may be active for the current process.
  """
  @type lookup_error_t ::
          {:error, :invalid_id} | {:error, :non_existing_id} | {:error, :scratchpad_missing}

  @doc group: :"Term Scratchpad"
  @doc """
  Creates a local "scratchpad" ETS table for the current process. Can be used to
  cleanup temporary free variable terms e.g., when creating abstraction terms.

  Puts the reference to the ETS table in the processes memory under the
  `:term_scratchpad` key.
  """
  @spec start_scratchpad() :: :ok
  def start_scratchpad do
    table = :ets.new(:scratchpad, [:set, :private])
    :ets.insert(table, {:id_counter, 0})
    Process.put(:term_scratchpad, table)
    :ok
  end

  @doc group: :"Term Scratchpad"
  @doc """
  Destroys the processes ephemeral ETS table explicitly.

  > #### Note {: .info}
  >
  > The scratchpad ETS table also dies with the process automatically.
  """
  @spec stop_scratchpad() :: :ok
  def stop_scratchpad do
    if table = Process.get(:term_scratchpad) do
      :ets.delete(table)
      Process.delete(:term_scratchpad)
    end

    :ok
  end

  @doc group: :"Term Scratchpad"
  @doc """
  Commits the term with the given ID (which might be local) to the global ETS
  table. Returns a tuple `{:ok, new_global_id}` or `{:error, reason}`.

  Also ensures recursively that the arguments are memoized.
  """
  @spec commit_to_global(Term.local_term_id() | Term.global_term_id()) ::
          {:ok, Term.global_term_id()} | {:error, :invalid_id}
  def commit_to_global(id) do
    case do_commit(id, %{}) do
      {:ok, {global_id, _cache}} -> {:ok, global_id}
      {:error, reason} -> {:error, reason}
    end
  end

  defp do_commit(id, _cache) when not is_integer(id) or id == 0, do: {:error, :invalid_id}
  defp do_commit(id, cache) when id > 0, do: {:ok, {id, cache}}

  defp do_commit(id, cache) when id < 0 and is_map_key(cache, id),
    do: {:ok, {Map.get(cache, id), cache}}

  defp do_commit(id, cache) when id < 0 do
    with {:ok, %Term{} = term} <- get_term(id),
         {:ok, committed_args, updated_cache} <- commit_args(term.args, cache) do
      draft_term = %Term{term | args: committed_args}
      signature = get_signature(draft_term)

      final_id =
        case :ets.lookup(@table, signature) do
          [{^signature, existing_id}] -> existing_id
          [] -> generate_concurrent_id(draft_term)
        end

      {:ok, {final_id, Map.put(updated_cache, id, final_id)}}
    end
  end

  defp commit_args(args, cache) do
    result =
      Enum.reduce_while(args, {:ok, [], cache}, fn arg_id, {:ok, acc_args, current_cache} ->
        case do_commit(arg_id, current_cache) do
          {:ok, {global_id, next_cache}} ->
            {:cont, {:ok, [global_id | acc_args], next_cache}}

          {:error, _} = err ->
            {:halt, err}
        end
      end)

    case result do
      {:ok, reversed_args, final_cache} -> {:ok, Enum.reverse(reversed_args), final_cache}
      error -> error
    end
  end

  @doc group: :"Term Scratchpad"
  @doc """
  Commits the term with the given ID (which might be local) to the global ETS
  table. Returns the new global ID, raising on errors.

  Also ensures recursively that the arguments are memoized.
  """
  @spec commit_to_global!(Term.local_term_id() | Term.global_term_id()) :: Term.global_term_id()
  def commit_to_global!(id) do
    case commit_to_global(id) do
      {:ok, global_id} ->
        global_id

      {:error, :invalid_id} ->
        raise ArgumentError, message: "Invalid ID: Expected positive or negative integer."
    end
  end

  @doc group: :"Term Scratchpad"
  @doc """
  Wraps the given function and executes it with an active scratchpad.

  Commits the final result to the global ETS table Cleans up the scratchpad
  afterwards if it didn't exist previously. Acts as a concurrency-safe garbage
  collector.
  """
  @spec with_scratchpad((-> {:ok, Term.term_id()} | {:error, t})) ::
          {:ok, Term.term_id()} | {:error, t}
        when t: term()
  def with_scratchpad(fun) do
    my_responsibility? = is_nil(Process.get(:term_scratchpad))

    if my_responsibility? do
      start_scratchpad()
    end

    try do
      with {:ok, result_id} <- fun.() do
        if my_responsibility? do
          commit_to_global(result_id)
        else
          {:ok, result_id}
        end
      end
    after
      if my_responsibility? do
        stop_scratchpad()
      end
    end
  end

  @doc group: :"Term Scratchpad"
  @doc """
  Wraps the given function and executes it with an active scratchpad,
  propagating errors when they occur.

  Commits the final result to the global ETS table Cleans up the scratchpad
  afterwards if it didn't exist previously. Acts as a concurrency-safe garbage
  collector.
  """
  @spec with_scratchpad!((-> Term.term_id())) :: Term.term_id()
  def with_scratchpad!(fun) do
    my_responsibility? = is_nil(Process.get(:term_scratchpad))

    if my_responsibility? do
      start_scratchpad()
    end

    try do
      result_id = fun.()

      if my_responsibility? do
        commit_to_global!(result_id)
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

  Returns the looked up or generated ID of the term. IDs are generated as
  integers in a concurrency-safe way. Local IDs are represented by negative,
  global ones by positive integers.

  > #### Note {: .info}
  >
  > If a scratchpad is active, the term is written to the local ETS table.
  > Otherwise, it writes globally.

  ## Example:

      iex> id = memoize(t)
      iex> match?({:ok, %{^t | id: ^id}}, get_term(id))
      true
  """
  @spec memoize(Term.t()) :: Term.global_term_id() | Term.local_term_id()
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
        new_id = -:erlang.unique_integer([:positive])
        term = %Term{draft_term | id: new_id}
        :ets.insert(local_table, {new_id, term})
        :ets.insert(local_table, {signature, new_id})
        new_id
    end
  end

  defp generate_concurrent_id(%Term{} = draft_term) do
    signature = get_signature(draft_term)
    new_id = :erlang.unique_integer([:positive])

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
          :ets.delete(@table, new_id)
          winning_id

        [] ->
          link_signature_or_rollback(signature, new_id, draft_term)
      end
    end
  end

  defp get_signature(%Term{
         bvars: b,
         head: h,
         args: a,
         type: t,
         fvars: f,
         consts: c,
         tvars: tv,
         max_num: m
       }) do
    {b, h, a, t, f, c, tv, m}
  end

  @doc group: :"Term Cache"
  @doc """
  Looks up and returns the concrete `ShotDs.Data.Term` struct for the given ID.

  Routes to global or local ETS table based on the sign of the ID.
  """
  @spec get_term(Term.term_id()) :: {:ok, Term.t()} | lookup_error_t()
  def get_term(id)

  def get_term(id) when not is_integer(id) or id == 0, do: {:error, :invalid_id}

  def get_term(id) when id > 0 do
    case :ets.lookup(@table, id) do
      [{^id, term}] -> {:ok, term}
      [] -> {:error, :non_existing_id}
    end
  end

  def get_term(id) when id < 0 do
    case Process.get(:term_scratchpad) do
      nil ->
        {:error, :scratchpad_missing}

      local_table ->
        case :ets.lookup(local_table, id) do
          [{^id, term}] -> {:ok, term}
          [] -> {:error, :non_existing_id}
        end
    end
  end

  @doc group: :"Term Cache"
  @doc """
  Looks up and returns the concrete `ShotDs.Data.Term` struct for the given ID,
  erroring out if the ID doesn't exist.

  Routes to global or local ETS table based on the sign of the ID.
  """
  @spec get_term!(Term.term_id()) :: Term.t()
  def get_term!(id)

  def get_term!(id) when not is_integer(id) or id == 0 do
    raise ArgumentError,
      message: "Invalid ID: Expected positive or negative integer, got: #{inspect(id)}"
  end

  def get_term!(id) when id > 0 do
    case :ets.lookup(@table, id) do
      [{^id, term}] -> term
      [] -> raise ArgumentError, "Given ID does not correspond to a memoized term."
    end
  end

  def get_term!(id) when id < 0 do
    case Process.get(:term_scratchpad) do
      nil ->
        raise ArgumentError,
          message: "Got a local ID but no scratchpad is active in the current process."

      local_table ->
        case :ets.lookup(local_table, id) do
          [{^id, term}] -> term
          [] -> raise ArgumentError, "Given ID does not correspond to a memoized term."
        end
    end
  end

  ##############################################################################
  # TERM CONSTRUCTION API
  ##############################################################################

  @doc group: :"Term Construction API"
  @doc """
  Creates and memoizes a term representing a single free variable, bound
  variable or constant. Handles eta-expansion automatically.

  Returns a local ID if a scratchpad is active in the caller's process.

  ## Example:

      iex> co = ShotDs.Data.Declaration.fresh_const(Type.new(:o))
      iex> id = make_term(co)
  """
  @dialyzer {:no_opaque, [make_term: 1, make_eta_expanded: 4]}

  @spec make_term(Declaration.t()) :: Term.term_id()
  def make_term(%Declaration{kind: kind, name: name, type: type} = decl) do
    fvars = if kind == :fv, do: MapSet.new([decl]), else: MapSet.new()
    consts = if kind == :co and name not in @signature, do: MapSet.new([decl]), else: MapSet.new()
    tvars = Type.free_type_vars(type)

    if Enum.empty?(type.args) do
      max_num =
        case decl do
          %Declaration{kind: :bv, name: n} -> n
          _ -> 0
        end

      memoize(%Term{
        id: @dummy_id,
        head: decl,
        type: type,
        fvars: fvars,
        consts: consts,
        tvars: tvars,
        max_num: max_num
      })
    else
      make_eta_expanded(decl, fvars, consts, tvars)
    end
  end

  defp make_eta_expanded(%Declaration{type: type} = decl, fvars, consts, tvars) do
    with_scratchpad!(fn ->
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
        fvars: Enum.reduce(new_vars, fvars, &MapSet.put(&2, &1)),
        consts: consts,
        tvars: tvars,
        max_num: max_num
      }

      base_term_id = memoize(base_term)

      List.foldr(new_vars, base_term_id, &make_abstr_term!(&2, &1))
    end)
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
  > with `with_scratchpad/1` or `with_scratchpad!/1` for garbage collection.
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

  @doc group: :"Term Construction API"
  @doc """
  Checks whether the term corresponding to the given ID is a _primitive term_
  i.e., if it is an eta-expanded constant or variable.
  """
  @spec primitive_term?(Term.term_id()) :: {:ok, boolean()} | lookup_error_t()
  def primitive_term?(term_id) do
    with {:ok, term} <- get_term(term_id) do
      %Term{bvars: bvars, args: args} = term

      primitive? =
        length(bvars) == length(args) &&
          Enum.zip(bvars, args)
          |> Enum.all?(fn {bv, arg} -> make_term(bv) === arg end)

      {:ok, primitive?}
    end
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
  @spec make_abstr_term(Term.term_id(), Declaration.t() | Term.term_id()) ::
          {:ok, Term.term_id()} | lookup_error_t() | {:error, :var_term_not_primitive}
  def make_abstr_term(term_id, var)

  def make_abstr_term(term_id, %Declaration{kind: :fv, type: var_type} = var) do
    with {:ok, %Term{} = draft_term} <- get_term(term_id) do
      %Term{bvars: bvars} = draft_term
      bv = Declaration.new_bound_var(length(bvars) + 1, var_type)
      bind_var(var, term_id) |> make_abstr_term(bv)
    end
  end

  def make_abstr_term(term_id, %Declaration{kind: :bv, name: var_name, type: var_type} = var) do
    with {:ok, %Term{} = draft_term} <- get_term(term_id) do
      %Term{bvars: bvars, type: term_type, max_num: max_num, tvars: tvars} = draft_term
      new_type = Type.new(term_type, var_type)
      new_max = max(var_name, max_num)
      bvar_tvars = Type.free_type_vars(var_type)
      new_tvars = MapSet.union(tvars, bvar_tvars)

      new_term = %Term{
        draft_term
        | bvars: [var | bvars],
          type: new_type,
          tvars: new_tvars,
          max_num: new_max
      }

      {:ok, memoize(new_term)}
    end
  end

  def make_abstr_term(term_id, var_term_id) do
    with {:ok, %Term{head: var}} <- get_term(var_term_id),
         {:ok, primitive?} <- primitive_term?(var_term_id) do
      if not primitive? or var.kind == :co do
        {:error, :var_term_not_primitive}
      else
        make_abstr_term(term_id, var)
      end
    end
  end

  @doc group: :"Term Construction API"
  @doc """
  Abstracts the term corresponding to the given id over the given variable (or
  variable term), erroring out if either term does not exist or the given
  variable term is not primitive. If the variable is already bound, adds it to
  the list of bound variables.

  > #### Note {: .info}
  >
  > Consider using `ShotDs.Hol.Dsl.lambda/2` instead as it is more expressive
  > and robust.
  """
  @spec make_abstr_term!(Term.term_id(), Declaration.t() | Term.term_id()) :: Term.term_id()
  def make_abstr_term!(term_id, var)

  def make_abstr_term!(term_id, var) do
    case make_abstr_term(term_id, var) do
      {:ok, res_term} ->
        res_term

      {:error, :invalid_id} ->
        raise ArgumentError,
          message: "Given ID is not valid. Expected positive or negative integer."

      {:error, :non_existing_id} ->
        raise ArgumentError, message: "Given ID does not correspond to a memoized term."

      {:error, :scratchpad_missing} ->
        raise ArgumentError,
          message: "Got a local ID but no scratchpad is active in the current process."

      {:error, :var_term_not_primitive} ->
        raise(ArgumentError, message: "Second argument is not a primitive variable term.")
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
  @spec make_appl_term(Term.term_id(), Term.term_id()) ::
          {:ok, Term.term_id()} | lookup_error_t() | {:error, :incompatible_types}
  def make_appl_term(left_id, right_id) do
    with {:ok, %Term{bvars: [_b | bs]} = left_term} <- get_term(left_id),
         {:ok, %Term{} = right_term} <- get_term(right_id),
         %Type{goal: goal_type, args: [arg1 | rest_types]} <- left_term.type,
         ^arg1 <- right_term.type do
      new_type = Type.new(goal_type, rest_types)
      new_max_num = calc_new_max_num(left_term.head, left_term.args, bs)
      new_tvars = calc_new_tvars(left_term.head, left_term.args, bs)

      body_term = %Term{
        left_term
        | bvars: bs,
          type: new_type,
          tvars: new_tvars,
          max_num: new_max_num
      }

      body_id = memoize(body_term)

      case instantiate(body_id, 1, right_id) do
        {:ok, {reduced_id, _cache}} -> {:ok, reduced_id}
        {:error, reason} -> {:error, reason}
      end
    else
      {:error, :non_existing_id} -> {:error, :non_existing_id}
      {:error, :scratchpad_missing} -> {:error, :scratchpad_missing}
      _exception -> {:error, :incompatible_types}
    end
  end

  @doc group: :"Term Construction API"
  @doc """
  Applies the term corresponding to `left_id` to the term corresponding to
  `right_id`, erroring out if either term does not exist or their types are
  incompatible.

  > #### Note {: .info}
  >
  > Consider using `ShotDs.Hol.Dsl.app/2` instead as it is more expressive and
  > robust.
  """
  @spec make_appl_term!(Term.term_id(), Term.term_id()) :: Term.term_id()
  def make_appl_term!(left_id, right_id) do
    case make_appl_term(left_id, right_id) do
      {:ok, res_term} ->
        res_term

      {:error, :non_existing_id} ->
        raise ArgumentError,
          message: "One of the given IDs does not correspond to a memoized term."

      {:error, :scratchpad_missing} ->
        raise ArgumentError,
          message: "Got a local ID but no scratchpad is active in the current process."

      {:error, :incompatible_types} ->
        raise ArgumentError, message: "The terms have incompatible types."
    end
  end

  @doc group: :"Term Construction API"
  @doc """
  Applies the term corresponding to `head_id` to the list of terms corresponding
  to `arg_ids`.
  """
  @spec fold_apply(Term.term_id(), [Term.term_id()]) :: {:ok, Term.term_id()} | lookup_error_t()
  def fold_apply(head_id, arg_ids) do
    Enum.reduce(arg_ids, {:ok, head_id}, fn arg_id, acc ->
      with {:ok, acc_id} <- acc,
           do: make_appl_term(acc_id, arg_id)
    end)
  end

  @doc group: :"Term Construction API"
  @doc """
  Applies the term corresponding to `head_id` to the list of terms corresponding
  to `arg_ids`, folding left to right, erroring out if one of the terms does not
  exist.
  """
  @spec fold_apply!(Term.term_id(), [Term.term_id()]) :: Term.term_id()
  def fold_apply!(head_id, arg_ids) do
    Enum.reduce(arg_ids, head_id, &make_appl_term!(&2, &1))
  end

  # Binds all occurrences of fvar in the term with id term_id
  @spec bind_var(Declaration.free_var_t(), Term.term_id()) :: Term.term_id()
  defp bind_var(%Declaration{kind: :fv} = fvar, term_id) do
    update_env = fn term, depth -> depth + length(term.bvars) end
    short_circuit = fn term, _depth -> not MapSet.member?(term.fvars, fvar) end

    transform = fn %Term{head: head, fvars: fvars} = term, new_args, depth, acc_cache ->
      new_fvars = MapSet.delete(fvars, fvar)

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
      new_tvars = calc_new_tvars(new_head, new_args, term.bvars)

      new_term = %Term{
        term
        | head: new_head,
          args: new_args,
          fvars: new_fvars,
          tvars: new_tvars,
          max_num: new_max_num
      }

      {memoize(new_term), acc_cache}
    end

    {new_id, _cache} = map_term!(term_id, 0, update_env, transform, short_circuit)
    new_id
  end

  defp calc_new_max_num(head_decl, arg_ids, bvars) do
    head_max =
      case head_decl do
        %Declaration{kind: :bv, name: n} -> n
        _ -> 0
      end

    arg_maxes = Enum.map(arg_ids, fn id -> get_term!(id).max_num end)
    bvar_maxes = Enum.map(bvars, & &1.name)
    Enum.max([head_max | arg_maxes ++ bvar_maxes], fn -> 0 end)
  end

  defp calc_new_tvars(head_decl, arg_ids, bvars) do
    after_bvars =
      Enum.reduce(bvars, Type.free_type_vars(head_decl.type), fn bv, acc ->
        MapSet.union(acc, Type.free_type_vars(bv.type))
      end)

    Enum.reduce(arg_ids, after_bvars, fn id, acc ->
      MapSet.union(acc, get_term!(id).tvars)
    end)
  end
end

defmodule ShotDs.TermFactory do
  @moduledoc groups: [:"Term Cache", :"Term Construction API"]
  @moduledoc """
  Contains functionality of creating, memoizing and accessing terms using an
  ETS cache. `ShotDs.TermFactory.init` must be called exactly once before the
  API can be used.

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
  import ShotDs.Semantics, only: [make_abstr_term: 2]

  @table :term_pool

  @doc group: :"Term Cache"
  @doc """
  Initializes a concurrent ETS table to store terms for efficient lookups.

  #### Note {: .warning}

  This function can only be called once! An `ArgumentError` will be raised if
  it is called again on the same BEAM VM.
  """
  @spec init() :: :ok
  def init do
    :ets.new(@table, [
      :set,
      :public,
      :named_table,
      read_concurrency: true,
      write_concurrency: true
    ])

    :ok
  end

  @doc group: :"Term Cache"
  @doc """
  Memoizes the given term in the module's `:ets` table. Terms will be
  identified if they share the same *signature*, e.g., all fields but `id`.

  Returns the looked up or generated ID of the term. ID's are generated as
  blake2s hashes (https://www.blake2.net/) ensuring collisions to be highly
  unlikely and deterministic ID generation for concurrent processing.

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
        id = :crypto.hash(:blake2s, :erlang.term_to_binary(signature))

        term = %Term{draft_term | id: id}

        :ets.insert(@table, {signature, id})
        :ets.insert(@table, {id, term})

        id
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
  variable or constant. Handles η-expansion automatically.

  ## Example:

      iex> co = ShotDs.Data.Declaration.fresh_const(Type.new(:o))
      iex> id = make_term(co)
  """
  @spec make_term(Declaration.t()) :: Term.term_id()
  def make_term(%Declaration{kind: kind, type: type} = decl) do
    fvars = if kind == :fv, do: [decl], else: []

    case type do
      %Type{args: []} ->
        %Term{id: Term.dummy_id(), head: decl, type: type, fvars: fvars}
        |> memoize()

      %Type{goal: goal_type, args: arg_types} ->
        new_vars = Enum.map(arg_types, &Declaration.fresh_var/1)
        new_arg_ids = Enum.map(new_vars, &make_term/1)

        max_num =
          new_arg_ids
          |> Enum.map(fn id -> get_term(id).max_num end)
          |> Enum.max(fn -> 0 end)

        base_term = %Term{
          id: Term.dummy_id(),
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
end

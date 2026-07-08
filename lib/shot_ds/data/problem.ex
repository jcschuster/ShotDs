defmodule ShotDs.Data.Problem do
  @moduledoc """
  A data structure to describe a (TPTP) proof problem.

  It contains meta-information about the problem (path to proof file, included
  files) as well as the problem definition which consist of:

  - A map of types which maps symbols (user types or constants) to their type

  - The definitions given by the user

  - The axioms defined by the user

  - The conjecture to be proven based on the axioms and definitions

  Note that definitions are not unfolded in the proof problem but kept as
  constants.
  """
  alias ShotDs.Data.{Type, TypeScheme, Declaration, Substitution, Term}
  alias ShotDs.Stt.Semantics
  alias ShotDs.Stt.TermFactory, as: TF

  defstruct path: "", includes: [], types: %{}, definitions: %{}, axioms: [], conjecture: nil

  @typedoc """
  A `Problem` is a collection holding the relevant information and
  meta-information of a problem stored in separate fields.

  The `:path` to a problem file is given as a string. This also includes the
  paths to the included files in `:includes`.

  The types are given as a map mapping symbol names (or type names) to their
  defined types (can be `:base_type` for user-defined base types).

  The definitions are given as a map from the symbol's name to the equation
  describing it. Note that the equation must first be deconstructed into the
  defined constant on the left hand side and it's definition on the right hand
  side.

  The axioms are stored as a list of pairs containing the axiom's name as
  string and term as its corresponding ID.

  The conjecture is tuple containing the conjecture's name as string and the
  conjecture itself as the term's ID. The field's value is `nil` if no
  conjecture could be found.
  """
  @type t() :: %__MODULE__{
          path: String.t(),
          includes: [String.t()],
          types: %{String.t() => :base_type | Type.t() | TypeScheme.t()},
          definitions: %{Declaration.t() => Term.term_id()},
          axioms: [{String.t(), Term.term_id()}],
          conjecture: {String.t(), Term.term_id()} | nil
        }

  @typedoc """
  A single axiom entry accepted by `new/1`. Either a `{name, term_id}` pair or
  a bare `term_id` (in which case a name of the form `"axiom_<n>"` is generated
  based on position).
  """
  @type axiom_input() :: {String.t(), Term.term_id()} | Term.term_id()

  @typedoc """
  A conjecture entry accepted by `new/1`. `nil` if no conjecture is given.
  A bare `term_id` gets the default name `"conjecture"`.
  """
  @type conjecture_input() :: {String.t(), Term.term_id()} | Term.term_id() | nil

  @typedoc """
  Options accepted by `new/1` and `new!/1`.
  """
  @type new_opts() :: [
          axioms: [axiom_input()],
          conjecture: conjecture_input(),
          path: String.t()
        ]

  @doc ~S"""
  Builds a `Problem` struct from a list of axioms and an optional conjecture.

  Axioms may be given as `{name, term_id}` pairs or as bare `term_id`s — bare
  entries are auto-named `"axiom_<n>"` based on their position (1-indexed),
  which is useful when the caller comes from an intermediate proof state where
  the original names have been discarded. The conjecture may be given as
  `{name, term_id}`, as a bare `term_id` (named `"conjecture"`), or as `nil`.

  The `types` map is populated automatically by scanning all referenced terms:

  - Each **constant** occurring in an axiom or conjecture is registered under
    its name with a `ShotDs.Data.TypeScheme`. When the same constant is used at
    multiple types (rank-1 polymorphism), the monotypes are reconciled by
    least-general-generalization and the free type variables are quantified in
    the resulting scheme.
  - Each **user-defined base type atom** (any goal other than `:o`, `:i`, or
    `:tType`) is registered as `:base_type`.

  Free variables that occur in **only one** formula retain their embedded
  types; when the problem is exported to TPTP, they are implicitly universally
  quantified in that formula (per the standard THF convention).

  Free variables that occur in **more than one** formula (axioms and/or
  conjecture) are automatically replaced everywhere by a fresh constant of the
  same type so their sharing across formulas is preserved when the problem is
  exported and re-parsed. The generated constant is named
  `"fv_" <> lowercased(fvar_name)` — the `fv_` prefix makes it visually
  distinct from ordinary user constants — with a numeric suffix appended if
  that name clashes with an existing constant.

  ## Options

  - `:axioms` — list of `axiom_input()` entries (default `[]`)
  - `:conjecture` — `conjecture_input()` (default `nil`)
  - `:path` — display path for the constructed problem (default `"memory"`)

  Returns `{:ok, problem}` or `{:error, reason}`.

  ## Examples

      iex> import ShotDs.Hol.Definitions
      iex> alias ShotDs.Stt.TermFactory, as: TF
      iex> a_id = TF.make_const_term("a", type_i())
      iex> p_id = TF.make_const_term("p", Type.new(:o, :i))
      iex> ax = ShotDs.Hol.Dsl.app(p_id, a_id)
      iex> {:ok, %ShotDs.Data.Problem{types: types}} =
      ...>   ShotDs.Data.Problem.new(axioms: [{"ax1", ax}])
      iex> Map.keys(types) |> Enum.sort()
      ["a", "p"]

      iex> import ShotDs.Hol.Definitions
      iex> alias ShotDs.Stt.TermFactory, as: TF
      iex> a_id = TF.make_const_term("a", type_i())
      iex> p_id = TF.make_const_term("p", Type.new(:o, :i))
      iex> ax = ShotDs.Hol.Dsl.app(p_id, a_id)
      iex> {:ok, problem} = ShotDs.Data.Problem.new(axioms: [ax], conjecture: ax)
      iex> Enum.map(problem.axioms, &elem(&1, 0))
      ["axiom_1"]
      iex> elem(problem.conjecture, 0)
      "conjecture"
  """
  @spec new(new_opts()) :: {:ok, t()} | {:error, String.t()}
  def new(opts \\ []) do
    raw_axioms = Keyword.get(opts, :axioms, [])
    raw_conj = Keyword.get(opts, :conjecture, nil)
    path = Keyword.get(opts, :path, "memory")

    with {:ok, axioms} <- normalize_axioms(raw_axioms),
         {:ok, conjecture} <- normalize_conjecture(raw_conj),
         {:ok, terms} <- fetch_terms(axioms, conjecture),
         {:ok, {axioms2, conjecture2, terms2}} <-
           skolemize_shared_fvars(axioms, conjecture, terms),
         {:ok, types} <- build_types_map(terms2) do
      {:ok,
       %__MODULE__{
         path: path,
         axioms: axioms2,
         conjecture: conjecture2,
         types: types
       }}
    end
  end

  @doc """
  Same as `new/1` but raises `ArgumentError` on failure.
  """
  @spec new!(new_opts()) :: t()
  def new!(opts \\ []) do
    case new(opts) do
      {:ok, problem} -> problem
      {:error, reason} -> raise ArgumentError, message: reason
    end
  end

  # --- Normalization / validation ---

  defp normalize_axioms(axioms) when is_list(axioms) do
    axioms
    |> Enum.with_index(1)
    |> Enum.reduce_while({:ok, []}, fn {entry, idx}, {:ok, acc} ->
      case normalize_axiom(entry, idx) do
        {:ok, pair} -> {:cont, {:ok, [pair | acc]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
    |> case do
      {:ok, rev} -> {:ok, Enum.reverse(rev)}
      err -> err
    end
  end

  defp normalize_axioms(other),
    do: {:error, "Invalid :axioms option, expected a list, got: #{inspect(other)}"}

  defp normalize_axiom({name, id}, _idx) when is_binary(name) and is_integer(id) and id > 0,
    do: {:ok, {name, id}}

  defp normalize_axiom(id, idx) when is_integer(id) and id > 0,
    do: {:ok, {"axiom_#{idx}", id}}

  defp normalize_axiom(other, _idx),
    do:
      {:error,
       "Invalid axiom entry #{inspect(other)}: expected term_id or {name, term_id} with pos_integer id"}

  defp normalize_conjecture(nil), do: {:ok, nil}

  defp normalize_conjecture({name, id}) when is_binary(name) and is_integer(id) and id > 0,
    do: {:ok, {name, id}}

  defp normalize_conjecture(id) when is_integer(id) and id > 0,
    do: {:ok, {"conjecture", id}}

  defp normalize_conjecture(other),
    do:
      {:error,
       "Invalid :conjecture option, expected nil, term_id, or {name, term_id}, got: #{inspect(other)}"}

  # --- Term fetching ---

  defp fetch_terms(axioms, conjecture) do
    ids =
      Enum.map(axioms, fn {_, id} -> id end) ++
        case conjecture do
          nil -> []
          {_, id} -> [id]
        end

    Enum.reduce_while(ids, {:ok, []}, fn id, {:ok, acc} ->
      case TF.get_term(id) do
        {:ok, term} -> {:cont, {:ok, [term | acc]}}
        {:error, reason} -> {:halt, {:error, "Term id #{id} lookup failed: #{inspect(reason)}"}}
      end
    end)
  end

  # --- Shared-free-variable Skolemization ---

  # Replaces every free variable that occurs in more than one of the given
  # formulas with a fresh `fv_...` constant of the same type, applying the
  # resulting substitution to each axiom and the conjecture. Free variables
  # confined to a single formula are left untouched (they are implicitly ∀-
  # quantified at unparse time by the TPTP emitter).
  defp skolemize_shared_fvars(axioms, conjecture, terms) do
    case shared_fvars(terms) do
      [] ->
        {:ok, {axioms, conjecture, terms}}

      shared ->
        substs = build_promotion_substs(shared, existing_const_names(terms))

        with {:ok, new_axioms} <- apply_substs_to_axioms(axioms, substs),
             {:ok, new_conjecture} <- apply_substs_to_conjecture(conjecture, substs),
             {:ok, new_terms} <- fetch_terms(new_axioms, new_conjecture) do
          {:ok, {new_axioms, new_conjecture, new_terms}}
        end
    end
  end

  defp shared_fvars(terms) do
    terms
    |> Enum.flat_map(fn %Term{fvars: fvs} -> MapSet.to_list(fvs) end)
    |> Enum.frequencies()
    |> Enum.filter(fn {_fv, count} -> count > 1 end)
    |> Enum.map(&elem(&1, 0))
  end

  # Uses `name_key/1` so ref-named constants (which are unprintable as strings)
  # are compared against the same normalized identifier they end up under in
  # the final `types` map.
  defp existing_const_names(terms) do
    terms
    |> Enum.flat_map(fn %Term{consts: cs} -> MapSet.to_list(cs) end)
    |> MapSet.new(fn %Declaration{name: n} -> name_key(n) end)
  end

  defp build_promotion_substs(fvars, existing_names) do
    {rev_substs, _taken} =
      Enum.reduce(fvars, {[], existing_names}, fn fv, {acc, taken} ->
        name = fresh_promoted_name(fv, taken)
        const_id = TF.make_const_term(name, fv.type)
        subst = Substitution.new(fv, const_id)
        {[subst | acc], MapSet.put(taken, name)}
      end)

    Enum.reverse(rev_substs)
  end

  defp fresh_promoted_name(fv, taken) do
    base = base_promoted_name(fv)

    if MapSet.member?(taken, base) do
      Stream.iterate(1, &(&1 + 1))
      |> Stream.map(&"#{base}_#{&1}")
      |> Enum.find(&(not MapSet.member?(taken, &1)))
    else
      base
    end
  end

  defp base_promoted_name(%Declaration{kind: :fv, name: name}) when is_binary(name) do
    case name do
      <<c, rest::binary>> when c in ?A..?Z ->
        "fv_" <> String.downcase(<<c>>) <> rest

      _ ->
        "fv_" <> name
    end
  end

  defp base_promoted_name(%Declaration{kind: :fv, name: ref}) when is_reference(ref),
    do: "fv_r" <> (:erlang.phash2(ref) |> Integer.to_string(36))

  defp apply_substs_to_axioms(axioms, substs) do
    axioms
    |> Enum.reduce_while({:ok, []}, fn {name, id}, {:ok, acc} ->
      case Semantics.subst(substs, id) do
        {:ok, new_id} ->
          {:cont, {:ok, [{name, new_id} | acc]}}

        {:error, reason} ->
          {:halt, {:error, "Substitution in axiom '#{name}' failed: #{inspect(reason)}"}}
      end
    end)
    |> case do
      {:ok, rev} -> {:ok, Enum.reverse(rev)}
      err -> err
    end
  end

  defp apply_substs_to_conjecture(nil, _substs), do: {:ok, nil}

  defp apply_substs_to_conjecture({name, id}, substs) do
    case Semantics.subst(substs, id) do
      {:ok, new_id} ->
        {:ok, {name, new_id}}

      {:error, reason} ->
        {:error, "Substitution in conjecture '#{name}' failed: #{inspect(reason)}"}
    end
  end

  # --- Types map construction ---

  defp build_types_map(terms) do
    consts_by_name =
      terms
      |> Enum.flat_map(fn %Term{consts: c} -> MapSet.to_list(c) end)
      |> Enum.group_by(& &1.name, & &1.type)

    with {:ok, const_types} <- reconcile_const_types(consts_by_name) do
      base_types =
        terms
        |> Enum.flat_map(&collect_term_types/1)
        |> Enum.flat_map(&collect_concrete_atoms/1)
        |> Enum.uniq()
        |> Enum.reject(&(&1 in [:i, :o, :tType]))
        |> Map.new(fn atom -> {Atom.to_string(atom), :base_type} end)

      {:ok, Map.merge(base_types, const_types)}
    end
  end

  defp collect_term_types(%Term{fvars: fvars, consts: consts}) do
    (MapSet.to_list(fvars) ++ MapSet.to_list(consts))
    |> Enum.map(& &1.type)
  end

  defp collect_concrete_atoms(%Type{goal: g, args: args}) do
    base = if is_atom(g), do: [g], else: []
    base ++ Enum.flat_map(args, &collect_concrete_atoms/1)
  end

  defp reconcile_const_types(consts_by_name) do
    schemes =
      Map.new(consts_by_name, fn {name, [first | rest]} ->
        monotype = anti_unify_list(first, rest, %{})
        scheme = TypeScheme.generalize(monotype, MapSet.new())
        {name_key(name), scheme}
      end)

    {:ok, schemes}
  end

  defp name_key(name) when is_binary(name), do: name

  defp name_key(ref) when is_reference(ref),
    do: "c#{:erlang.phash2(ref) |> Integer.to_string(36)}"

  # Anti-unify (least general generalization) a non-empty list of monotypes into
  # a single monotype. Type variables are freshened and reused consistently for
  # every mismatched sub-position, giving the most general common instance.
  defp anti_unify_list(acc, [], _pair_map), do: acc

  defp anti_unify_list(acc, [next | rest], pair_map) do
    {result, new_map} = au(acc, next, pair_map)
    anti_unify_list(result, rest, new_map)
  end

  defp au(%Type{} = t1, %Type{} = t2, pair_map) do
    cond do
      t1 == t2 ->
        {t1, pair_map}

      Type.type_var?(t1) or Type.type_var?(t2) ->
        fresh_for_pair(t1, t2, pair_map)

      t1.goal == t2.goal and length(t1.args) == length(t2.args) ->
        {rev_args, final_map} =
          [t1.args, t2.args]
          |> Enum.zip()
          |> Enum.reduce({[], pair_map}, fn {a1, a2}, {acc, m} ->
            {r, m2} = au(a1, a2, m)
            {[r | acc], m2}
          end)

        {%Type{goal: t1.goal, args: Enum.reverse(rev_args)}, final_map}

      true ->
        fresh_for_pair(t1, t2, pair_map)
    end
  end

  defp fresh_for_pair(t1, t2, pair_map) do
    key = pair_key(t1, t2)

    case Map.get(pair_map, key) do
      nil ->
        fresh = make_ref()
        {Type.new(fresh), Map.put(pair_map, key, fresh)}

      existing ->
        {Type.new(existing), pair_map}
    end
  end

  # Order-independent key so au(t1, t2) and au(t2, t1) share the same fresh var.
  defp pair_key(t1, t2) do
    a = :erlang.phash2(t1)
    b = :erlang.phash2(t2)
    if a <= b, do: {t1, t2}, else: {t2, t1}
  end
end

defimpl String.Chars, for: ShotDs.Data.Problem do
  def to_string(%{
        path: path,
        includes: includes,
        types: types,
        definitions: defs,
        axioms: axioms,
        conjecture: conjecture
      }) do
    name_string = "Problem " <> if path in ["", "memory"], do: "<unnamed>", else: path

    includes_string =
      if Enum.empty?(includes) do
        ""
      else
        "\nincludes: " <> Enum.join(includes, ", ")
      end

    types_string =
      if Enum.empty?(types) do
        ""
      else
        "\nTypes: " <>
          Enum.map_join(types, ", ", fn
            {name, :base_type} -> "#{name} (base type)"
            {name, type} -> "#{name}::#{type}"
          end)
      end

    defs_string =
      if Enum.empty?(defs) do
        ""
      else
        "\nDepends on #{map_size(defs)} definitions: {#{Enum.map_join(defs, ", ", fn {c, _t} -> Kernel.to_string(c) end)}}"
      end

    axioms_string =
      if Enum.empty?(axioms) do
        ""
      else
        "\n#{length(axioms)} axioms: {#{Enum.map_join(axioms, ", ", fn {c, _t} -> Kernel.to_string(c) end)}}"
      end

    conjecture_string =
      case conjecture do
        nil -> "\nNo conjecture provided"
        {name, _term} -> "\nDefines conjecture: #{name}"
      end

    name_string <>
      includes_string <> types_string <> defs_string <> axioms_string <> conjecture_string
  end
end

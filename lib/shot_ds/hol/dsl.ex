defmodule ShotDs.Hol.Dsl do
  @moduledoc """
  Introduces a domain specific language (DSL) for constructing HOL terms.

  The DSL utilizes unused Elixir operators with the following precedence:

        (Highest)    ~>, <~>    [Implication, Equivalence]
                     &&&        [Conjunction]
        (Lowest)     |||        [Disjunction]

  > #### Note {: .info}
  >
  > All operators are left-associative, so `a ~> b ~> c` parses as
  > `(a ~> b) ~> c`.

  > #### Warning {: .warning}

  > The operator `&&&` and `|||` will clash with the operators defined in the
  > `Bitwise` module. Consider hiding these definitions when importing
  > `Bitwise`.
  """

  import ShotDs.Hol.Definitions,
    only: [
      neg_term: 0,
      or_term: 0,
      and_term: 0,
      implies_term: 0,
      equivalent_term: 0,
      equals_term: 1,
      pi_term: 1,
      sigma_term: 1
    ]

  alias ShotDs.Data.{Type, Declaration, Term}
  alias ShotDs.Stt.TermFactory, as: TF

  @doc "Logical Negation"
  @spec neg(Term.term_id()) :: Term.term_id()
  def neg(a), do: app(neg_term(), a)

  @doc "Logical Disjunction (OR)"
  @spec Term.term_id() ||| Term.term_id() :: Term.term_id()
  def a ||| b, do: app(or_term(), [a, b])

  @doc "Logical Conjunction (AND)"
  @spec Term.term_id() &&& Term.term_id() :: Term.term_id()
  def a &&& b, do: app(and_term(), [a, b])

  @doc "Logical Implication"
  @spec Term.term_id() ~> Term.term_id() :: Term.term_id()
  def a ~> b, do: app(implies_term(), [a, b])

  @doc "Logical Equivalence"
  @spec Term.term_id() <~> Term.term_id() :: Term.term_id()
  def a <~> b, do: app(equivalent_term(), [a, b])

  @doc """
  Logical Equality.

  Automatically infers the Hol type by inspecting the left argument's term in
  the ETS cache.
  """
  @spec eq(Term.term_id(), Term.term_id()) :: Term.term_id()
  def eq(a, b) do
    term_a = TF.get_term(a)
    app(equals_term(term_a.type), [a, b])
  end

  @doc """
  Logical Inequality.

  Automatically infers the Hol type by inspecting the left argument's term in
  the ETS cache.
  """
  @spec neq(Term.term_id(), Term.term_id()) :: Term.term_id()
  def neq(a, b), do: neg(eq(a, b))

  @doc """
  Universal quantification. Supports single or multiple variables.

  ## Examples

      iex> forall(Type.new(:i), fn x -> ... end)

      iex> forall([Type.new(:o, [:o, :o]), Type.new(:o), Type.new(:o)], fn r, x, y -> ... end)
  """
  @spec forall([Type.t()] | Type.t(), (... -> Term.term_id())) :: Term.term_id()
  def forall(var_types, body_fn) when is_list(var_types) and is_function(body_fn),
    do: build_quantified_term(var_types, body_fn, &pi_term/1)

  def forall(%Type{} = t, body_fn) when is_function(body_fn),
    do: forall([t], body_fn)

  @doc """
  Existential quantification. Supports single or multiple variables.

  ## Examples

      iex> exists(Type.new(:i), fn x -> ... end)

      iex> exists([Type.new(:o, [:o, :o]), Type.new(:o), Type.new(:o)], fn r, x, y -> ... end)
  """
  @spec exists([Type.t()] | Type.t(), (... -> Term.term_id())) :: Term.term_id()
  def exists(var_types, body_fn) when is_list(var_types) and is_function(body_fn),
    do: build_quantified_term(var_types, body_fn, &sigma_term/1)

  def exists(%Type{} = t, body_fn) when is_function(body_fn),
    do: exists([t], body_fn)

  defp build_quantified_term(var_types, body_fn, quantifier_fn) do
    decls = Enum.map(var_types, &Declaration.fresh_var/1)
    var_terms = Enum.map(decls, &TF.make_term/1)
    body_term_id = apply(body_fn, var_terms)

    List.foldr(decls, body_term_id, fn %Declaration{type: type} = decl, acc_term_id ->
      abstracted_body = TF.make_abstr_term(acc_term_id, decl)
      quantifier_fn.(type) |> app(abstracted_body)
    end)
  end

  @doc """
  Applies a term to a single argument term or list of argument terms.
  """
  @spec app(Term.term_id(), [Term.term_id()] | Term.term_id()) :: Term.term_id()
  def app(head_id, arg_ids) when is_integer(head_id) and is_list(arg_ids) do
    TF.fold_apply(head_id, arg_ids)
  end

  def app(head_id, arg_id) when is_integer(head_id) and is_integer(arg_id) do
    TF.make_appl_term(head_id, arg_id)
  end

  @doc """
  Constructs a lambda abstraction over a list of variable types. Temporary
  fresh free variables will be generated corresponding to the types. Passes the
  generated variable term IDs to the provided `body_fn`. The arity of `body_fn`
  must correspond to the number of given variables.

  ## Examples:

      iex> lambda(Type.new(:i), fn x -> ... end)

      iex> lambda([Type.new(:o), Type.new(:o), Type.new(:o)], fn x, y, z -> ... end)
  """
  @spec lambda([Type.t()] | Type.t(), (... -> Term.term_id())) :: Term.term_id()
  def lambda(var_types, body_fn) when is_function(body_fn) do
    decls =
      var_types
      |> List.wrap()
      |> List.flatten()
      |> Enum.map(&Declaration.fresh_var/1)

    var_terms = Enum.map(decls, &TF.make_term/1)
    body_term_id = apply(body_fn, var_terms)
    List.foldr(decls, body_term_id, &TF.make_abstr_term(&2, &1))
  end
end

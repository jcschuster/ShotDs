defmodule ShotDs.Stt.Booleans do
  @moduledoc """
  Church's encoding of Booleans in simple type theory (STT).

  Church defines Booleans as lambda-abstractions which take a value for truth
  and a value for falsity. Conversely, the term denoting truth (`tt`) projects
  the first value, the term for falsity (`ff`) projects the second.

  > #### Note {: .info}
  >
  > Some standard encodings like _if-then-else_ are only definable as
  > parameterized family of terms in STT, not as polymorphic statements.
  """
  import ShotDs.Hol.Dsl
  alias ShotDs.Data.{Type, Declaration, Term}

  @doc ~S"""
  Returns the simple type of an encoded Boolean following the given base type,
  i.e. $\iota\to\iota\to\iota$ for $\iota$.
  """
  @spec b_type(Type.t()) :: Type.t()
  def b_type(base \\ %Type{goal: :i, args: []}),
    do: Type.new(base, [base, base])

  @doc group: :Values
  @doc ~S"""
  Returns the ID of the term corresponding to the Boolean value _true_.

  $$\mathtt{tt} := \lambda AB.\,A$$
  """
  @spec tt(Type.t()) :: Term.term_id()
  def tt(base \\ %Type{goal: :i, args: []}),
    do: lambda([base, base], fn a, _b -> a end)

  @doc group: :Values
  @doc ~S"""
  Returns the ID of the term corresponding to the Boolean value _false_.

  $$\mathtt{ff} := \lambda AB.\,B$$
  """
  @spec ff(Type.t()) :: Term.term_id()
  def ff(base \\ %Type{goal: :i, args: []}),
    do: lambda([base, base], fn _a, b -> b end)

  @doc """
  Generates a variable term with the given name corresponding to a Church
  Boolean.
  """
  @spec b_var(Declaration.var_name_t(), Type.t()) :: Term.term_id()
  def b_var(name, base \\ %Type{goal: :i, args: []}) when is_binary(name) or is_reference(name),
    do: var(name, b_type(base))

  @doc group: :Operators
  @doc ~S"""
  Generates the Church Boolean corresponding to the negation of the Boolean term
  associated with the given ID.

  $$\mathtt{b\_not} := \lambda PAB.\,P\,B\,A$$
  """
  @spec b_not(Term.term_id(), Type.t()) :: Term.term_id()
  def b_not(p, base \\ %Type{goal: :i, args: []}),
    do: lambda([base, base], fn a, b -> app(p, [b, a]) end)

  @doc group: :Operators
  @doc ~S"""
  Generates the Church Boolean corresponding to the logical conjunction of the
  Boolean terms associated with the given IDs.

  $$\mathtt{b\_and} := \lambda PQAB.\,P\,(Q\,A\,B)\,B$$
  """
  @spec b_and(Term.term_id(), Term.term_id(), Type.t()) :: Term.term_id()
  def b_and(p, q, base \\ %Type{goal: :i, args: []}),
    do: lambda([base, base], fn a, b -> app(p, [app(q, [a, b]), b]) end)

  @doc group: :Operators
  @doc ~S"""
  Generates the Church boolean corresponding to the logical disjunction of the
  Boolean terms associated with the given IDs.

  $$\mathtt{b\_or} := \lambda PQAB.\,P\,A\,(Q\,A\,B)$$
  """
  @spec b_or(Term.term_id(), Term.term_id(), Type.t()) :: Term.term_id()
  def b_or(p, q, base \\ %Type{goal: :i, args: []}),
    do: lambda([base, base], fn a, b -> app(p, [a, app(q, [a, b])]) end)
end

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
  import ShotDs.Hol.{Definitions, Dsl}
  alias ShotDs.Data.{Type, Declaration, Term}

  @doc ~S"""
  Returns the simple type of an encoded Boolean, i.e. $\iota\to\iota\to\iota$.
  """
  @spec b_type() :: Type.t()
  def b_type, do: type_iii()

  @doc group: :Values
  @doc ~S"""
  Returns the ID of the term corresponding to the Boolean value _true_.

  $$\mathtt{tt} := \lambda AB.\text{ }A$$
  """
  @spec tt() :: Term.term_id()
  def tt, do: lambda([type_i(), type_i()], fn a, _b -> a end)

  @doc group: :Values
  @doc ~S"""
  Returns the ID of the term corresponding to the Boolean value _false_.

  $$\mathtt{ff} := \lambda AB.\text{ }B$$
  """
  @spec ff() :: Term.term_id()
  def ff, do: lambda([type_i(), type_i()], fn _a, b -> b end)

  @doc """
  Generates a variable term with the given name corresponding to a Church
  Boolean.
  """
  @spec b_var(Declaration.var_name_t()) :: Term.term_id()
  def b_var(name) when is_binary(name) or is_reference(name),
    do: var(name, b_type())

  @doc group: :Operators
  @doc ~S"""
  Generates the Church Boolean corresponding to the negation of the Boolean term
  associated with the given ID.

  $$\mathtt{b\_not} := \lambda PAB.\text{ }P\text{ }B\text{ }A$$
  """
  @spec b_not(Term.term_id()) :: Term.term_id()
  def b_not(p), do: lambda([type_i(), type_i()], fn a, b -> app(p, [b, a]) end)

  @doc group: :Operators
  @doc ~S"""
  Generates the Church Boolean corresponding to the logical conjunction of the
  Boolean terms associated with the given IDs.

  $$\mathtt{b\_and} := \lambda PQAB.\text{ }P\text{ }(Q\text{ }A\text{ }B)\text{ }B$$
  """
  @spec b_and(Term.term_id(), Term.term_id()) :: Term.term_id()
  def b_and(p, q), do: lambda([type_i(), type_i()], fn a, b -> app(p, [app(q, [a, b]), b]) end)

  @doc group: :Operators
  @doc ~S"""
  Generates the Church boolean corresponding to the logical disjunction of the
  Boolean terms associated with the given IDs.

  $$\mathtt{b\_or} := \lambda PQAB.\text{ }P\text{ }A\text{ }(Q\text{ }A\text{ }B)$$
  """
  @spec b_or(Term.term_id(), Term.term_id()) :: Term.term_id()
  def b_or(p, q), do: lambda([type_i(), type_i()], fn a, b -> app(p, [a, app(q, [a, b])]) end)
end

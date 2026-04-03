defmodule ShotDs.Stt.Booleans do
  @moduledoc """
  Church's encoding of Booleans in simple type theory (STT).

  Church defines Booleans as lambda-abstractions which take a value for truth
  and a value for falsity. Conversely, the term denoting truth (`tt`) projects
  the first value, the term for falsity (`ff`) projects the second.

  > #### Note {: .info}
  >
  > Some standard encodings like _if-then-else_ are only definable as
  > parameterized family of terms in STT.
  """
  import ShotDs.Hol.{Definitions, Dsl}
  alias ShotDs.Data.{Type, Declaration, Term}

  @doc """
  Returns the simple type of an encoded boolean.
  """
  @spec b_type() :: Type.t()
  def b_type, do: Type.new(:i, [:i, :i])

  @doc """
  Returns the ID of the term corresponding to the boolean value _true_.
  """
  @spec tt() :: Term.term_id()
  def tt, do: lambda([type_i(), type_i()], fn t, _f -> t end)

  @doc """
  Returns the ID of the term corresponding to the boolean value _false_.
  """
  @spec ff() :: Term.term_id()
  def ff, do: lambda([type_i(), type_i()], fn _t, f -> f end)

  @doc """
  Generates a variable term with the given name corresponding to a Church
  boolean.
  """
  @spec b_var(Declaration.var_name_t()) :: Term.term_id()
  def b_var(name) when is_binary(name) or is_reference(name),
    do: var(name, b_type())

  @doc """
  Generates the Church boolean corresponding to the negation of the boolean term
  associated with the given ID.
  """
  @spec b_not(Term.term_id()) :: Term.term_id()
  def b_not(p), do: app(p, [ff(), tt()])

  @doc """
  Generates the Church boolean corresponding to the logical conjunction of the
  boolean terms associated with the given IDs.
  """
  @spec b_and(Term.term_id(), Term.term_id()) :: Term.term_id()
  def b_and(p, q), do: app(p, [q, p])

  @doc """
  Generates the Church boolean corresponding to the logical disjunction of the
  boolean terms associated with the given IDs.
  """
  @spec b_or(Term.term_id(), Term.term_id()) :: Term.term_id()
  def b_or(p, q), do: app(p, [p, q])
end

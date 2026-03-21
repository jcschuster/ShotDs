defmodule ShotDs.Stt.Numerals do
  @moduledoc """
  Encodes Church numerals in simple type theory.

  Church numerals are defined as lambda-abstractions which take a successor
  function *s* and a starting point *z* and returns the *n*-fold application
  of the successor function to the starting point.

  > #### Note {: .info}
  >
  > Some functions are not definable without polymorphism. This includes for
  > example the predecessor function, subtraction and exponentiation.
  """
  import ShotDs.Hol.{Definitions, Dsl}
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Data.{Type, Declaration, Term}

  @i %Type{goal: :i, args: []}
  @ii %Type{goal: :i, args: [@i]}
  @s %Declaration{kind: :bv, name: 2, type: @ii}
  @z %Declaration{kind: :bv, name: 1, type: @i}

  @doc """
  Generates the Church numeral corresponding to the given natural number.
  Returns the ID of the generated term.
  """
  @spec num(non_neg_integer()) :: Term.term_id()
  def num(n) when is_integer(n) do
    if n < 0 do
      raise "ArgumentError: Church numerals are only defined for natural numbers!"
    end

    lambda([type_ii(), type_i()], fn s, z ->
      Enum.reduce(1..n//1, z, fn _, c -> app(s, c) end)
    end)
  end

  @doc """
  Generates the successor of the Church numeral term corresponding to the given
  ID. Returns the ID of the generated term.
  """
  @spec succ(Term.term_id()) :: Term.term_id()
  def succ(n_id) when is_integer(n_id) do
    if !numeral?(n_id) do
      raise "ArgumentError: the successor function is only defined on Church numerals!"
    end

    lambda([type_ii(), type_i()], fn s, z ->
      app(s, app(n_id, [s, z]))
    end)
  end

  @doc """
  Generates the Church numeral corresponding to the addition of the terms with
  the given IDs. Returns the ID of the resulting term.
  """
  @spec plus(Term.term_id(), Term.term_id()) :: Term.term_id()
  def plus(m_id, n_id) when is_integer(m_id) and is_integer(n_id) do
    if !numeral?(m_id) || !numeral?(n_id) do
      raise "ArgumentError: the addition function is only defined on Church numerals!"
    end

    lambda([type_ii(), type_i()], fn s, z ->
      app(m_id, [s, app(n_id, [s, z])])
    end)
  end

  @doc """
  Generates the Church numeral corresponding to the multiplication of the terms
  with the given IDs. Returns the ID of the resulting term.
  """
  @spec mult(Term.term_id(), Term.term_id()) :: Term.term_id()
  def mult(m_id, n_id) when is_integer(m_id) and is_integer(n_id) do
    if !numeral?(m_id) || !numeral?(n_id) do
      raise "ArgumentError: the multiplication function is only defined on Church numerals!"
    end

    lambda([type_ii(), type_i()], fn s, z ->
      app(m_id, [app(n_id, s), z])
    end)
  end

  @doc """
  Checks whether the term corresponding to the given ID is a valid Church
  numeral.
  """
  @spec numeral?(Term.term_id()) :: boolean()
  def numeral?(term_id) when is_integer(term_id) do
    %Term{} = term = TF.get_term(term_id)

    case term do
      %Term{bvars: [@s, @z], type: %Type{args: [@ii, @i | rest]} = type} ->
        numeral_body?(%Term{term | bvars: [], type: %Type{type | args: rest}})

      _ ->
        false
    end
  end

  defp numeral_body?(%Term{bvars: [], head: @z, args: []}), do: true

  defp numeral_body?(%Term{bvars: [], head: @s, args: [inner]}),
    do: numeral_body?(TF.get_term(inner))

  defp numeral_body?(_), do: false
end

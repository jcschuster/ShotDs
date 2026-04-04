defmodule ShotDs.Stt.Numerals do
  @moduledoc ~S"""
  Encodes Church numerals in simple type theory.

  Church numerals are defined as lambda-abstractions which take a successor
  function $S_{\iota\to\iota}$ and a starting point $Z_\iota$ and returns the
  *n*-fold application of the successor function to the starting point. I.e.,
  in our encoding, numerals are represented as a term of type
  $(\iota\to\iota)\to\iota\to\iota$.

  Simple arithmetic operators can be defined ontop of this encoding as Church
  numerals correspond to iterators. Some examples of this are implemented in
  this module.

  > #### Note {: .info}
  >
  > Some functions are not definable without polymorphism. This includes for
  > example the predecessor function, subtraction and exponentiation.

  Some examples ($S^{\circ n}$ represents that $S$ is applied $n$ times):

  | Number   | Encoding                                              |
  |----------|-------------------------------------------------------|
  | 0        | $\lambda SZ.\text{ }Z$                                |
  | 1        | $\lambda SZ.\text{ }S\text{ }Z$                       |
  | 2        | $\lambda SZ.\text{ }S\text{ }(S\text{ }Z)$            |
  | 3        | $\lambda SZ.\text{ }S\text{ }(S\text{ }(S\text{ }Z))$ |
  | $\vdots$ | $\vdots$                                              |
  | $n$      | $\lambda SZ.\text{ }S^{\circ n}\text{ }Z$             |
  """
  import ShotDs.Hol.{Definitions, Dsl}
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Data.{Type, Declaration, Term}

  @i %Type{goal: :i, args: []}
  @ii %Type{goal: :i, args: [@i]}
  @s %Declaration{kind: :bv, name: 2, type: @ii}
  @z %Declaration{kind: :bv, name: 1, type: @i}

  @doc ~S"""
  Returns the simple type corresponding to an encoded numeral, i.e.,
  $(\iota\to\iota)\to\iota\to\iota$.
  """
  @spec n_type() :: Type.t()
  def n_type, do: Type.new(:i, [@ii, :i])

  @doc """
  Generates the Church numeral corresponding to the given natural number.
  Returns the ID of the generated term.
  """
  @spec num(non_neg_integer()) :: Term.term_id()
  def num(n) when is_integer(n) do
    if n < 0 do
      raise ArgumentError, message: "Church numerals are only defined for natural numbers!"
    end

    lambda([type_ii(), type_i()], fn s, z ->
      Enum.reduce(1..n//1, z, fn _, c -> app(s, c) end)
    end)
  end

  @doc """
  Generates a variable term with the given name corresponding to a church
  numeral.
  """
  @spec num_var(Declaration.var_name_t()) :: Term.term_id()
  def num_var(name) when is_binary(name) or is_reference(name),
    do: var(name, n_type())

  @doc group: :Operators
  @doc ~S"""
  Generates the successor of the Church numeral term corresponding to the given
  ID. Returns the ID of the generated term.

  $$\mathtt{succ} := \lambda NSZ.\text{ }S\text{ }(N\text{ }S\text{ }Z)$$
  """
  @spec succ(Term.term_id()) :: Term.term_id()
  def succ(n_id) do
    lambda([type_ii(), type_i()], fn s, z ->
      app(s, app(n_id, [s, z]))
    end)
  end

  @doc group: :Operators
  @doc ~S"""
  Generates the Church numeral corresponding to the addition of the terms with
  the given IDs. Returns the ID of the resulting term.

  $$\mathtt{plus} := \lambda MNSZ.\text{ }M\text{ }S\text{ }(N\text{ }S\text{ }Z)$$
  """
  @spec plus(Term.term_id(), Term.term_id()) :: Term.term_id()
  def plus(m_id, n_id) do
    lambda([type_ii(), type_i()], fn s, z ->
      app(m_id, [s, app(n_id, [s, z])])
    end)
  end

  @doc group: :Operators
  @doc ~S"""
  Generates the Church numeral corresponding to the multiplication of the terms
  with the given IDs. Returns the ID of the resulting term.

  $$\mathtt{mult} := \lambda MNSZ.\text{ }M\text{ }(N\text{ }S)\text{ }Z$$
  """
  @spec mult(Term.term_id(), Term.term_id()) :: Term.term_id()
  def mult(m_id, n_id) do
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
    %Term{} = term = TF.get_term!(term_id)

    case term do
      %Term{bvars: [@s, @z], type: %Type{args: [@ii, @i | rest]} = type} ->
        numeral_body?(%Term{term | bvars: [], type: %Type{type | args: rest}})

      _ ->
        false
    end
  end

  defp numeral_body?(%Term{bvars: [], head: @z, args: []}), do: true

  defp numeral_body?(%Term{bvars: [], head: @s, args: [inner]}),
    do: numeral_body?(TF.get_term!(inner))

  defp numeral_body?(_), do: false
end

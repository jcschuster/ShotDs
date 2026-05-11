defmodule ShotDs.Stt.Numerals do
  @moduledoc ~S"""
  Encodes Church numerals in simple type theory.

  Church numerals are defined as lambda-abstractions which take a successor
  function $S_{\tau\to\tau}$ and a starting point $Z_\tau$ and returns the
  *n*-fold application of the successor function to the starting point. I.e.,
  in our encoding, numerals are represented as a term of type
  $(\tau\to\tau)\to\tau\to\tau$ for any base $\tau$.

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
  | 0        | $\lambda SZ.\,Z$                                      |
  | 1        | $\lambda SZ.\,S\,Z$                                   |
  | 2        | $\lambda SZ.\,S\,(S\,Z)$                              |
  | 3        | $\lambda SZ.\,S\,(S\,(S\,Z))$                         |
  | $\vdots$ | $\vdots$                                              |
  | $n$      | $\lambda SZ.\,S^{\circ n}\,Z$                         |
  """
  import ShotDs.Hol.Dsl
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Data.{Type, Declaration, Term}

  @doc ~S"""
  Returns the simple type corresponding to an encoded numeral, e.g.,
  $(\iota\to\iota)\to\iota\to\iota$.
  """
  @spec n_type(Type.t()) :: Type.t()
  def n_type(base \\ %Type{goal: :i, args: []}),
    do: Type.new(base, [Type.new(base, base), base])

  @doc """
  Generates the Church numeral corresponding to the given natural number.
  Returns the ID of the generated term.
  """
  @spec num(non_neg_integer()) :: Term.term_id()
  def num(n, base \\ %Type{goal: :i, args: []}) when is_integer(n) do
    if n < 0 do
      raise ArgumentError, message: "Church numerals are only defined for natural numbers!"
    end

    lambda([Type.new(base, base), base], fn s, z ->
      Enum.reduce(1..n//1, z, fn _, c -> app(s, c) end)
    end)
  end

  @doc """
  Generates a variable term with the given name corresponding to a church
  numeral.
  """
  @spec num_var(Declaration.var_name_t(), Type.t()) :: Term.term_id()
  def num_var(name, base \\ %Type{goal: :i, args: []}) when is_binary(name) or is_reference(name),
    do: var(name, n_type(base))

  @doc group: :Operators
  @doc ~S"""
  Generates the successor of the Church numeral term corresponding to the given
  ID. Returns the ID of the generated term.

  $$\mathtt{succ} := \lambda NSZ.\,S\,(N\,S\,Z)$$
  """
  @spec succ(Term.term_id(), Type.t()) :: Term.term_id()
  def succ(n_id, base \\ %Type{goal: :i, args: []}) do
    lambda([Type.new(base, base), base], fn s, z ->
      app(s, app(n_id, [s, z]))
    end)
  end

  @doc group: :Operators
  @doc ~S"""
  Generates the Church numeral corresponding to the addition of the terms with
  the given IDs. Returns the ID of the resulting term.

  $$\mathtt{plus} := \lambda MNSZ.\,M\,S\,(N\,S\,Z)$$
  """
  @spec plus(Term.term_id(), Term.term_id(), Type.t()) :: Term.term_id()
  def plus(m_id, n_id, base \\ %Type{goal: :i, args: []}) do
    lambda([Type.new(base, base), base], fn s, z ->
      app(m_id, [s, app(n_id, [s, z])])
    end)
  end

  @doc group: :Operators
  @doc ~S"""
  Generates the Church numeral corresponding to the multiplication of the terms
  with the given IDs. Returns the ID of the resulting term.

  $$\mathtt{mult} := \lambda MNSZ.\,M\,(N\,S)\,Z$$
  """
  @spec mult(Term.term_id(), Term.term_id(), Type.t()) :: Term.term_id()
  def mult(m_id, n_id, base \\ %Type{goal: :i, args: []}) do
    lambda([Type.new(base, base), base], fn s, z ->
      app(m_id, [app(n_id, s), z])
    end)
  end

  @doc """
  Checks whether the term corresponding to the given ID is a valid Church
  numeral.
  """
  @spec numeral?(Term.term_id(), Type.t()) :: boolean()
  def numeral?(term_id, base \\ %Type{goal: :i, args: []}) when is_integer(term_id) do
    %Term{} = term = TF.get_term!(term_id)

    s_type = Type.new(base, base)
    s = Declaration.new_bound_var(2, s_type)
    z = Declaration.new_bound_var(1, base)

    case term do
      %Term{bvars: [^s, ^z], type: %Type{args: [^s_type, ^base | rest]} = type} ->
        numeral_body?(%Term{term | bvars: [], type: %Type{type | args: rest}}, base)

      _ ->
        false
    end
  end

  defp numeral_body?(%Term{bvars: [], head: z, args: []}, base),
    do: z == %Declaration{kind: :bv, name: 1, type: base}

  defp numeral_body?(%Term{bvars: [], head: s, args: [inner]}, base) do
    s == %Declaration{kind: :bv, name: 2, type: Type.new(base, base)} and
      numeral_body?(TF.get_term!(inner), base)
  end

  defp numeral_body?(_, _), do: false
end

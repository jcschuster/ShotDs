defmodule ShotDs.Hol.Definitions do
  @moduledoc """
  Provides definitions for common HOL types, terms and constants.

  This module implements the following propositional constants:

  `⊤::o, ⊥::o, ¬::o->o, ∨::o->o->o, ∧::o->o->o, ⊃::o->o->o, ≡::o->o->o`

  Additionally, the following polymorphic higher-order constants:

  `=::t->t->o, Π::(t->o)->o, Σ::(t->o)->o`
  """

  alias ShotDs.Data.{Type, Declaration, Term}
  alias ShotDs.TermFactory, as: TF

  #############################################################################
  # TYPES
  #############################################################################

  @doc group: :Types
  @doc """
  Base type for booleans (type o). Represents true or false.
  """
  @spec type_o() :: Type.t()
  def type_o, do: Type.new(:o)

  @doc group: :Types
  @doc """
  Base type for individuals (type i).
  """
  @spec type_i() :: Type.t()
  def type_i, do: Type.new(:i)

  @doc group: :Types
  @doc """
  Type for symbols of type o->o, e.g. unary connectives like negateion.
  """
  @spec type_oo() :: Type.t()
  def type_oo, do: Type.new(:o, :o)

  @doc group: :Types
  @doc """
  Type for symbols of type o->o->o, e.g. binary connectives like conjunction.
  """
  @spec type_ooo() :: Type.t()
  def type_ooo, do: Type.new(:o, [:o, :o])

  @doc group: :Types
  @doc """
  Type for symbols of type i->i, i.e., endomorphisms/operators on type i.
  """
  @spec type_ii() :: Type.t()
  def type_ii, do: Type.new(:i, :i)

  @doc group: :Types
  @doc """
  Type for symbols of type i->i->i, i.e., binary operators on type i.
  """
  @spec type_iii() :: Type.t()
  def type_iii, do: Type.new(:i, [:i, :i])

  @doc group: :Types
  @doc """
  Type for symbols of type i->o, e.g. sets of individuals or predicates over
  individuals.
  """
  @spec type_io() :: Type.t()
  def type_io, do: Type.new(:o, :i)

  @doc group: :Types
  @doc """
  Type for symbols of type i->i->o, e.g. relations on individuals.
  """
  @spec type_iio() :: Type.t()
  def type_iio, do: Type.new(:o, [:i, :i])

  @doc group: :Types
  @doc """
  Type for symbols of type (i->o)->o, e.g. sets of sets of individuals, or
  predicates over sets of individuals.
  """
  @spec type_io_o() :: Type.t()
  def type_io_o, do: Type.new(:o, Type.new(:o, :i))

  @doc group: :Types
  @doc """
  Type for symbols of type (i->o)->i, e.g. the choice operator (Hilbert's
  epsilon).
  """
  @spec type_io_i() :: Type.t()
  def type_io_i, do: Type.new(:i, Type.new(:o, :i))

  @doc group: :Types
  @doc """
  Type for symbols of type (i->o)->(i->o)->o, i.e. relations between sets of
  individuals, e.g. the subset relation.
  """
  @spec type_io_io_o() :: Type.t()
  def type_io_io_o, do: Type.new(:o, [Type.new(:o, :i), Type.new(:o, :i)])

  @doc group: :Types
  @doc """
  Type for symbols of type (i->o)->(i->o)->i->o, e.g. set operations like union
  or intersection.
  """
  @spec type_io_io_io() :: Type.t()
  def type_io_io_io, do: Type.new(:o, [Type.new(:o, :i), Type.new(:o, :i), :i])

  #############################################################################
  # CONSTANTS
  #############################################################################

  @doc group: :Constants
  @doc """
  Constant representing truth.
  """
  @spec true_const() :: Declaration.const_t()
  def true_const, do: Declaration.new_const("⊤", type_o())

  @doc group: :Constants
  @doc """
  Constant representing falsity.
  """
  @spec false_const() :: Declaration.const_t()
  def false_const, do: Declaration.new_const("⊥", type_o())

  @doc group: :Constants
  @doc """
  Constant representing the negation operator.
  """
  @spec neg_const() :: Declaration.const_t()
  def neg_const, do: Declaration.new_const("¬", type_oo())

  @doc group: :Constants
  @doc """
  Constant representing the disjunction operator.
  """
  @spec or_const() :: Declaration.const_t()
  def or_const, do: Declaration.new_const("∨", type_ooo())

  @doc group: :Constants
  @doc """
  Constant representing the conjunction operator.
  """
  @spec and_const() :: Declaration.const_t()
  def and_const, do: Declaration.new_const("∧", type_ooo())

  @doc group: :Constants
  @doc """
  Constant representing the implication operator.
  """
  @spec implies_const() :: Declaration.const_t()
  def implies_const, do: Declaration.new_const("⊃", type_ooo())

  @doc group: :Constants
  @doc """
  Constant representing the equivalence operator.
  """
  @spec equivalent_const() :: Declaration.const_t()
  def equivalent_const, do: Declaration.new_const("≡", type_ooo())

  @doc group: :Constants
  @doc """
  Constant representing equality over instances of the given type.
  """
  @spec equals_const(Type.t()) :: Declaration.const_t()
  def equals_const(%Type{} = t), do: Declaration.new_const("=", Type.new(:o, [t, t]))

  @doc group: :Constants
  @doc """
  Constant representing the pi operator (universal quantification) over the
  given element type.
  """
  @spec pi_const(Type.t()) :: Declaration.const_t()
  def pi_const(%Type{} = t), do: Declaration.new_const("Π", Type.new(:o, Type.new(:o, t)))

  @doc group: :Constants
  @doc """
  Constant representing the sigma operator (existential quantification) over
  the given element type.
  """
  @spec sigma_const(Type.t()) :: Declaration.const_t()
  def sigma_const(%Type{} = t), do: Declaration.new_const("Σ", Type.new(:o, Type.new(:o, t)))

  #############################################################################
  # TERMS
  #############################################################################

  @doc group: :Terms
  @doc """
  Term representing truth.
  """
  @spec true_term() :: Term.term_id()
  def true_term, do: TF.make_const_term("⊤", type_o())

  @doc group: :Terms
  @doc """
  Term representing falsity.
  """
  @spec false_term() :: Term.term_id()
  def false_term, do: TF.make_const_term("⊥", type_o())

  @doc group: :Terms
  @doc """
  Term representing the negation operator.
  """
  @spec neg_term() :: Term.term_id()
  def neg_term, do: TF.make_const_term("¬", type_oo())

  @doc group: :Terms
  @doc """
  Term representing the disjunction operator.
  """
  @spec or_term() :: Term.term_id()
  def or_term, do: TF.make_const_term("∨", type_ooo())

  @doc group: :Terms
  @doc """
  Term representing the negated disjunction operator. As it is not part of the
  signature, it is defined as negated disjunction.
  """
  def nor_term do
    x = Declaration.new_free_var("X", type_o())
    y = Declaration.new_free_var("Y", type_o())

    disj = or_term() |> TF.make_appl_term(TF.make_term(x)) |> TF.make_appl_term(TF.make_term(y))
    neg_term() |> TF.make_appl_term(disj) |> TF.make_abstr_term(y) |> TF.make_abstr_term(x)
  end

  @doc group: :Terms
  @doc """
  Term representing the conjunction operator.
  """
  @spec and_term() :: Term.term_id()
  def and_term, do: TF.make_const_term("∧", type_ooo())

  @doc group: :Terms
  @doc """
  Term representing the negated conjunction operator. As it is not part of the
  signature, it is represented as negated conjunction.
  """
  def nand_term do
    x = Declaration.new_free_var("X", type_o())
    y = Declaration.new_free_var("Y", type_o())

    conj = and_term() |> TF.make_appl_term(TF.make_term(x)) |> TF.make_appl_term(TF.make_term(y))
    neg_term() |> TF.make_appl_term(conj) |> TF.make_abstr_term(y) |> TF.make_abstr_term(x)
  end

  @doc group: :Terms
  @doc """
  Term representing the implication operator.
  """
  @spec implies_term() :: Term.term_id()
  def implies_term, do: TF.make_const_term("⊃", type_ooo())

  @doc group: :Terms
  @doc """
  Term representing the converse of the implication operator. As it is not part
  of the signature, it is represented as implication with flipped arguments.
  """
  def implied_by_term do
    x = Declaration.new_free_var("X", type_o())
    y = Declaration.new_free_var("Y", type_o())

    implies_term()
    |> TF.make_appl_term(TF.make_term(y))
    |> TF.make_appl_term(TF.make_term(x))
    |> TF.make_abstr_term(y)
    |> TF.make_abstr_term(x)
  end

  @doc group: :Terms
  @doc """
  Term representing the equivalence operator.
  """
  @spec equivalent_term() :: Term.term_id()
  def equivalent_term, do: TF.make_const_term("≡", type_ooo())

  @doc group: :Terms
  @doc """
  Term representing the exclusive disjunction operator. As it is no part of the
  signature, it is represented as negated equivalence.
  """
  def xor_term do
    x = Declaration.new_free_var("X", type_o())
    y = Declaration.new_free_var("Y", type_o())

    equiv =
      equivalent_term()
      |> TF.make_appl_term(TF.make_term(x))
      |> TF.make_appl_term(TF.make_term(y))

    neg_term() |> TF.make_appl_term(equiv) |> TF.make_abstr_term(y) |> TF.make_abstr_term(x)
  end

  @doc group: :Terms
  @doc """
  Term representing equality over instances of the given type.
  """
  @spec equals_term(Type.t()) :: Term.term_id()
  def equals_term(%Type{} = t), do: TF.make_const_term("=", Type.new(:o, [t, t]))

  @doc group: :Terms
  @doc """
  Term representing unequality over instances of the given type. As it is not
  part of the signature, it is represented as negated equality.
  """
  @spec not_equals_term(Type.t()) :: Term.term_id()
  def not_equals_term(%Type{} = t) do
    x = Declaration.new_free_var("X", t)
    y = Declaration.new_free_var("Y", t)

    eq =
      equals_term(t) |> TF.make_appl_term(TF.make_term(x)) |> TF.make_appl_term(TF.make_term(y))

    neg_term() |> TF.make_appl_term(eq) |> TF.make_abstr_term(y) |> TF.make_abstr_term(x)
  end

  @doc group: :Terms
  @doc """
  Term representing the pi operator (universal quantification) over the
  given element type.
  """
  @spec pi_term(Type.t()) :: Term.term_id()
  def pi_term(%Type{} = t), do: TF.make_const_term("Π", Type.new(:o, Type.new(:o, t)))

  @doc group: :Terms
  @doc """
  Term representing the sigma operator (existential quantification) over
  the given element type.
  """
  @spec sigma_term(Type.t()) :: Term.term_id()
  def sigma_term(%Type{} = t), do: TF.make_const_term("Σ", Type.new(:o, Type.new(:o, t)))

  @doc """
  Constructor for Leibniz equality on the given type, which defines equality by
  stating that both arguments share the same properties. Generates an
  abstraction which can be applied to two arguments.

  # Examples

      iex> leibniz_equality(type_i(), equivalent_term()) == parse("^[X:$i, Y:$i]: ![P:$i>$o]: P @ X <=> P @ Y")
      true

      iex> leibniz_equality(type_i(), implied_by_term()) == parse("^[X:$i, Y:$i]: ![P:$i>$o]: P @ X <= P @ Y")
      true
  """
  @spec leibniz_equality(Type.t(), :equiv | :imp | :conv_imp) :: Term.term_id()
  def leibniz_equality(type, connective \\ :equiv)

  def leibniz_equality(%Type{} = type, :equiv), do: mk_leibniz_equality(type, equivalent_term())

  def leibniz_equality(%Type{} = type, :imp), do: mk_leibniz_equality(type, implies_term())

  def leibniz_equality(%Type{} = type, :conv_imp),
    do: mk_leibniz_equality(type, implied_by_term())

  defp mk_leibniz_equality(type, connective) do
    x = Declaration.new_free_var("X", type)
    y = Declaration.new_free_var("Y", type)

    p_type = Type.new(:o, type)
    p = Declaration.new_free_var("P", p_type)
    p_term = TF.make_term(p)

    p_x = TF.make_appl_term(p_term, TF.make_term(x))
    p_y = TF.make_appl_term(p_term, TF.make_term(y))

    connective
    |> TF.make_appl_term(p_x)
    |> TF.make_appl_term(p_y)
    |> TF.make_abstr_term(p)
    |> then(&TF.make_appl_term(pi_term(p_type), &1))
    |> TF.make_abstr_term(y)
    |> TF.make_abstr_term(x)
  end

  @doc """
  Constructor for Andrews equality on the given type, which defines equality by
  stating that both arguments share all reflexive relations. Generates an
  abstraction which can be applied to two arguments.

  # Example

      iex> andrews_equality(type_i()) == parse("^[X:$i, Y:$i]: ![Q:$i>$i>$o]: ((![Z:$i]: Q @ Z @ Z) => Q @ X @ Y)")
      true
  """
  @spec andrews_equality(Type.t()) :: Term.term_id()
  def andrews_equality(%Type{} = type) do
    x = Declaration.new_free_var("X", type)
    y = Declaration.new_free_var("Y", type)
    z = Declaration.new_free_var("Z", type)
    z_term = TF.make_term(z)

    q_type = Type.new(:o, [type, type])
    q = Declaration.new_free_var("Q", q_type)
    q_term = TF.make_term(q)

    lhs =
      q_term
      |> TF.make_appl_term(z_term)
      |> TF.make_appl_term(z_term)
      |> TF.make_abstr_term(z)
      |> then(&TF.make_appl_term(pi_term(type), &1))

    rhs = q_term |> TF.make_appl_term(TF.make_term(x)) |> TF.make_appl_term(TF.make_term(y))

    implies_term()
    |> TF.make_appl_term(lhs)
    |> TF.make_appl_term(rhs)
    |> TF.make_abstr_term(q)
    |> then(&TF.make_appl_term(pi_term(q_type), &1))
    |> TF.make_abstr_term(y)
    |> TF.make_abstr_term(x)
  end

  @doc """
  Constructor for extensional equality on the given function type, which
  defines equality by equality of the extensions. Generates an abstraction
  which can be applied to two arguments.

  # Example

      iex> extensional_equality(type_ii()) == parse("^[X:$i>i, Y:$i>i]: ![Z:$i]: X @ Z = Y @ Z")
      true
  """
  def extensional_equality(%Type{args: [at | rest_ats]} = type) do
    x = Declaration.new_free_var("X", type)
    y = Declaration.new_free_var("Y", type)
    z = Declaration.new_free_var("Z", at)
    z_term = TF.make_term(z)

    x_z = TF.make_appl_term(TF.make_term(x), z_term)
    y_z = TF.make_appl_term(TF.make_term(y), z_term)

    equals_term(%{type | args: rest_ats})
    |> TF.make_appl_term(x_z)
    |> TF.make_appl_term(y_z)
    |> TF.make_abstr_term(z)
    |> then(&TF.make_appl_term(pi_term(at), &1))
    |> TF.make_abstr_term(y)
    |> TF.make_abstr_term(x)
  end

  def extensional_equality(type) do
    raise "ArgumentError: type for extensional equality must be a function type. Got #{inspect(type)} instead."
  end
end

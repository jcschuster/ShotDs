defmodule ShotDs.Hol.Definitions do
  @moduledoc """
  Provides definitions for common HOL types, terms and constants.

  This module implements the following propositional constants:

      ⊤::o, ⊥::o, ¬::o->o, ∨::o->o->o, ∧::o->o->o, ⊃::o->o->o, ≡::o->o->o

  Additionally, the following polymorphic higher-order constants:

      =::t->t->o, Π::(t->o)->o, Σ::(t->o)->o
  """

  alias ShotDs.Data.{Type, Declaration, Term}
  alias ShotDs.TermFactory, as: TF
  import ShotDs.Util.Builder

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
    lambda([type_o(), type_o()], fn x, y ->
      app(neg_term(), app(or_term(), [x, y]))
    end)
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
    lambda([type_o(), type_o()], fn x, y ->
      app(neg_term(), app(and_term(), [x, y]))
    end)
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
    lambda([type_o(), type_o()], fn x, y ->
      app(implies_term(), [y, x])
    end)
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
    lambda([type_o(), type_o()], fn x, y ->
      app(neg_term(), app(equivalent_term(), [x, y]))
    end)
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
    lambda([t, t], fn x, y ->
      app(neg_term(), app(equals_term(t), [x, y]))
    end)
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
end

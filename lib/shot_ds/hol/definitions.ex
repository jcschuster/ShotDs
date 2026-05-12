defmodule ShotDs.Hol.Definitions do
  @moduledoc groups: [:"Simple Types", :Constants, :Terms, :Equality]
  @moduledoc ~S"""
  Provides definitions for common HOL types, terms and constants.

  This module implements the following propositional constants:

  $$\top_o \quad \bot_o \quad \neg_{o\to o} \quad \lor_{o\to o\to o} \quad
  \land_{o\to o\to o} \quad \supset_{o\to o\to o} \quad \equiv_{o\to o\to o}$$

  Additionally, the following parameterized higher-order constants:

  $$=_{\tau\to\tau\to o} \quad \forall_{(\tau\to o)\to o} \quad
  \exists_{(\tau\to o)\to o}$$
  """

  alias ShotDs.Data.{Type, Declaration, Term}
  alias ShotDs.Stt.TermFactory, as: TF

  ##############################################################################
  # TYPES
  ##############################################################################

  @doc group: :"Simple Types"
  @doc """
  Base type for booleans (type $o$). Represents true or false.
  """
  @spec type_o() :: Type.t()
  def type_o, do: Type.new(:o)

  @doc group: :"Simple Types"
  @doc ~S"""
  Base type for individuals (type $\iota$).
  """
  @spec type_i() :: Type.t()
  def type_i, do: Type.new(:i)

  @doc group: :"Simple Types"
  @doc ~S"""
  Type for symbols of type $o\to o$, e.g. unary connectives like negation.
  """
  @spec type_oo() :: Type.t()
  def type_oo, do: Type.new(:o, :o)

  @doc group: :"Simple Types"
  @doc ~S"""
  Type for symbols of type $o\to o\to o$, e.g. binary connectives like
  conjunction.
  """
  @spec type_ooo() :: Type.t()
  def type_ooo, do: Type.new(:o, [:o, :o])

  @doc group: :"Simple Types"
  @doc ~S"""
  Type for symbols of type $\iota\to\iota$, i.e., endomorphisms/operators on
  type $\iota$.
  """
  @spec type_ii() :: Type.t()
  def type_ii, do: Type.new(:i, :i)

  @doc group: :"Simple Types"
  @doc ~S"""
  Type for symbols of type $\iota\to\iota\to\iota$, i.e., binary operators on
  type $\iota$ or Church's encoding of booleans.
  """
  @spec type_iii() :: Type.t()
  def type_iii, do: Type.new(:i, [:i, :i])

  @doc group: :"Simple Types"
  @doc ~S"""
  Type for symbols of type $(\iota\to\iota)\to\iota\to\iota$, i.e., iterators
  like Church numerals.
  """
  @spec type_ii_ii() :: Type.t()
  def type_ii_ii, do: Type.new(:i, [type_ii(), :i])

  @doc group: :"Simple Types"
  @doc ~S"""
  Type for symbols of type $\iota\to o$, e.g. sets of individuals or predicates
  over individuals.
  """
  @spec type_io() :: Type.t()
  def type_io, do: Type.new(:o, :i)

  @doc group: :"Simple Types"
  @doc ~S"""
  Type for symbols of type $\iota\to\iota\to o$, e.g. relations on individuals.
  """
  @spec type_iio() :: Type.t()
  def type_iio, do: Type.new(:o, [:i, :i])

  @doc group: :"Simple Types"
  @doc ~S"""
  Type for symbols of type $(\iota\to o)\to o$, e.g. sets of sets of
  individuals, or predicates over sets of individuals.
  """
  @spec type_io_o() :: Type.t()
  def type_io_o, do: Type.new(:o, Type.new(:o, :i))

  @doc group: :"Simple Types"
  @doc ~S"""
  Type for symbols of type $(\iota\to o)\to\iota$, e.g. the choice operator
  (Hilbert's $\epsilon$).
  """
  @spec type_io_i() :: Type.t()
  def type_io_i, do: Type.new(:i, Type.new(:o, :i))

  @doc group: :"Simple Types"
  @doc ~S"""
  Type for symbols of type $(\iota\to o)\to\iota\to o$, e.g. predicate modifiers
  over type $\iota$.
  """
  @spec type_io_io() :: Type.t()
  def type_io_io, do: Type.new(:i, [Type.new(:o, :i), :i])

  @doc group: :"Simple Types"
  @doc ~S"""
  Type for symbols of type $(\iota\to o)\to(\iota\to o)\to o$, i.e. relations
  between sets of individuals, e.g. the subset relation.
  """
  @spec type_io_io_o() :: Type.t()
  def type_io_io_o, do: Type.new(:o, [Type.new(:o, :i), Type.new(:o, :i)])

  @doc group: :"Simple Types"
  @doc ~S"""
  Type for symbols of type $(\iota\to o)\to(\iota\to o)\to\iota\to o$, e.g. set
  or predicate operations like intersection.
  """
  @spec type_io_io_io() :: Type.t()
  def type_io_io_io, do: Type.new(:o, [Type.new(:o, :i), Type.new(:o, :i), :i])

  ##############################################################################
  # CONSTANTS
  ##############################################################################

  @doc group: :Constants
  @doc """
  Returns the names of the logical connectives from the signature as list.
  """
  @spec signature() :: [String.t()]
  def signature, do: ~w(⊤ ⊥ ¬ ∨ ∧ ⊃ ≡ = ∀ ∃)

  @doc group: :Constants
  @doc ~S"""
  Constant representing truth $\top_o$.
  """
  @spec true_const() :: Declaration.const_t()
  def true_const, do: Declaration.new_const("⊤", type_o())

  @doc group: :Constants
  @doc ~S"""
  Constant representing falsity $\bot_o$.
  """
  @spec false_const() :: Declaration.const_t()
  def false_const, do: Declaration.new_const("⊥", type_o())

  @doc group: :Constants
  @doc ~S"""
  Constant representing the negation operator $\neg_{o\to o}$.
  """
  @spec neg_const() :: Declaration.const_t()
  def neg_const, do: Declaration.new_const("¬", type_oo())

  @doc group: :Constants
  @doc ~S"""
  Constant representing the disjunction operator $\land_{o\to o\to o}$.
  """
  @spec or_const() :: Declaration.const_t()
  def or_const, do: Declaration.new_const("∨", type_ooo())

  @doc group: :Constants
  @doc ~S"""
  Constant representing the conjunction operator $\lor_{o\to o\to o}$.
  """
  @spec and_const() :: Declaration.const_t()
  def and_const, do: Declaration.new_const("∧", type_ooo())

  @doc group: :Constants
  @doc ~S"""
  Constant representing the implication operator $\supset_{o\to o\to o}$.
  """
  @spec implies_const() :: Declaration.const_t()
  def implies_const, do: Declaration.new_const("⊃", type_ooo())

  @doc group: :Constants
  @doc ~S"""
  Constant representing the equivalence operator $\equiv_{o\to o\to o}$.
  """
  @spec equivalent_const() :: Declaration.const_t()
  def equivalent_const, do: Declaration.new_const("≡", type_ooo())

  @doc group: :Constants
  @doc ~S"""
  Constant representing equality $=_{\tau\to\tau\to o}$ over instances of the
  given simple type $\tau$.
  """
  @spec equals_const(Type.t()) :: Declaration.const_t()
  def equals_const(%Type{} = t),
    do: Declaration.new_const("=", Type.new(:o, [t, t]))

  @doc group: :Constants
  @doc ~S"""
  Constant representing the $\forall_{(\tau\to o)\to o}$ operator (universal
  quantification) over the given element type $\tau$.
  """
  @spec forall_const(Type.t()) :: Declaration.const_t()
  def forall_const(%Type{} = t),
    do: Declaration.new_const("∀", Type.new(:o, Type.new(:o, t)))

  @doc group: :Constants
  @doc ~S"""
  Constant representing the $\exists_{(\tau\to o)\to o}$ operator (existential
  quantification) over the given element type $\tau$.
  """
  @spec exists_const(Type.t()) :: Declaration.const_t()
  def exists_const(%Type{} = t),
    do: Declaration.new_const("∃", Type.new(:o, Type.new(:o, t)))

  ##############################################################################
  # TERMS
  ##############################################################################

  @doc group: :Terms
  @doc ~S"""
  Term representing truth $\top_o$.
  """
  @spec true_term() :: Term.term_id()
  def true_term, do: TF.make_const_term("⊤", type_o())

  @doc group: :Terms
  @doc ~S"""
  Term representing falsity $\bot_o$.
  """
  @spec false_term() :: Term.term_id()
  def false_term, do: TF.make_const_term("⊥", type_o())

  @doc group: :Terms
  @doc ~S"""
  Term representing the negation operator $\neg_{o\to o}$.
  """
  @spec neg_term() :: Term.term_id()
  def neg_term, do: TF.make_const_term("¬", type_oo())

  @doc group: :Terms
  @doc ~S"""
  Term representing the disjunction operator $\lor_{o\to o\to o}$.
  """
  @spec or_term() :: Term.term_id()
  def or_term, do: TF.make_const_term("∨", type_ooo())

  @doc group: :Terms
  @doc ~S"""
  Term representing the negated disjunction operator. As it is not part of the
  signature, it is defined as negated disjunction
  $\lambda P Q. \neg (P \lor Q)$.
  """
  def nor_term do
    x = Declaration.new_free_var("X", type_o())
    y = Declaration.new_free_var("Y", type_o())

    disj = or_term() |> TF.make_appl_term!(TF.make_term(x)) |> TF.make_appl_term!(TF.make_term(y))
    neg_term() |> TF.make_appl_term!(disj) |> TF.make_abstr_term!(y) |> TF.make_abstr_term!(x)
  end

  @doc group: :Terms
  @doc ~S"""
  Term representing the conjunction operator $\land_{o\to o\to o}$.
  """
  @spec and_term() :: Term.term_id()
  def and_term, do: TF.make_const_term("∧", type_ooo())

  @doc group: :Terms
  @doc ~S"""
  Term representing the negated conjunction operator. As it is not part of the
  signature, it is represented as negated conjunction
  $\lambda P Q. \neg (P \land Q)$.
  """
  def nand_term do
    x = Declaration.new_free_var("X", type_o())
    y = Declaration.new_free_var("Y", type_o())

    and_term()
    |> TF.make_appl_term!(TF.make_term(x))
    |> TF.make_appl_term!(TF.make_term(y))
    |> then(&TF.make_appl_term!(neg_term(), &1))
    |> TF.make_abstr_term!(y)
    |> TF.make_abstr_term!(x)
  end

  @doc group: :Terms
  @doc ~S"""
  Term representing the implication operator $\supset_{o\to o\to o}$.
  """
  @spec implies_term() :: Term.term_id()
  def implies_term, do: TF.make_const_term("⊃", type_ooo())

  @doc group: :Terms
  @doc ~S"""
  Term representing the converse of the implication operator
  $\subset_{o\to o\to o}$. As it is not part of the signature, it is represented
  as implication with flipped arguments $\lambda P Q. Q \supset P$.
  """
  def implied_by_term do
    x = Declaration.new_free_var("X", type_o())
    y = Declaration.new_free_var("Y", type_o())

    implies_term()
    |> TF.make_appl_term!(TF.make_term(y))
    |> TF.make_appl_term!(TF.make_term(x))
    |> TF.make_abstr_term!(y)
    |> TF.make_abstr_term!(x)
  end

  @doc group: :Terms
  @doc ~S"""
  Term representing the equivalence operator $\equiv_{o\to o\to o}$.
  """
  @spec equivalent_term() :: Term.term_id()
  def equivalent_term, do: TF.make_const_term("≡", type_ooo())

  @doc group: :Terms
  @doc ~S"""
  Term representing the exclusive disjunction operator. As it is no part of the
  signature, it is represented as negated equivalence
  $\lambda P Q.\neg(P \equiv Q)$.
  """
  def xor_term do
    x = Declaration.new_free_var("X", type_o())
    y = Declaration.new_free_var("Y", type_o())

    equivalent_term()
    |> TF.make_appl_term!(TF.make_term(x))
    |> TF.make_appl_term!(TF.make_term(y))
    |> then(&TF.make_appl_term!(neg_term(), &1))
    |> TF.make_abstr_term!(y)
    |> TF.make_abstr_term!(x)
  end

  @doc group: :Terms
  @doc ~S"""
  Term representing the equality operator $=^\tau$ over instances of the given
  type $\tau$.
  """
  @spec equals_term(Type.t()) :: Term.term_id()
  def equals_term(%Type{} = t),
    do: TF.make_const_term("=", Type.new(:o, [t, t]))

  @doc group: :Terms
  @doc ~S"""
  Term representing unequality over instances of the given type $\tau$. As it is
  not part of the signature, it is represented as negated equality
  $\lambda X_\tau Y_\tau. \neg (X =^\tau Y)$.
  """
  @spec not_equals_term(Type.t()) :: Term.term_id()
  def not_equals_term(%Type{} = t) do
    x = Declaration.new_free_var("X", t)
    y = Declaration.new_free_var("Y", t)

    equals_term(t)
    |> TF.make_appl_term!(TF.make_term(x))
    |> TF.make_appl_term!(TF.make_term(y))
    |> then(&TF.make_appl_term!(neg_term(), &1))
    |> TF.make_abstr_term!(y)
    |> TF.make_abstr_term!(x)
  end

  @doc group: :Terms
  @doc ~S"""
  Term representing the $\forall_{(\tau\to o)\to o}$ operator (universal
  quantification) over the given element type $\tau$.
  """
  @spec forall_term(Type.t()) :: Term.term_id()
  def forall_term(%Type{} = t),
    do: TF.make_const_term("∀", Type.new(:o, Type.new(:o, t)))

  @doc group: :Terms
  @doc ~S"""
  Term representing the $\exists_{(\tau\to o)\to o}$ operator (existential
  quantification) over the given element type $\tau$.
  """
  @spec exists_term(Type.t()) :: Term.term_id()
  def exists_term(%Type{} = t),
    do: TF.make_const_term("∃", Type.new(:o, Type.new(:o, t)))

  @doc group: :Equality
  @doc ~S"""
  Constructor for Leibniz equality on the given type, which defines equality by
  stating that both arguments share the same properties. Generates an
  abstraction which can be applied to two arguments.

  $$\mathcal{L}^\tau := \lambda X_\tau Y_\tau.\text{ }\forall(\lambda P_{\tau\to o}.\text{ }P\text{ }X \odot P\text{ }Y)$$

  where $\odot \in \{\supset, \subset, \equiv\}$
  """
  @spec leibniz_equality(Type.t(), :equiv | :imp | :conv_imp) :: Term.term_id()
  def leibniz_equality(type, connective \\ :equiv)

  def leibniz_equality(%Type{} = type, :equiv),
    do: mk_leibniz_equality(type, equivalent_term())

  def leibniz_equality(%Type{} = type, :imp),
    do: mk_leibniz_equality(type, implies_term())

  def leibniz_equality(%Type{} = type, :conv_imp),
    do: mk_leibniz_equality(type, implied_by_term())

  defp mk_leibniz_equality(type, connective) do
    x = Declaration.new_free_var("X", type)
    y = Declaration.new_free_var("Y", type)

    p_type = Type.new(:o, type)
    p = Declaration.new_free_var("P", p_type)
    p_term = TF.make_term(p)

    p_x = TF.make_appl_term!(p_term, TF.make_term(x))
    p_y = TF.make_appl_term!(p_term, TF.make_term(y))

    connective
    |> TF.make_appl_term!(p_x)
    |> TF.make_appl_term!(p_y)
    |> TF.make_abstr_term!(p)
    |> then(&TF.make_appl_term!(forall_term(p_type), &1))
    |> TF.make_abstr_term!(y)
    |> TF.make_abstr_term!(x)
  end

  @doc group: :Equality
  @doc ~S"""
  Constructor for Andrews equality on the given type, which defines equality by
  stating that both arguments share all reflexive relations. Generates an
  abstraction which can be applied to two arguments.

  $$\mathcal{A}^\tau := \lambda X_\tau Y_\tau.\text{ }\forall(\lambda Q_{\tau\to\tau\to o}.\text{ }
  (\forall(\lambda Z_\tau.\text{ }Q\text{ }Z\text{ }Z)) \supset Q\text{ }X\text{ }Y)$$
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
      |> TF.make_appl_term!(z_term)
      |> TF.make_appl_term!(z_term)
      |> TF.make_abstr_term!(z)
      |> then(&TF.make_appl_term!(forall_term(type), &1))

    rhs =
      q_term
      |> TF.make_appl_term!(TF.make_term(x))
      |> TF.make_appl_term!(TF.make_term(y))

    implies_term()
    |> TF.make_appl_term!(lhs)
    |> TF.make_appl_term!(rhs)
    |> TF.make_abstr_term!(q)
    |> then(&TF.make_appl_term!(forall_term(q_type), &1))
    |> TF.make_abstr_term!(y)
    |> TF.make_abstr_term!(x)
  end

  @doc group: :Equality
  @doc ~S"""
  Constructor for extensional equality on the given function type, which
  defines equality by equality of the extensions. Generates an abstraction
  which can be applied to two arguments.

  $$\mathcal{E}^{\alpha\to\beta} := \lambda X_{\alpha\to\beta} Y_{\alpha\to\beta}.\text{ }\forall(\lambda Z_\alpha. X\text{ }Z \doteq^\beta Y\text{ }Z)$$

  for some interpretation of the inner equality relation $\doteq^\beta$.
  """
  def extensional_equality(%Type{args: [at | rest_ats]} = type) do
    x = Declaration.new_free_var("X", type)
    y = Declaration.new_free_var("Y", type)
    z = Declaration.new_free_var("Z", at)
    z_term = TF.make_term(z)

    x_z = TF.make_appl_term!(TF.make_term(x), z_term)
    y_z = TF.make_appl_term!(TF.make_term(y), z_term)

    equals_term(%{type | args: rest_ats})
    |> TF.make_appl_term!(x_z)
    |> TF.make_appl_term!(y_z)
    |> TF.make_abstr_term!(z)
    |> then(&TF.make_appl_term!(forall_term(at), &1))
    |> TF.make_abstr_term!(y)
    |> TF.make_abstr_term!(x)
  end

  def extensional_equality(type) do
    raise ArgumentError,
      message:
        "Type for extensional equality must be a function type. Got #{inspect(type)} instead."
  end
end

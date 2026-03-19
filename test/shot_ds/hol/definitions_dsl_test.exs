defmodule ShotDs.Hol.DefinitionsDslTest do
  use ShotDs.TermFactoryCase

  import ShotDs.Hol.Dsl

  alias ShotDs.Hol.{Definitions}

  test "Definitions exposes canonical Hol helper types" do
    assert Definitions.type_o() == Type.new(:o)
    assert Definitions.type_i() == Type.new(:i)
    assert Definitions.type_oo() == Type.new(:o, :o)
    assert Definitions.type_ooo() == Type.new(:o, [:o, :o])
    assert Definitions.type_iio() == Type.new(:o, [:i, :i])
  end

  test "Definitions creates core constants and terms" do
    assert %Declaration{name: "⊤", kind: :co} = Definitions.true_const()
    assert %Declaration{name: "⊥", kind: :co} = Definitions.false_const()

    assert %Term{head: %Declaration{name: "⊤"}, type: %Type{goal: :o}} =
             Definitions.true_term() |> TF.get_term()

    assert %Term{head: %Declaration{name: "⊥"}, type: %Type{goal: :o}} =
             Definitions.false_term() |> TF.get_term()
  end

  test "Definitions derived connectives are constructed from primitives" do
    rendered_xor = Definitions.xor_term() |> Formatter.format_term()
    rendered_nor = Definitions.nor_term() |> Formatter.format_term()
    rendered_nand = Definitions.nand_term() |> Formatter.format_term()

    assert String.contains?(rendered_xor, "¬")
    assert String.contains?(rendered_xor, "≡")
    assert String.contains?(rendered_nor, "∨")
    assert String.contains?(rendered_nand, "∧")
  end

  test "Dsl boolean operators construct expected heads" do
    a = Definitions.true_term()
    b = Definitions.false_term()

    assert %Term{head: %Declaration{name: "¬"}} = neg(a) |> TF.get_term()
    assert %Term{head: %Declaration{name: "∨"}} = (a ||| b) |> TF.get_term()
    assert %Term{head: %Declaration{name: "∧"}} = (a &&& b) |> TF.get_term()
    assert %Term{head: %Declaration{name: "⊃"}} = a ~> b |> TF.get_term()
    assert %Term{head: %Declaration{name: "≡"}} = a <~> b |> TF.get_term()
  end

  test "Dsl equality helpers infer the left-hand side type" do
    i = Type.new(:i)
    x = TF.make_free_var_term("X", i)
    y = TF.make_free_var_term("Y", i)

    eq_term = eq(x, y)
    neq_term = neq(x, y)

    assert %Term{head: %Declaration{name: "="}, type: %Type{goal: :o}} = TF.get_term(eq_term)
    assert %Term{head: %Declaration{name: "¬"}, type: %Type{goal: :o}} = TF.get_term(neq_term)
  end

  test "Dsl quantifiers support single and multiple variable arities" do
    single = forall(Type.new(:i), fn x -> eq(x, x) end)

    multi =
      exists([Type.new(:i), Type.new(:i)], fn x, y ->
        eq(x, y)
      end)

    assert %Term{type: %Type{goal: :o}} = TF.get_term(single)
    assert %Term{type: %Type{goal: :o}} = TF.get_term(multi)

    assert Formatter.format_term(single) |> String.contains?("Π")
    assert Formatter.format_term(multi) |> String.contains?("Σ")
  end

  test "Definitions.leibniz_equality/2 builds lambda terms with expected connective" do
    i = Type.new(:i)

    eqv = Definitions.leibniz_equality(i)
    imp = Definitions.leibniz_equality(i, :imp)
    conv_imp = Definitions.leibniz_equality(i, :conv_imp)

    assert %Term{type: %Type{goal: :o, args: [%Type{goal: :i}, %Type{goal: :i}]}} =
             TF.get_term(eqv)

    assert %Term{type: %Type{goal: :o, args: [%Type{goal: :i}, %Type{goal: :i}]}} =
             TF.get_term(imp)

    assert %Term{type: %Type{goal: :o, args: [%Type{goal: :i}, %Type{goal: :i}]}} =
             TF.get_term(conv_imp)

    assert Formatter.format_term(eqv) |> String.contains?("≡")
    assert Formatter.format_term(imp) |> String.contains?("⊃")
    assert Formatter.format_term(conv_imp) |> String.contains?("⊃")
  end

  test "Definitions.andrews_equality/1 constructs reflexive equality" do
    i = Type.new(:i)
    andrews_eq = Definitions.andrews_equality(i)

    assert %Term{type: %Type{goal: :o, args: [%Type{goal: :i}, %Type{goal: :i}]}} =
             TF.get_term(andrews_eq)

    # Should contain reflexivity check and implication
    rendered = Formatter.format_term(andrews_eq)
    assert String.contains?(rendered, "Π")
  end

  test "Definitions.extensional_equality/1 constructs function equality" do
    ii = Type.new(:i, :i)
    ext_eq = Definitions.extensional_equality(ii)

    assert %Term{type: %Type{goal: :o, args: [^ii, ^ii]}} = TF.get_term(ext_eq)

    rendered = Formatter.format_term(ext_eq)
    assert String.contains?(rendered, "Π")
    assert String.contains?(rendered, "=")
  end

  test "Definitions.extensional_equality/1 raises for non-function types" do
    assert_raise RuntimeError, ~r/must be a function type/, fn ->
      Definitions.extensional_equality(Type.new(:i))
    end
  end

  test "Definitions exposes all type constructors" do
    assert Definitions.type_ii() == Type.new(:i, :i)
    assert Definitions.type_iii() == Type.new(:i, [:i, :i])
    assert Definitions.type_io() == Type.new(:o, :i)
    assert Definitions.type_io_o() == Type.new(:o, Type.new(:o, :i))
    assert Definitions.type_io_i() == Type.new(:i, Type.new(:o, :i))
    assert Definitions.type_io_io_o() == Type.new(:o, [Type.new(:o, :i), Type.new(:o, :i)])
    assert Definitions.type_io_io_io() == Type.new(:o, [Type.new(:o, :i), Type.new(:o, :i), :i])
  end

  test "Definitions creates all logical operator constants" do
    assert %Declaration{name: "¬"} = Definitions.neg_const()
    assert %Declaration{name: "∨"} = Definitions.or_const()
    assert %Declaration{name: "∧"} = Definitions.and_const()
    assert %Declaration{name: "⊃"} = Definitions.implies_const()
    assert %Declaration{name: "≡"} = Definitions.equivalent_const()
  end

  test "Definitions creates polymorphic constants" do
    i = Type.new(:i)
    assert %Declaration{name: "="} = Definitions.equals_const(i)
    assert %Declaration{name: "Π"} = Definitions.pi_const(i)
    assert %Declaration{name: "Σ"} = Definitions.sigma_const(i)
  end

  test "Definitions creates all logical operator terms" do
    assert %Term{head: %Declaration{name: "¬"}} = Definitions.neg_term() |> TF.get_term()
    assert %Term{head: %Declaration{name: "∨"}} = Definitions.or_term() |> TF.get_term()
    assert %Term{head: %Declaration{name: "∧"}} = Definitions.and_term() |> TF.get_term()
    assert %Term{head: %Declaration{name: "⊃"}} = Definitions.implies_term() |> TF.get_term()
    assert %Term{head: %Declaration{name: "≡"}} = Definitions.equivalent_term() |> TF.get_term()
  end

  test "Definitions creates derived logical terms" do
    rendered_implied = Definitions.implied_by_term() |> Formatter.format_term()
    assert String.contains?(rendered_implied, "⊃")

    rendered_nand = Definitions.nand_term() |> Formatter.format_term()
    assert String.contains?(rendered_nand, "∧")
    assert String.contains?(rendered_nand, "¬")
  end

  test "Definitions creates polymorphic terms" do
    i = Type.new(:i)
    eq_i = Definitions.equals_term(i)
    assert %Term{head: %Declaration{name: "="}} = TF.get_term(eq_i)

    neq_i = Definitions.not_equals_term(i)
    assert %Term{head: %Declaration{name: "¬"}} = TF.get_term(neq_i)

    pi_i = Definitions.pi_term(i)
    assert %Term{head: %Declaration{name: "Π"}} = TF.get_term(pi_i)

    sigma_i = Definitions.sigma_term(i)
    assert %Term{head: %Declaration{name: "Σ"}} = TF.get_term(sigma_i)
  end

  test "Dsl expr operators work with variables" do
    o = Type.new(:o)
    x = TF.make_free_var_term("X", o)

    assert %Term{type: %Type{goal: :o}} = neg(x) |> TF.get_term()
  end

  test "Dsl forall with multiple variables creates nested quantifiers" do
    multi = forall([Type.new(:i), Type.new(:i)], fn x, y -> eq(x, y) end)

    term = TF.get_term(multi)
    assert %Term{type: %Type{goal: :o}} = term

    # Check that it has multiple binders
    rendered = Formatter.format_term(multi)
    assert String.contains?(rendered, "Π")
  end

  test "String.Chars protocol for Term works" do
    i = Type.new(:i)
    x = TF.make_free_var_term("X", i)

    str = to_string(TF.get_term(x))
    assert is_binary(str)
    assert String.contains?(str, "X")
  end

  test "String.Chars protocol for lambda terms" do
    lambda_id = lambda(Type.new(:i), fn x -> x end)

    str = to_string(TF.get_term(lambda_id))
    assert is_binary(str)
    assert String.contains?(str, "λ")
  end

  test "String.Chars protocol for application terms" do
    f = TF.make_const_term("f", Type.new(:o, :i))
    x = TF.make_const_term("a", Type.new(:i))
    app = TF.make_appl_term(f, x)

    str = to_string(TF.get_term(app))
    assert is_binary(str)
    assert String.contains?(str, "f")
  end
end

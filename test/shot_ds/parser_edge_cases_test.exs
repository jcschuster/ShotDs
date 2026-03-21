defmodule ShotDs.ParserEdgeCasesTest do
  use ShotDs.TermFactoryCase

  alias ShotDs.Parser
  alias ShotDs.Data.Context

  test "parse/1 handles deeply nested applications" do
    term_id = Parser.parse("$true & $false | $true => $false <=> $true")

    assert %Term{type: %Type{goal: :o}} = TF.get_term(term_id)
  end

  test "parse/1 handles untyped variable shadowing" do
    ctx = Context.new() |> Context.put_var("X", Type.new(:i))

    # Lambda with different binding for X
    term_id = Parser.parse("^[X:$o]: X", ctx)

    assert %Term{type: %Type{goal: :o}} = TF.get_term(term_id)
  end

  test "parse/1 handles constants as bareword atoms" do
    term1 = Parser.parse("hello")
    term2 = Parser.parse("world_123")

    assert %Term{head: %Declaration{name: "hello"}} = TF.get_term(term1)
    assert %Term{head: %Declaration{name: "world_123"}} = TF.get_term(term2)
  end

  test "parse/1 complex precedence with all operators" do
    # Tests full precedence chain: ! > ^ > => > | > & > ~ > =
    formula = "![X]: X = X & $true => $false | ~$true"
    term_id = Parser.parse(formula)

    assert %Term{type: %Type{goal: :o}} = TF.get_term(term_id)
  end

  test "parse_type/1 with top-level parentheses" do
    t1 = Parser.parse_type("($i>$o)")
    t2 = Parser.parse_type("$i>$o")

    assert t1 == t2
  end

  test "parse_type/1 deeply nested parentheses" do
    complex = Parser.parse_type("(($i>($o))>$o)")

    # Should parse successfully despite nesting
    assert %Type{goal: :o} = complex
  end

  test "parse/1 quantified variable in complex context" do
    term_id = Parser.parse("![X:$i, Y:$i]: X = Y & $true => X = Y")

    assert %Term{type: %Type{goal: :o}} = TF.get_term(term_id)
  end

  test "parse/1 lambda inside quantifier" do
    term_id =
      Parser.parse("![P:$i>$o]: P @ c", Context.new() |> Context.put_const("c", Type.new(:i)))

    assert %Term{type: %Type{goal: :o}} = TF.get_term(term_id)
  end

  test "parse/1 application with multiple arguments chained" do
    ctx =
      Context.new()
      |> Context.put_const("f", Type.new(:i, [:o, :i, :o]))
      |> Context.put_const("a", Type.new(:o))
      |> Context.put_const("b", Type.new(:i))
      |> Context.put_const("c", Type.new(:o))

    term_id = Parser.parse("f @ a @ b @ c", ctx)

    assert %Term{type: %Type{goal: :i}} = TF.get_term(term_id)
  end

  test "parse/1 lambda with type annotation" do
    term_id = Parser.parse("^[X:$i, Y:$o]: X = X")

    assert %Term{bvars: [_, _]} = TF.get_term(term_id)
  end

  test "parse/1 polymorphic constants resolve types correctly" do
    ctx =
      Context.new()
      |> Context.put_const("x", Type.new(:i))
      |> Context.put_const("y", Type.new(:i))

    term_id = Parser.parse("x = y", ctx)

    assert %Term{head: %Declaration{name: "="}} = TF.get_term(term_id)
  end

  test "parse/1 derived connectives all work" do
    implied_by = Parser.parse("$true <= $false")
    xor = Parser.parse("$true <~> $false")
    nor = Parser.parse("$true ~| $false")
    nand = Parser.parse("$true ~& $false")

    assert %Term{head: %Declaration{name: "⊃"}} = TF.get_term(implied_by)
    assert Formatter.format_term(xor) |> String.contains?("¬")
    assert Formatter.format_term(nor) |> String.contains?("¬")
    assert Formatter.format_term(nand) |> String.contains?("¬")
  end

  test "parse/1 parentheses in lambda body" do
    term_id = Parser.parse("^[X:$i]: (X)")

    assert %Term{type: %Type{goal: :i, args: [_]}} = TF.get_term(term_id)
  end

  test "parse_tokens/1 with explicit context" do
    {:ok, tokens, "", _, _, _} = Lexer.tokenize("f @ a")

    ctx =
      Context.new()
      |> Context.put_const("f", Type.new(:i, :o))
      |> Context.put_const("a", Type.new(:o))

    term_id = Parser.parse_tokens(tokens, ctx)

    assert %Term{type: %Type{goal: :i}} = TF.get_term(term_id)
  end

  test "parse/1 unary negation stacking" do
    term_id = Parser.parse("~ ~ ~ $true")

    assert %Term{type: %Type{goal: :o}} = TF.get_term(term_id)
  end

  test "parse/2 respects context const/var distinction" do
    ctx =
      Context.new()
      |> Context.put_const("c", Type.new(:i))
      |> Context.put_var("V", Type.new(:i))

    c_term = Parser.parse("c", ctx)
    v_term = Parser.parse("V", ctx)

    assert %Term{head: %Declaration{kind: :co}} = TF.get_term(c_term)
    assert %Term{head: %Declaration{kind: :fv}} = TF.get_term(v_term)
  end

  test "parse/1 variable capitalization follows HOL conventions" do
    # Uppercase should be variable
    upper = Parser.parse("X")
    # Lowercase should be constant
    lower = Parser.parse("x")

    assert %Term{head: %Declaration{kind: :fv}} = TF.get_term(upper)
    assert %Term{head: %Declaration{kind: :co}} = TF.get_term(lower)
  end

  test "parse_type_tokens/1 with function types" do
    {:ok, tokens, "", _, _, _} = Lexer.tokenize("$i > $o > $i")
    {type, []} = Parser.parse_type_tokens(tokens)

    # Type parsing normalizes args to a flattened list
    assert %Type{goal: :i, args: [%Type{goal: :i}, %Type{goal: :o}]} = type
  end

  test "parse_type_tokens/1 with single arrow" do
    {:ok, tokens, "", _, _, _} = Lexer.tokenize("$i > $o")
    {type, []} = Parser.parse_type_tokens(tokens)

    assert %Type{goal: :o, args: [%Type{goal: :i}]} = type
  end
end

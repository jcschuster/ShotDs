defmodule ShotDs.ParserEdgeCasesTest do
  use ShotDs.TermFactoryCase

  alias ShotDs.Parser
  alias ShotDs.Data.Context

  test "parse/1 handles deeply nested applications" do
    term_id = Parser.parse("$true & $false | $true => $false <=> $true") |> ok!()

    assert %Term{type: %Type{goal: :o}} = term!(term_id)
  end

  test "parse/1 handles untyped variable shadowing" do
    ctx = Context.new() |> Context.put_var("X", Type.new(:i))

    # Lambda with different binding for X
    term_id = Parser.parse("^[X:$o]: X", ctx) |> ok!()

    assert %Term{type: %Type{goal: :o}} = term!(term_id)
  end

  test "parse/1 handles constants as bareword atoms" do
    term1 = Parser.parse("hello") |> ok!()
    term2 = Parser.parse("world_123") |> ok!()

    assert %Term{head: %Declaration{name: "hello"}} = term!(term1)
    assert %Term{head: %Declaration{name: "world_123"}} = term!(term2)
  end

  test "parse/1 complex precedence with all operators" do
    # Tests full precedence chain: ! > ^ > => > | > & > ~ > =
    formula = "![X]: X = X & $true => $false | ~$true"
    term_id = Parser.parse(formula) |> ok!()

    assert %Term{type: %Type{goal: :o}} = term!(term_id)
  end

  test "parse_type!/1 with top-level parentheses" do
    t1 = Parser.parse_type!("($i>$o)")
    t2 = Parser.parse_type!("$i>$o")

    assert t1 == t2
  end

  test "parse_type!/1 deeply nested parentheses" do
    complex = Parser.parse_type!("(($i>($o))>$o)")

    # Should parse successfully despite nesting
    assert %Type{goal: :o} = complex
  end

  test "parse/1 quantified variable in complex context" do
    term_id = Parser.parse("![X:$i, Y:$i]: X = Y & $true => X = Y") |> ok!()

    assert %Term{type: %Type{goal: :o}} = term!(term_id)
  end

  test "parse/1 lambda inside quantifier" do
    term_id =
      Parser.parse("![P:$i>$o]: P @ c", Context.new() |> Context.put_const("c", Type.new(:i)))
      |> ok!()

    assert %Term{type: %Type{goal: :o}} = term!(term_id)
  end

  test "parse/1 application with multiple arguments chained" do
    ctx =
      Context.new()
      |> Context.put_const("f", Type.new(:i, [:o, :i, :o]))
      |> Context.put_const("a", Type.new(:o))
      |> Context.put_const("b", Type.new(:i))
      |> Context.put_const("c", Type.new(:o))

    term_id = Parser.parse("f @ a @ b @ c", ctx) |> ok!()

    assert %Term{type: %Type{goal: :i}} = term!(term_id)
  end

  test "parse/1 lambda with type annotation" do
    term_id = Parser.parse("^[X:$i, Y:$o]: X = X") |> ok!()

    assert %Term{bvars: [_, _]} = term!(term_id)
  end

  test "parse/1 polymorphic constants resolve types correctly" do
    ctx =
      Context.new()
      |> Context.put_const("x", Type.new(:i))
      |> Context.put_const("y", Type.new(:i))

    term_id = Parser.parse("x = y", ctx) |> ok!()

    assert %Term{head: %Declaration{name: "="}} = term!(term_id)
  end

  test "parse/1 derived connectives all work" do
    implied_by = Parser.parse("$true <= $false") |> ok!()
    xor = Parser.parse("$true <~> $false") |> ok!()
    nor = Parser.parse("$true ~| $false") |> ok!()
    nand = Parser.parse("$true ~& $false") |> ok!()

    assert %Term{head: %Declaration{name: "⊃"}} = term!(implied_by)
    assert Formatter.format_term!(xor) |> String.contains?("¬")
    assert Formatter.format_term!(nor) |> String.contains?("¬")
    assert Formatter.format_term!(nand) |> String.contains?("¬")
  end

  test "parse/1 parentheses in lambda body" do
    term_id = Parser.parse("^[X:$i]: (X)") |> ok!()

    assert %Term{type: %Type{goal: :i, args: [_]}} = term!(term_id)
  end

  test "parse_tokens/1 with explicit context" do
    {:ok, tokens, "", _, _, _} = Lexer.tokenize("f @ a")

    ctx =
      Context.new()
      |> Context.put_const("f", Type.new(:i, :o))
      |> Context.put_const("a", Type.new(:o))

    term_id = Parser.parse_tokens(tokens, ctx) |> ok!()

    assert %Term{type: %Type{goal: :i}} = term!(term_id)
  end

  test "parse/1 unary negation stacking" do
    term_id = Parser.parse("~ ~ ~ $true") |> ok!()

    assert %Term{type: %Type{goal: :o}} = term!(term_id)
  end

  test "parse/2 respects context const/var distinction" do
    ctx =
      Context.new()
      |> Context.put_const("c", Type.new(:i))
      |> Context.put_var("V", Type.new(:i))

    c_term = Parser.parse("c", ctx) |> ok!()
    v_term = Parser.parse("V", ctx) |> ok!()

    assert %Term{head: %Declaration{kind: :co}} = term!(c_term)
    assert %Term{head: %Declaration{kind: :fv}} = term!(v_term)
  end

  test "parse/1 variable capitalization follows HOL conventions" do
    # Uppercase should be variable
    upper = Parser.parse("X") |> ok!()
    # Lowercase should be constant
    lower = Parser.parse("x") |> ok!()

    assert %Term{head: %Declaration{kind: :fv}} = term!(upper)
    assert %Term{head: %Declaration{kind: :co}} = term!(lower)
  end

  test "parse_type_tokens/1 with function types" do
    {:ok, tokens, "", _, _, _} = Lexer.tokenize("$i > $o > $i")
    {:ok, {type, []}} = Parser.parse_type_tokens(tokens)

    # Type parsing normalizes args to a flattened list
    assert %Type{goal: :i, args: [%Type{goal: :i}, %Type{goal: :o}]} = type
  end

  test "parse_type_tokens/1 with single arrow" do
    {:ok, tokens, "", _, _, _} = Lexer.tokenize("$i > $o")
    {:ok, {type, []}} = Parser.parse_type_tokens(tokens)

    assert %Type{goal: :o, args: [%Type{goal: :i}]} = type
  end
end

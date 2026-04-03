defmodule ShotDs.ParserTest do
  use ShotDs.TermFactoryCase

  alias ShotDs.Parser

  test "parse_type/1 parses right-associative function types" do
    assert Parser.parse_type("$o>$i>$o") == Type.new(:o, [:o, :i])
    assert to_string(Parser.parse_type("$o>$i>$o")) == "o>i>o"
  end

  test "parse_type_tokens/1 parses parenthesized type expressions" do
    {:ok, tokens, "", _, _, _} = Lexer.tokenize("($i>$o)>$o")
    {type, []} = Parser.parse_type_tokens(tokens)

    assert to_string(type) == "(i>o)>o"
  end

  test "parse/2 uses context types for constants and variables" do
    ctx =
      Context.new()
      |> Context.put_const("f", Type.new(:o, :i))
      |> Context.put_var("X", Type.new(:i))

    term_id = Parser.parse("f @ X", ctx) |> ok!()

    assert %Term{head: %Declaration{kind: :co, name: "f"}, type: %Type{goal: :o}} =
             term!(term_id)
  end

  test "parse/1 respects precedence between negation and conjunction" do
    term_id = Parser.parse("~ $true & $false") |> ok!()
    %Term{head: %Declaration{name: "∧"}, args: [lhs_id, _rhs_id]} = term!(term_id)

    lhs = term!(lhs_id)
    assert %Declaration{name: "¬"} = lhs.head
  end

  test "parse/1 builds quantified terms with inferred variable types" do
    term_id = Parser.parse("![X]: X = X") |> ok!()

    assert %Term{type: %Type{goal: :o, args: []}} = term!(term_id)
    assert Formatter.format_term!(term_id) |> String.contains?("Π")
  end

  test "parse/1 expands derived connective xor into negated equivalence" do
    term_id = Parser.parse("$true <~> $false") |> ok!()

    assert Formatter.format_term!(term_id) |> String.contains?("¬")
    assert Formatter.format_term!(term_id) |> String.contains?("≡")
  end

  test "parse_tokens/2 parses token lists produced by the lexer" do
    {:ok, tokens, "", _, _, _} = Lexer.tokenize("a")

    term_id = Parser.parse_tokens(tokens) |> ok!()

    assert %Term{head: %Declaration{name: "a"}} = term!(term_id)
  end

  test "parse_tokens/2 returns an error for invalid starts" do
    assert {:error, message} = Parser.parse_tokens([{:rparen, ")"}], Context.new())
    assert message =~ "Syntax Error"
  end

  test "parse/2 returns type errors when constraints are inconsistent" do
    ctx =
      Context.new()
      |> Context.put_const("f", Type.new(:o, :i))
      |> Context.put_const("p", Type.new(:o))

    assert {:error, message} = Parser.parse("f @ p", ctx)
    assert message =~ "Type Error"
  end

  test "parse/1 handles bare nullary connectives" do
    assert %Term{head: %Declaration{name: "⊤"}} = Parser.parse("$true") |> ok!() |> term!()
    assert %Term{head: %Declaration{name: "⊥"}} = Parser.parse("$false") |> ok!() |> term!()
  end

  test "parse/2 with all quantifier styles (forall/pi/exists/sigma)" do
    single_forall = Parser.parse("![X]:X=X") |> ok!()
    single_pi = Parser.parse("!![X]:X=X") |> ok!()
    single_exists = Parser.parse("?[X]:X=X") |> ok!()
    single_sigma = Parser.parse("??[X]:X=X") |> ok!()

    assert %Term{type: %Type{goal: :o}} = term!(single_forall)
    assert %Term{type: %Type{goal: :o}} = term!(single_pi)
    assert %Term{type: %Type{goal: :o}} = term!(single_exists)
    assert %Term{type: %Type{goal: :o}} = term!(single_sigma)
  end

  test "parse/1 handles all binary connectives" do
    assert %Term{head: %Declaration{name: "∧"}} =
             Parser.parse("$true & $false") |> ok!() |> term!()

    assert %Term{head: %Declaration{name: "∨"}} =
             Parser.parse("$true | $false") |> ok!() |> term!()

    assert %Term{head: %Declaration{name: "⊃"}} =
             Parser.parse("$true => $false") |> ok!() |> term!()

    assert %Term{head: %Declaration{name: "≡"}} =
             Parser.parse("$true <=> $false") |> ok!() |> term!()
  end

  test "parse/1 handles equality and inequality" do
    eq_parsed =
      Parser.parse(
        "a = b",
        Context.new()
        |> Context.put_const("a", Type.new(:i))
        |> Context.put_const("b", Type.new(:i))
      )
      |> ok!()

    neq_parsed =
      Parser.parse(
        "a != b",
        Context.new()
        |> Context.put_const("a", Type.new(:i))
        |> Context.put_const("b", Type.new(:i))
      )
      |> ok!()

    assert %Term{head: %Declaration{name: "="}} = term!(eq_parsed)
    assert %Term{head: %Declaration{name: "¬"}} = term!(neq_parsed)
  end

  test "parse/1 handles NOR and NAND derived connectives" do
    nor = Parser.parse("$true ~| $false") |> ok!()
    nand = Parser.parse("$true ~& $false") |> ok!()

    assert Formatter.format_term!(nor) |> String.contains?("¬")
    assert Formatter.format_term!(nor) |> String.contains?("∨")
    assert Formatter.format_term!(nand) |> String.contains?("¬")
    assert Formatter.format_term!(nand) |> String.contains?("∧")
  end

  test "parse/1 handles converse implication" do
    term_id = Parser.parse("$true <= $false") |> ok!()

    # Should be implication with flipped arguments
    term = term!(term_id)
    assert %Term{head: %Declaration{name: "⊃"}} = term
  end

  test "parse/1 respects operator precedence with all levels" do
    # Negation > conjunction > disjunction > implication
    term_id = Parser.parse("~ $true & $false | $true => $false") |> ok!()

    assert %Term{type: %Type{goal: :o}} = term!(term_id)
  end

  test "parse/1 handles parenthesized expressions" do
    paren = Parser.parse("($true)") |> ok!()
    no_paren = Parser.parse("$true") |> ok!()

    assert paren == no_paren
  end

  test "parse/1 handles complex lambda expressions" do
    ctx = Context.new() |> Context.put_const("a", Type.new(:i))
    lambda = Parser.parse("^ [X:$i, Y:$i]: a", ctx) |> ok!()

    assert %Term{bvars: [_, _]} = term!(lambda)
  end

  test "parse_type/1 handles complex nested function types" do
    complex = Parser.parse_type("($i>$i)>$o")

    assert %Type{goal: :o, args: [%Type{goal: :i, args: [%Type{goal: :i}]}]} = complex
  end

  test "parse/1 handles multiple quantified variables" do
    term_id = Parser.parse("![X:$i, Y:$i, Z:$i]: X = Y") |> ok!()

    assert %Term{type: %Type{goal: :o}} = term!(term_id)
  end

  test "parse/1 infers types from context through application chain" do
    ctx =
      Context.new()
      |> Context.put_const("f", Type.new(:i, [:i, :i]))
      |> Context.put_const("a", Type.new(:i))
      |> Context.put_const("b", Type.new(:i))

    term_id = Parser.parse("f @ a @ b", ctx) |> ok!()

    assert %Term{type: %Type{goal: :i}} = term!(term_id)
  end
end

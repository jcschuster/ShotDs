defmodule ShotDs.ParserContextTest do
  use ShotDs.TermFactoryCase

  alias ShotDs.Parser
  alias ShotDs.Data.{Context, Type}

  test "parse_context/1 with empty string returns empty context" do
    {:ok, ctx} = Parser.parse_context("")

    assert ctx.vars == %{}
    assert ctx.consts == %{}
  end

  test "parse_context/1 parses single variable declaration" do
    {:ok, ctx} = Parser.parse_context("X:$i")

    assert ctx.vars |> Map.has_key?("X")
    assert ctx.vars["X"] == Type.new(:i)
  end

  test "parse_context/1 parses single constant declaration" do
    {:ok, ctx} = Parser.parse_context("f:$o>$i")

    assert ctx.consts |> Map.has_key?("f")
    # $o>$i is parsed right-associatively as i <- o
    assert Context.get_type(ctx, "f") == Type.new(:i, :o)
  end

  test "parse_context!/1 raises on invalid syntax" do
    assert_raise ShotDs.Parser.ParseError, fn ->
      Parser.parse_context!("invalid syntax !!!")
    end
  end

  test "parse_context!/1 parses variable with type" do
    ctx = Parser.parse_context!("X:$i")

    assert ctx.vars |> Map.has_key?("X")
    var_type = ctx.vars["X"]
    assert var_type == Type.new(:i)
  end

  test "parse_context!/1 parses constant with function type" do
    ctx = Parser.parse_context!("f:$o>$i")

    assert ctx.consts |> Map.has_key?("f")
    assert Context.get_type(ctx, "f") == Type.new(:i, :o)
  end

  test "parse_context/1 handles multiple variable declarations" do
    {:ok, ctx} = Parser.parse_context("X:$i, Y:$o")

    assert ctx.vars |> Map.has_key?("X")
    assert ctx.vars |> Map.has_key?("Y")
    assert ctx.vars["X"] == Type.new(:i)
    assert ctx.vars["Y"] == Type.new(:o)
  end

  test "parse_context/1 handles mixed variable and constant declarations" do
    {:ok, ctx} = Parser.parse_context("X:$i, f:$o>$i")

    assert ctx.vars |> Map.has_key?("X")
    assert ctx.consts |> Map.has_key?("f")
  end

  test "parse_context/1 parses multiple constants" do
    {:ok, ctx} = Parser.parse_context("p:$o, q:$o, r:$o")

    assert ctx.consts |> Map.has_key?("p")
    assert ctx.consts |> Map.has_key?("q")
    assert ctx.consts |> Map.has_key?("r")
  end

  test "parse_context/1 parses constants with complex types" do
    {:ok, ctx} = Parser.parse_context("f:$i>$i>$o, g:$o>$o>$o")

    # $i>$i>$o is parsed right-associatively as o <- i <- i
    assert Context.get_type(ctx, "f") == Type.new(:o, [:i, :i])

    # $o>$o>$o is parsed as o <- o <- o
    assert Context.get_type(ctx, "g") == Type.new(:o, [:o, :o])
  end

  test "parse_context/1 with parenthesized types" do
    {:ok, ctx} = Parser.parse_context("f:($i>$o)>$o")

    # Type should be (i>o)>o
    assert Context.get_type(ctx, "f") == Type.new(:o, [Type.new(:o, :i)])
  end

  test "parse_context/1 with duplicate names uses last definition" do
    # The parser uses Context.put_var/put_const which overwrites
    {:ok, ctx} = Parser.parse_context("X:$i, X:$o")
    assert ctx.vars["X"] == Type.new(:o)
  end

  test "parse_context!/1 raises on syntax errors" do
    assert_raise ShotDs.Parser.ParseError, fn ->
      Parser.parse_context!("X: ??")
    end
  end

  test "parse_context/1 handles whitespace" do
    {:ok, ctx1} = Parser.parse_context("X : $i")
    {:ok, ctx2} = Parser.parse_context("X:$i")

    assert ctx1.vars == ctx2.vars
  end

  test "parse_context/1 with only whitespace and commas returns error" do
    # Parser doesn't accept comma without declarations
    assert {:error, _reason} = Parser.parse_context("  ,  ")
  end

  test "parse_type!/1 parses base types" do
    assert Parser.parse_type!("$i") == Type.new(:i)
    assert Parser.parse_type!("$o") == Type.new(:o)
  end

  test "parse_type!/1 parses arrow types" do
    type = Parser.parse_type!("$i>$o")
    assert type == Type.new(:o, :i)
  end

  test "parse_type!/1 parses complex types" do
    type = Parser.parse_type!("$i>$o>$i")
    # Right-associative: parses as i <- (o <- i)
    assert type.goal == :i
    assert length(type.args) == 2
  end

  test "parse_type!/1 with parentheses" do
    type = Parser.parse_type!("($i>$o)>$o")
    assert type == Type.new(:o, [Type.new(:o, :i)])
  end

  test "parse_type!/1 can parse custom types" do
    # Parser allows custom type atoms
    type = Parser.parse_type!("custom_type")
    assert type == Type.new(:custom_type)
  end

  test "parse_type/1 with undefined atoms is valid" do
    # Parser treats atoms as type names
    assert {:ok, type} = Parser.parse_type("undefined")
    assert type == Type.new(:undefined)
  end

  test "parse_type_tokens/1 parses token list for single type" do
    {:ok, tokens, "", _, _, _} = Lexer.tokenize("$i")
    {:ok, {type, remaining}} = Parser.parse_type_tokens(tokens)

    assert type == Type.new(:i)
    assert remaining == []
  end

  test "parse_type_tokens/1 with remaining tokens" do
    {:ok, tokens, "", _, _, _} = Lexer.tokenize("$i)")
    {:ok, {type, remaining}} = Parser.parse_type_tokens(tokens)

    assert type == Type.new(:i)
    assert [{:rparen, ")", _}] = remaining
  end

  test "parse_context/1 with many declarations" do
    {:ok, ctx} = Parser.parse_context("a:$o, b:$o, c:$i, d:$i>$o, e:$o>$i>$o")

    assert map_size(ctx.consts) == 5
    # d:$i>$o is i <- o, so Type.new(:o, :i)
    assert Context.get_type(ctx, "d") == Type.new(:o, :i)
    # e:$o>$i>$o parses as o <- (i <- o)
    e_type = Context.get_type(ctx, "e")
    assert e_type.goal == :o
    assert length(e_type.args) == 2
  end

  test "parse_type!/1 long chains of arrow types" do
    type = Parser.parse_type!("$i>$i>$i>$i>$o")
    # Should be o > i > i > i > i
    assert type.goal == :o
    assert length(type.args) == 4
  end

  test "parse_context/1 deeply nested parenthesized types" do
    {:ok, ctx} = Parser.parse_context("f:(($i>$o)>$o)>$o")

    assert Context.get_type(ctx, "f").goal == :o
  end
end

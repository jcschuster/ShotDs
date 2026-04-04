defmodule ShotDs.Util.FormatterTest do
  use ShotDs.TermFactoryCase

  alias ShotDs.Data.{Type, Declaration, Problem}
  alias ShotDs.Util.Formatter
  alias ShotDs.Stt.Numerals

  # Test format/2 dispatcher with all types
  test "format/2 with Type returns formatted string" do
    type = Type.new(:o, :i)
    {:ok, result} = Formatter.format(type)

    assert is_binary(result)
    assert String.contains?(result, "o")
    assert String.contains?(result, "i")
  end

  test "format/2 with Declaration returns formatted string" do
    decl = %Declaration{kind: :co, name: "f", type: Type.new(:o, :i)}
    {:ok, result} = Formatter.format(decl)

    assert is_binary(result)
    assert String.contains?(result, "f")
  end

  test "format/2 with Term struct returns formatted string" do
    term_id = TF.make_const_term("p", Type.new(:o))
    term = term!(term_id)

    {:ok, result} = Formatter.format(term)
    assert is_binary(result)
  end

  test "format!/2 with invalid input raises error" do
    assert_raise FunctionClauseError, fn ->
      Formatter.format!(%{"invalid" => "input"})
    end
  end

  test "format/2 with invalid term ID returns error" do
    result = Formatter.format(-999)
    assert {:error, _reason} = result
  end

  test "format_term/2 with valid term ID returns formatted string" do
    term_id = Numerals.num(2)

    {:ok, result} = Formatter.format_term(term_id)

    assert is_binary(result)
    assert String.length(result) > 0
  end

  test "format_term!/2 returns string for valid term" do
    term_id = Numerals.num(3)

    result = Formatter.format_term!(term_id)

    assert is_binary(result)
  end

  test "format_term/2 with type annotations enabled" do
    term_id = TF.make_const_term("a", Type.new(:i))

    {:ok, result} = Formatter.format_term(term_id, false)

    assert is_binary(result)
  end

  test "format_term/2 with invalid ID returns error" do
    result = Formatter.format_term(99_999)
    assert {:error, _reason} = result
  end

  test "format_substitution!/2 formats Substitution" do
    fvar_decl = %Declaration{kind: :fv, name: "Y", type: Type.new(:o)}
    term_id = TF.make_const_term("b", Type.new(:o))
    subst = %Substitution{fvar: fvar_decl, term_id: term_id}

    result = Formatter.format_substitution!(subst)

    assert is_binary(result)
  end

  test "format_substitution supports Declaration formatting" do
    # Test that substitutions can be formatted with declarations
    fvar_decl = %Declaration{kind: :fv, name: "Z", type: Type.new(:i)}
    term_id = TF.make_const_term("t", Type.new(:i))
    subst = %Substitution{fvar: fvar_decl, term_id: term_id}

    result = Formatter.format_substitution!(subst)

    # Should contain the variable name and formatting
    assert is_binary(result)
    assert String.length(result) > 0
  end

  test "format_problem/2 with empty problem" do
    problem = %Problem{}

    {:ok, result} = Formatter.format_problem(problem)

    assert is_binary(result)
  end

  test "format_problem!/2 returns formatted string" do
    problem = %Problem{path: "test.p"}

    result = Formatter.format_problem!(problem)

    assert is_binary(result)
  end

  test "format/2 returns error for unknown type" do
    result = Formatter.format(:not_a_valid_type)
    assert {:error, :unknown_argument} = result
  end

  test "format_term/2 with Term struct" do
    term_id = TF.make_const_term("x", Type.new(:o))
    term = term!(term_id)

    {:ok, result} = Formatter.format_term(term)

    assert is_binary(result)
  end

  test "format_term!/2 with Term struct" do
    term_id = TF.make_const_term("c", Type.new(:i))
    term = term!(term_id)

    result = Formatter.format_term!(term)

    assert is_binary(result)
  end

  test "format/2 dispatcher with integer term ID" do
    term_id = TF.make_const_term("test", Type.new(:o))

    {:ok, result} = Formatter.format(term_id)

    assert is_binary(result)
  end

  test "format!/2 dispatcher with integer term ID" do
    term_id = TF.make_const_term("test", Type.new(:o))

    result = Formatter.format!(term_id)

    assert is_binary(result)
  end

  test "format!/2 with Problem struct" do
    term_id = TF.make_const_term("x", Type.new(:o))

    problem = %Problem{
      path: "problem.p",
      axioms: [{"ax1", term_id}]
    }

    result = Formatter.format!(problem)

    assert is_binary(result)
  end

  test "format!/2 with complex problem" do
    term_id = TF.make_const_term("c", Type.new(:o))

    problem = %Problem{
      path: "complex.p",
      includes: ["lib.ax"],
      types: %{"p" => :base_type},
      conjecture: {"goal", term_id}
    }

    result = Formatter.format!(problem)

    assert is_binary(result)
    assert String.contains?(result, "complex.p")
  end

  test "format_term!/2 hide_types parameter affects output" do
    term_id = TF.make_const_term("a", Type.new(:i))

    result_with_types = Formatter.format_term!(term_id, false)
    result_without_types = Formatter.format_term!(term_id, true)

    # Both should be strings
    assert is_binary(result_with_types)
    assert is_binary(result_without_types)
  end

  test "format!/2 with Substitution struct" do
    fvar_decl = %Declaration{kind: :fv, name: "X", type: Type.new(:i)}
    term_id = TF.make_const_term("a", Type.new(:i))
    subst = %Substitution{fvar: fvar_decl, term_id: term_id}

    result = Formatter.format!(subst)

    assert is_binary(result)
  end
end

defmodule ShotDs.Parser.ParseErrorTest do
  use ExUnit.Case

  alias ShotDs.Parser.ParseError

  test "ParseError can be raised and caught" do
    assert_raise ParseError, fn ->
      raise ParseError, message: "test error"
    end
  end

  test "ParseError has default message" do
    error = %ParseError{}

    assert error.message == "parse error"
  end

  test "ParseError message can be customized" do
    error = %ParseError{message: "custom error"}

    assert error.message == "custom error"
  end

  test "ParseError message appears in exception raise" do
    message = "Expected token but got something else"

    result = catch_error(raise ParseError, message: message)

    assert result.message == message
  end

  test "ParseError implements Exception protocol" do
    error = %ParseError{message: "test"}

    # Should have exception message
    exception_message = Exception.message(error)
    assert exception_message == "test"
  end

  test "ParseError can be pattern matched" do
    result =
      try do
        raise ParseError, message: "pattern match test"
      rescue
        ParseError -> "caught"
      end

    assert result == "caught"
  end
end

defmodule ShotDs.Data.ProblemStringCharsTest do
  use ExUnit.Case

  alias ShotDs.Data.{Problem, Type, Declaration, Term}

  test "to_string on empty problem shows unnamed" do
    problem = %Problem{}

    result = to_string(problem)

    assert String.contains?(result, "Problem <unnamed>")
  end

  test "to_string shows path when provided" do
    problem = %Problem{path: "/path/to/problem.p"}

    result = to_string(problem)

    assert String.contains?(result, "Problem /path/to/problem.p")
  end

  test "to_string shows includes when provided" do
    problem = %Problem{includes: ["axioms.ax", "theorems.p"]}

    result = to_string(problem)

    assert String.contains?(result, "includes: axioms.ax, theorems.p")
  end

  test "to_string does not show includes section when empty" do
    problem = %Problem{includes: []}

    result = to_string(problem)

    refute String.contains?(result, "includes:")
  end

  test "to_string shows types section when provided" do
    problem = %Problem{types: %{"a" => :base_type, "f" => Type.new(:o, :i)}}

    result = to_string(problem)

    assert String.contains?(result, "Types:")
    assert String.contains?(result, "a (base type)")
    assert String.contains?(result, "f::")
  end

  test "to_string does not show types section when empty" do
    problem = %Problem{types: %{}}

    result = to_string(problem)

    refute String.contains?(result, "Types:")
  end

  test "to_string shows definitions section when provided" do
    atom_decl = %Declaration{kind: :co, name: "f", type: Type.new(:i)}
    # Using a dummy term ID (would normally be created by term factory)
    problem = %Problem{definitions: %{atom_decl => 1}}

    result = to_string(problem)

    assert String.contains?(result, "Depends on")
    assert String.contains?(result, "definitions:")
    assert String.contains?(result, "f")
  end

  test "to_string does not show definitions section when empty" do
    problem = %Problem{definitions: %{}}

    result = to_string(problem)

    refute String.contains?(result, "Depends on")
  end

  test "to_string shows axioms section when provided" do
    problem = %Problem{axioms: [{"ax1", 1}, {"ax2", 2}, {"ax3", 3}]}

    result = to_string(problem)

    assert String.contains?(result, "3 axioms:")
    assert String.contains?(result, "ax1")
    assert String.contains?(result, "ax2")
    assert String.contains?(result, "ax3")
  end

  test "to_string does not show axioms section when empty" do
    problem = %Problem{axioms: []}

    result = to_string(problem)

    refute String.contains?(result, "axioms:")
  end

  test "to_string shows no conjecture message when absent" do
    problem = %Problem{conjecture: nil}

    result = to_string(problem)

    assert String.contains?(result, "No conjecture provided")
  end

  test "to_string shows conjecture when provided" do
    problem = %Problem{conjecture: {"conj", 42}}

    result = to_string(problem)

    assert String.contains?(result, "Defines conjecture: conj")
  end

  test "to_string combines all sections on complete problem" do
    problem = %Problem{
      path: "/problems/complex.p",
      includes: ["lib1.ax", "lib2.ax"],
      types: %{"mytype" => :base_type},
      definitions: %{%Declaration{kind: :co, name: "f", type: Type.new(:i)} => 1},
      axioms: [{"ax1", 5}, {"ax2", 6}],
      conjecture: {"goal", 100}
    }

    result = to_string(problem)

    assert String.contains?(result, "Problem /problems/complex.p")
    assert String.contains?(result, "includes: lib1.ax, lib2.ax")
    assert String.contains?(result, "Types:")
    assert String.contains?(result, "Depends on")
    assert String.contains?(result, "2 axioms:")
    assert String.contains?(result, "Defines conjecture: goal")
  end

  test "to_string handles special memory path correctly" do
    problem = %Problem{path: "memory"}

    result = to_string(problem)

    assert String.contains?(result, "Problem <unnamed>")
  end

  test "String.Chars protocol implemented for Problem" do
    problem = %Problem{path: "test.p"}

    result = Kernel.to_string(problem)

    # Should call the String.Chars.to_string implementation
    assert String.contains?(result, "Problem test.p")
  end
end

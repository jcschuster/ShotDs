defmodule ShotDs.Hol.SigilsTest do
  use ShotDs.TermFactoryCase

  alias ShotDs.Data.{Context, Term}
  alias ShotDs.Hol.Sigils
  alias ShotDs.Parser
  alias ShotDs.Tptp

  test "sigil_f/2 parses valid TH0 formulas with empty modifiers" do
    formula_str = "$true => $false"

    result = Sigils.sigil_f(formula_str, [])

    assert is_integer(result)
    assert result > 0
  end

  test "sigil_f/2 returns term ID for simple atom with context" do
    formula_str = "$true"

    result = Sigils.sigil_f(formula_str, [])

    assert is_integer(result)
    assert result > 0
  end

  test "sigil_f/2 uses global context from process dictionary when available" do
    ctx = Context.new() |> Context.put_const("f", Type.new(:i, :o))

    result =
      Sigils.with_context(ctx, fn ->
        # Inside with_context, sigil_f should use ctx from process dictionary
        Sigils.sigil_f("f @ $true", [])
      end)

    assert is_integer(result)
    assert result > 0
  end

  test "sigil_f/2 uses empty context when no process context is set" do
    # Ensure no process context is set
    Process.delete(:hol_context)

    # Should parse successfully with empty context
    result = Sigils.sigil_f("$true", [])
    assert is_integer(result)
    assert result > 0
  end

  test "sigil_f/2 raises on invalid formula syntax" do
    assert_raise ShotDs.Parser.ParseError, fn ->
      Sigils.sigil_f("invalid syntax !!!", [])
    end
  end

  test "sigil_f/2 with variable without type assignment" do
    # Variables without context are assigned type variables and
    # outermost variables get type o by type inference
    Process.delete(:hol_context)

    result = Sigils.sigil_f("X", [])
    assert is_integer(result)
    assert result > 0
  end

  test "sigil_p/2 parses valid TPTP strings" do
    tptp_str = "thf(ax, axiom, $true)."

    result = Sigils.sigil_p(tptp_str, [])

    assert %_{} = result
  end

  test "sigil_p/2 returns problem matching Tptp.parse_tptp_string!" do
    tptp_str = "thf(ax, axiom, $true)."

    sigil_result = Sigils.sigil_p(tptp_str, [])
    tptp_result = Tptp.parse_tptp_string!(tptp_str)

    assert sigil_result == tptp_result
  end

  test "sigil_p/2 raises on invalid TPTP syntax" do
    # TPTP parser raises ArgumentError for invalid syntax, not ParseError
    assert_raise ArgumentError, fn ->
      Sigils.sigil_p("invalid tptp syntax", [])
    end
  end

  test "sigil_e/2 parses valid context declarations" do
    context_str = "X::$i"

    result = Sigils.sigil_e(context_str, [])

    assert %Context{} = result
  end

  test "sigil_e/2 returns context matching Parser.parse_context!" do
    context_str = "X::$i"

    sigil_result = Sigils.sigil_e(context_str, [])
    parser_result = Parser.parse_context!(context_str)

    assert sigil_result == parser_result
  end

  test "sigil_e/2 should raise on invalid context syntax" do
    assert_raise ShotDs.Parser.ParseError, fn ->
      Sigils.sigil_e("invalid context !!!", [])
    end
  end

  test "with_context/2 sets process context for nested sigil operations" do
    ctx = Context.new() |> Context.put_var("Y", Type.new(:i))

    result =
      Sigils.with_context(ctx, fn ->
        # sigil_f should use the provided context
        Sigils.sigil_f("$true", [])
      end)

    assert is_integer(result)
    assert result > 0
  end

  test "with_context/2 restores old context after execution" do
    ctx1 = Context.new() |> Context.put_var("X", Type.new(:i))
    ctx2 = Context.new() |> Context.put_var("Y", Type.new(:o))

    # Set initial context
    Process.put(:hol_context, ctx1)

    Sigils.with_context(ctx2, fn ->
      # Inside, context should be ctx2
      retrieved_ctx = Process.get(:hol_context)
      assert retrieved_ctx == ctx2
    end)

    # After, context should be restored to ctx1
    restored_ctx = Process.get(:hol_context)
    assert restored_ctx == ctx1
  end

  test "with_context/2 deletes context if none was set before" do
    # Ensure no context is set
    Process.delete(:hol_context)

    ctx = Context.new() |> Context.put_var("Z", Type.new(:i))

    Sigils.with_context(ctx, fn ->
      # Inside, context should be set
      assert Process.get(:hol_context) == ctx
    end)

    # After, context should be deleted since none was set before
    assert Process.get(:hol_context) == nil
  end

  test "with_context/2 cleans up context even on error" do
    Process.delete(:hol_context)

    ctx = Context.new() |> Context.put_var("W", Type.new(:i))

    catch_error(
      Sigils.with_context(ctx, fn ->
        raise "test error"
      end)
    )

    # Context should be cleaned up after error
    assert Process.get(:hol_context) == nil
  end

  test "with_context/2 can be nested and properly manages stack" do
    ctx1 = Context.new() |> Context.put_var("X", Type.new(:i))
    ctx2 = Context.new() |> Context.put_var("Y", Type.new(:o))

    Process.delete(:hol_context)

    result =
      Sigils.with_context(ctx1, fn ->
        inner_result =
          Sigils.with_context(ctx2, fn ->
            # Should have ctx2 here
            inner_ctx = Process.get(:hol_context)
            assert inner_ctx == ctx2
            "inner"
          end)

        # Should have ctx1 again
        outer_ctx = Process.get(:hol_context)
        assert outer_ctx == ctx1

        inner_result
      end)

    assert result == "inner"
    # Should have no context after all nesting
    assert Process.get(:hol_context) == nil
  end

  test "sigil_f/2 with conjunction formula" do
    formula = "$true & $false"

    result = Sigils.sigil_f(formula, [])

    assert is_integer(result)
    assert result > 0
  end

  test "sigil_f/2 with implication formula" do
    formula = "$true => $false"

    result = Sigils.sigil_f(formula, [])

    assert is_integer(result)
    assert result > 0
  end

  test "sigil_f/2 with negation formula" do
    formula = "~ $true"

    result = Sigils.sigil_f(formula, [])

    assert is_integer(result)
    assert result > 0
  end

  test "multiple sigil uses with different contexts" do
    ctx1 = Context.new() |> Context.put_const("p", Type.new(:o))
    ctx2 = Context.new() |> Context.put_const("q", Type.new(:o))

    result1 =
      Sigils.with_context(ctx1, fn ->
        Sigils.sigil_f("p", [])
      end)

    result2 =
      Sigils.with_context(ctx2, fn ->
        Sigils.sigil_f("q", [])
      end)

    assert is_integer(result1)
    assert is_integer(result2)
    assert result1 != result2
  end
end

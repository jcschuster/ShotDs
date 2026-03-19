defmodule ShotDsTest do
  use ShotDs.TermFactoryCase

  alias ShotDs.Data.Context
  alias ShotDs.Parser
  alias ShotDs.Tptp
  alias ShotDs.Util.{Builder, Formatter}

  test "init/0 delegate forwards to TermFactory.init/0" do
    assert_raise ArgumentError, fn ->
      ShotDs.init()
    end
  end

  test "parse delegates to Parser for arities 1 and 2" do
    formula = "$true => $false"

    assert ShotDs.parse(formula) == Parser.parse(formula)

    ctx =
      Context.new()
      |> Context.put_const("f", Type.new(:o, :i))
      |> Context.put_var("X", Type.new(:i))

    assert ShotDs.parse("f @ X", ctx) == Parser.parse("f @ X", ctx)
  end

  test "parse_type/1 delegates to Parser.parse_type/1" do
    assert ShotDs.parse_type("$i>$o") == Parser.parse_type("$i>$o")
  end

  test "parse_tptp_string/1 delegates to Tptp.parse_tptp_string/1" do
    content = "thf(ax,axiom,$true)."

    assert ShotDs.parse_tptp_string(content) == Tptp.parse_tptp_string(content)
  end

  test "parse_tptp_file delegates to Tptp.parse_tptp_file for arities 1 and 2" do
    prev = System.get_env("TPTP_ROOT")
    on_exit(fn -> reset_env("TPTP_ROOT", prev) end)

    System.delete_env("TPTP_ROOT")

    assert ShotDs.parse_tptp_file("missing.p") == Tptp.parse_tptp_file("missing.p")

    dir = mk_tmp_dir()
    path = Path.join(dir, "problem.p")
    File.write!(path, "thf(ax,axiom,$true).")

    assert ShotDs.parse_tptp_file(path, false) == Tptp.parse_tptp_file(path, false)
  end

  test "construction delegates build terms with expected shapes" do
    i = Type.new(:i)

    x = ShotDs.make_free_var_term("X", i)
    c = ShotDs.make_const_term("c", i)

    assert x == TF.make_free_var_term("X", i)
    assert c == TF.make_const_term("c", i)
  end

  test "lambda/2 and app/2 delegates construct and apply terms" do
    i = Type.new(:i)

    lambda_id = ShotDs.lambda(i, fn x -> x end)

    assert %Term{type: %Type{goal: :i, args: [%Type{goal: :i}]}, bvars: [_]} =
             TF.get_term(lambda_id)

    f = ShotDs.make_const_term("f", Type.new(:o, :i))
    x = ShotDs.make_const_term("a", i)

    assert ShotDs.app(f, x) == Builder.app(f, x)
    assert ShotDs.app(f, [x]) == Builder.app(f, [x])
  end

  test "format delegates match Formatter for arities 1 and 2" do
    term_id = ShotDs.parse("$true & $false")
    term = TF.get_term(term_id)

    assert ShotDs.format(term) == Formatter.format(term)
    assert ShotDs.format(term, true) == Formatter.format(term, true)
  end

  defp mk_tmp_dir do
    dir = Path.join(System.tmp_dir!(), "shot_ds_test_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    dir
  end

  defp reset_env(_name, nil), do: System.delete_env("TPTP_ROOT")
  defp reset_env(name, value), do: System.put_env(name, value)
end

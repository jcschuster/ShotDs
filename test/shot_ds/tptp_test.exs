defmodule ShotDs.TptpTest do
  use ShotDs.TermFactoryCase

  alias ShotDs.Tptp
  alias ShotDs.Parser

  test "parse_tptp_string/2 parses type declarations, axioms and conjectures" do
    content = """
    thf(a_t,type,a:$i).
    thf(p_t,type,p:$i>$o).
    thf(ax1,axiom,(p @ a)).
    thf(cj,conjecture,?[X:$i]:(p @ X)).
    """

    assert {:ok, problem} = Tptp.parse_tptp_string(content, "memory")

    assert problem.path == "memory"
    assert problem.types["a"].body == Type.new(:i)
    assert problem.types["p"].body == Type.new(:o, :i)
    assert length(problem.axioms) == 1
    assert {"cj", _term_id} = problem.conjecture
  end

  test "parse_tptp_string/2 stores definitions and keeps them available in later context" do
    content = """
    thf(a_t,type,a:$i).
    thf(f_t,type,f:$i).
    thf(def1,definition,(f = a)).
    thf(ax1,axiom,(f = a)).
    """

    assert {:ok, problem} = Tptp.parse_tptp_string(content, "memory")

    # Definitions are stored with Declaration objects as keys
    f_decl = %Declaration{kind: :co, name: "f", type: Type.new(:i)}
    assert Map.has_key?(problem.definitions, f_decl)
    assert [{"ax1", _}] = problem.axioms
  end

  test "parse_tptp_string/2 reports lexer leftovers" do
    assert {:error, msg} = Tptp.parse_tptp_string("thf(x,axiom,$true). #", "memory")

    assert String.contains?(msg, "Lexer failed")
    assert String.contains?(msg, "#")
  end

  test "parse_tptp_file/2 with non-TPTP mode reads direct file path" do
    dir = mk_tmp_dir()
    path = Path.join(dir, "problem.p")

    File.write!(path, "thf(ax,axiom,$true).")

    assert {:ok, problem} = Tptp.parse_tptp_file(path, :custom)
    assert problem.path == path
    assert problem.axioms != []
  end

  test "parse_tptp_file/2 in Tptp mode requires TPTP_ROOT" do
    prev = System.get_env("TPTP_ROOT")
    on_exit(fn -> reset_env("TPTP_ROOT", prev) end)

    System.delete_env("TPTP_ROOT")

    assert {:error, msg} = Tptp.parse_tptp_file("foo.p")
    assert String.contains?(msg, "TPTP_ROOT")
  end

  test "parse_tptp_file/2 resolves includes through TPTP_ROOT and merges problems" do
    dir = mk_tmp_dir()
    prev = System.get_env("TPTP_ROOT")
    on_exit(fn -> reset_env("TPTP_ROOT", prev) end)

    System.put_env("TPTP_ROOT", dir)

    inc_path = Path.join(dir, "inc.p")

    problems_dir = Path.join(dir, "Problems")
    domain_dir = Path.join(problems_dir, "TST")

    File.mkdir_p!(problems_dir)
    File.mkdir_p!(domain_dir)

    main_path = Path.join(domain_dir, "TSTmain.p")

    File.write!(inc_path, "thf(a_t,type,a:$i). thf(ax_inc,axiom,$true).")

    File.write!(
      main_path,
      "include('inc.p'). thf(cj,conjecture,$true)."
    )

    assert {:ok, problem} = Tptp.parse_tptp_file("TSTmain.p")

    assert Enum.any?(problem.includes, &String.ends_with?(&1, "inc.p"))
    assert Map.has_key?(problem.types, "a")
    assert Enum.any?(problem.axioms, fn {name, _} -> name == "ax_inc" end)
    assert {"cj", _} = problem.conjecture
  end

  test "parse_tptp_string/2 reports cyclic include" do
    assert {:error, msg} = Tptp.parse_tptp_string("include('self.p').", "self.p")
    assert String.contains?(msg, "Cyclic import")
  end

  test "parse_tptp_string/2 reports unexpected tokens" do
    assert {:error, msg} = Tptp.parse_tptp_string("$true", "memory")
    assert String.contains?(msg, "Unexpected token")
  end

  # --- unparse tests ---

  test "unparse/1 renders truth and falsity" do
    {:ok, p_true} = Tptp.parse_tptp_string("thf(ax,axiom,$true).", "memory")
    {:ok, p_false} = Tptp.parse_tptp_string("thf(ax,axiom,$false).", "memory")
    {_, t_id} = hd(p_true.axioms)
    {_, f_id} = hd(p_false.axioms)
    assert {:ok, "$true"} = Parser.unparse(t_id)
    assert {:ok, "$false"} = Parser.unparse(f_id)
  end

  test "unparse/1 renders negation" do
    {:ok, problem} = Tptp.parse_tptp_string("thf(ax,axiom,~$true).", "memory")
    {_, term_id} = hd(problem.axioms)
    assert {:ok, "~$true"} = Parser.unparse(term_id)
  end

  test "unparse/1 renders conjunction" do
    {:ok, problem} = Tptp.parse_tptp_string("thf(ax,axiom,$true & $false).", "memory")
    {_, term_id} = hd(problem.axioms)
    assert {:ok, "$true & $false"} = Parser.unparse(term_id)
  end

  test "unparse/1 renders disjunction" do
    {:ok, problem} = Tptp.parse_tptp_string("thf(ax,axiom,$true | $false).", "memory")
    {_, term_id} = hd(problem.axioms)
    assert {:ok, "$true | $false"} = Parser.unparse(term_id)
  end

  test "unparse/1 renders implication with parentheses for left-assoc case" do
    {:ok, problem} =
      Tptp.parse_tptp_string("thf(ax,axiom,($true => $false) => $true).", "memory")

    {_, term_id} = hd(problem.axioms)
    assert {:ok, formula} = Parser.unparse(term_id)
    assert String.contains?(formula, "($true => $false) =>")
  end

  test "unparse/1 renders universal quantification" do
    {:ok, problem} =
      Tptp.parse_tptp_string("thf(p_t,type,p:$i>$o). thf(ax,axiom,![X:$i]: p @ X).", "memory")

    {_, term_id} = hd(problem.axioms)
    assert {:ok, formula} = Parser.unparse(term_id)
    assert String.contains?(formula, "![")
    assert String.contains?(formula, "$i]:")
    assert String.contains?(formula, "p @")
  end

  test "unparse/1 renders existential quantification" do
    {:ok, problem} =
      Tptp.parse_tptp_string("thf(p_t,type,p:$i>$o). thf(ax,axiom,?[X:$i]: p @ X).", "memory")

    {_, term_id} = hd(problem.axioms)
    assert {:ok, formula} = Parser.unparse(term_id)
    assert String.contains?(formula, "?[")
  end

  test "unparse/1 flattens nested universal quantifiers" do
    {:ok, problem} =
      Tptp.parse_tptp_string(
        "thf(p_t,type,p:$i>$i>$o). thf(ax,axiom,![X:$i,Y:$i]: p @ X @ Y).",
        "memory"
      )

    {_, term_id} = hd(problem.axioms)
    assert {:ok, formula} = Parser.unparse(term_id)
    assert String.contains?(formula, "![")
    # Should have two variables in the single binder list
    assert Regex.match?(~r/!\[.*:.*,.*:.*\]/, formula)
  end

  test "unparse/1 renders equality" do
    {:ok, problem} =
      Tptp.parse_tptp_string("thf(a_t,type,a:$i). thf(ax,axiom,a = a).", "memory")

    {_, term_id} = hd(problem.axioms)
    assert {:ok, formula} = Parser.unparse(term_id)
    assert String.contains?(formula, " = ")
  end

  test "unparse_problem/1 with term_id wraps in thf annotation" do
    {:ok, problem} = Tptp.parse_tptp_string("thf(cj,conjecture,$true).", "memory")
    {_, term_id} = problem.conjecture
    assert {:ok, output} = Tptp.unparse_problem(term_id)
    assert String.starts_with?(output, "thf(f1, conjecture,")
    assert String.contains?(output, "$true")
  end

  test "unparse_problem/1 with Problem struct outputs full problem" do
    content = """
    thf(a_t,type,a:$i).
    thf(p_t,type,p:$i>$o).
    thf(ax1,axiom,(p @ a)).
    thf(cj,conjecture,?[X:$i]:(p @ X)).
    """

    {:ok, problem} = Tptp.parse_tptp_string(content, "memory")
    assert {:ok, output} = Tptp.unparse_problem(problem)
    assert String.contains?(output, "thf(a, type,")
    assert String.contains?(output, "thf(ax1, axiom,")
    assert String.contains?(output, "thf(cj, conjecture,")
    assert String.contains?(output, "p @")
  end

  defp mk_tmp_dir do
    dir = Path.join(System.tmp_dir!(), "shot_ds_test_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    dir
  end

  defp reset_env(_name, nil), do: System.delete_env("TPTP_ROOT")
  defp reset_env(name, value), do: System.put_env(name, value)
end

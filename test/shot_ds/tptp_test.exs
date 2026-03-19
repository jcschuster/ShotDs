defmodule ShotDs.TptpTest do
  use ShotDs.TermFactoryCase

  alias ShotDs.Tptp

  test "parse_tptp_string/2 parses type declarations, axioms and conjectures" do
    content = """
    thf(a_t,type,a:$i).
    thf(p_t,type,p:$i>$o).
    thf(ax1,axiom,(p @ a)).
    thf(cj,conjecture,?[X:$i]:(p @ X)).
    """

    assert {:ok, problem} = Tptp.parse_tptp_string(content, "memory")

    assert problem.path == "memory"
    assert problem.types["a"] == Type.new(:i)
    assert problem.types["p"] == Type.new(:o, :i)
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

    assert Map.has_key?(problem.definitions, "def1")
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

    assert {:ok, problem} = Tptp.parse_tptp_file(path, false)
    assert problem.path == path
    assert problem.axioms != []
  end

  test "parse_tptp_file/2 in Tptp mode requires TPTP_ROOT" do
    prev = System.get_env("TPTP_ROOT")
    on_exit(fn -> reset_env("TPTP_ROOT", prev) end)

    System.delete_env("TPTP_ROOT")

    assert {:error, msg} = Tptp.parse_tptp_file("foo.p", true)
    assert String.contains?(msg, "TPTP_ROOT")
  end

  test "parse_tptp_file/2 resolves includes through TPTP_ROOT and merges problems" do
    dir = mk_tmp_dir()
    prev = System.get_env("TPTP_ROOT")
    on_exit(fn -> reset_env("TPTP_ROOT", prev) end)

    System.put_env("TPTP_ROOT", dir)

    inc_path = Path.join(dir, "inc.p")
    main_path = Path.join(dir, "main.p")

    File.write!(inc_path, "thf(a_t,type,a:$i). thf(ax_inc,axiom,$true).")

    File.write!(
      main_path,
      "include('inc.p'). thf(cj,conjecture,$true)."
    )

    assert {:ok, problem} = Tptp.parse_tptp_file("main.p", true)

    assert Enum.any?(problem.includes, &String.ends_with?(&1, "inc.p"))
    assert Map.has_key?(problem.types, "a")
    assert Enum.any?(problem.axioms, fn {name, _} -> name == "ax_inc" end)
    assert {"cj", _} = problem.conjecture
  end

  test "parse_tptp_string/2 raises on cyclic include" do
    assert_raise RuntimeError, ~r/Cyclic import/, fn ->
      Tptp.parse_tptp_string("include('self.p').", "self.p")
    end
  end

  test "parse_tptp_string/2 reports unexpected tokens" do
    assert {:error, msg} = Tptp.parse_tptp_string("$true", "memory")
    assert String.contains?(msg, "Unexpected token")
  end

  defp mk_tmp_dir do
    dir = Path.join(System.tmp_dir!(), "shot_ds_test_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    dir
  end

  defp reset_env(_name, nil), do: System.delete_env("TPTP_ROOT")
  defp reset_env(name, value), do: System.put_env(name, value)
end

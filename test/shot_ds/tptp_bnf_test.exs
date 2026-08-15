defmodule ShotDs.TptpBnfTest do
  @moduledoc """
  Conformance tests against the TPTP syntax BNF
  (https://tptp.org/UserDocs/TPTPLanguage/SyntaxBNF.html).

  Constructs that are syntactically well-formed TPTP but have no counterpart in
  Church's simple type theory are expected to fail with a descriptive error
  rather than a lexer or pattern-match crash.
  """

  use ShotDs.TermFactoryCase

  alias ShotDs.Parser
  alias ShotDs.Tptp

  describe "<thf_atom_typing>" do
    test "accepts the parenthesised form" do
      assert {:ok, problem} = Tptp.parse_tptp_string("thf(p_type,type,( p : $i>$o )).")
      assert problem.types["p"].body == Type.new(:o, :i)
    end

    test "accepts arbitrarily nested parentheses" do
      assert {:ok, problem} = Tptp.parse_tptp_string("thf(p_type,type,((( p : $i )))).")
      assert problem.types["p"].body == Type.new(:i)
    end

    test "accepts a distinct object as <typeable_atom>" do
      assert {:ok, problem} = Tptp.parse_tptp_string(~S|thf(o_type,type,"Bob" : $i).|)
      assert problem.types["Bob"].body == Type.new(:i)
    end

    test "reports a descriptive error for a malformed declaration" do
      assert {:error, msg} = Tptp.parse_tptp_string("thf(bad,type,$i>$o).")
      assert String.contains?(msg, "not a valid type declaration")
    end
  end

  describe "<annotations>" do
    test "ignores a <source>" do
      content = "thf(ax,axiom,$true,file('X.p',ax))."
      assert {:ok, problem} = Tptp.parse_tptp_string(content)
      assert [{"ax", _}] = problem.axioms
    end

    test "ignores a <source> together with <optional_info>" do
      content = "thf(ax,axiom,$true,inference(rw,[status(thm)],[a,b]),[bar(1)])."
      assert {:ok, problem} = Tptp.parse_tptp_string(content)
      assert [{"ax", _}] = problem.axioms
    end

    test "does not confuse a binder comma with the annotation comma" do
      content = "thf(ax,axiom,![X: $i,Y: $i]: (p @ X @ Y),file('X.p',ax))."
      assert {:ok, problem} = Tptp.parse_tptp_string(content)
      assert [{"ax", _}] = problem.axioms
    end
  end

  describe "<formula_role>" do
    test "treats theorem and corollary as usable axioms" do
      content = "thf(t,theorem,$true). thf(c,corollary,$true)."
      assert {:ok, problem} = Tptp.parse_tptp_string(content)
      assert [{"t", _}, {"c", _}] = problem.axioms
    end

    test "accepts any <lower_word> as a role" do
      assert {:ok, problem} = Tptp.parse_tptp_string("thf(x,some_new_role,$true).")
      assert problem.axioms == []
    end

    test "accepts the <lower_word>-<general_term> form" do
      content = "thf(a,axiom-1,$true). thf(b,axiom-inference(x,[y,z]),$true)."
      assert {:ok, problem} = Tptp.parse_tptp_string(content)
      assert [{"a", _}, {"b", _}] = problem.axioms
    end

    test "still checks formulas of an ignored role" do
      assert {:error, msg} = Tptp.parse_tptp_string("thf(x,plain,$true & &).")
      assert String.contains?(msg, "Failed to parse formula 'x'")
    end
  end

  describe "<name>" do
    test "accepts an <integer> as name" do
      assert {:ok, problem} = Tptp.parse_tptp_string("thf(42,axiom,$true).")
      assert [{"42", _}] = problem.axioms
    end

    test "accepts a <single_quoted> name with an escaped quote" do
      assert {:ok, problem} = Tptp.parse_tptp_string(~S|thf('it\'s',axiom,$true).|)
      assert [{"it's", _}] = problem.axioms
    end
  end

  describe "lexical rules" do
    test "skips <comment_block>s" do
      content = "/* a block\n   comment */ thf(ax,axiom,$true). /**/"
      assert {:ok, problem} = Tptp.parse_tptp_string(content)
      assert [{"ax", _}] = problem.axioms
    end

    test "lexes <dollar_dollar_word>s as system constants" do
      assert {:ok, tokens, "", _, _, _} = Lexer.tokenize("$$foo")
      assert [{:system, "$$foo", 0}] = tokens
    end

    test "lexes the <number> forms" do
      assert {:ok, tokens, "", _, _, _} = Lexer.tokenize("12 -3 1/2 3.14 2.0e-3")

      assert [
               {:integer, "12", _},
               {:integer, "-3", _},
               {:rational, "1/2", _},
               {:real, "3.14", _},
               {:real, "2.0e-3", _}
             ] = tokens
    end

    test "resolves escapes and strips quotes in quoted tokens" do
      assert {:ok, [{:distinct, "a'b", 0}], "", _, _, _} = Lexer.tokenize(~S|'a\'b'|)
      assert {:ok, [{:distinct_object, ~S|a"b|, 0}], "", _, _, _} = Lexer.tokenize(~S|"a\"b"|)
    end

    test "reports byte offsets after a quoted token" do
      assert {:ok, [_, {:atom, "b", 7}], "", _, _, _} = Lexer.tokenize(~S|'a\'b' b|)
    end
  end

  describe "<thf_atomic_formula>" do
    test "types <number> literals by their arithmetic sort" do
      content = "thf(n,type,n : $int). thf(ax,axiom,n = 42)."
      assert {:ok, problem} = Tptp.parse_tptp_string(content)
      assert [{"ax", _}] = problem.axioms
    end

    test "maps $iType and $oType onto $i and $o" do
      assert Parser.parse_type!("$iType>$oType") == Type.new(:o, :i)
    end

    test "round-trips the arithmetic <defined_type>s" do
      assert Parser.unparse_type(Parser.parse_type!("$int>$rat>$real")) == "$int > $rat > $real"
    end

    test "round-trips a mapping type into a user-declared base type" do
      assert Parser.unparse_type(Parser.parse_type!("$int>pt")) == "$int > pt"
      assert Parser.unparse_type(Parser.parse_type!("($int>pt)>pt>$o")) == "($int > pt) > pt > $o"
    end

    test "renders declared type constructors as applications" do
      type = Parser.parse_type!("$int>pt")

      assert Parser.with_type_constructors([:pt], fn -> Parser.unparse_type(type) end) ==
               "pt @ $int"
    end

    test "rejects a <defined_type> used in term position" do
      assert {:error, msg} = Tptp.parse_tptp_string("thf(ax,axiom,$true & $i).")
      assert String.contains?(msg, "denotes a type")
    end

    test "parses $$-words as ordinary constants" do
      assert {:ok, problem} = Tptp.parse_tptp_string("thf(ax,axiom,$$foo).")
      assert [{"ax", _}] = problem.axioms
    end

    test "parses $ite as a defined if-then-else term" do
      content = "thf(p,type,p : $o). thf(ax,axiom,$ite(p,$true,$false))."
      assert {:ok, problem} = Tptp.parse_tptp_string(content)
      assert [{"ax", _}] = problem.axioms
    end

    test "parses a <thf_conn_term> in parentheses" do
      assert {:ok, _} = Tptp.parse_tptp_string("thf(ax,axiom,(&) @ $true @ $false).")
      assert {:ok, _} = Tptp.parse_tptp_string("thf(ax,axiom,(~) @ $true).")
    end
  end

  describe "<th0_quantifier> and <thf_definition>" do
    test "parses the @+ choice binder" do
      content =
        "thf(p,type,p : $i>$o). thf(q,type,q : $i>$o). thf(ax,axiom,q @ (@+[X: $i]: (p @ X)))."

      assert {:ok, problem} = Tptp.parse_tptp_string(content)
      assert [{"ax", _}] = problem.axioms
    end

    test "parses the @- description binder" do
      content =
        "thf(p,type,p : $i>$o). thf(q,type,q : $i>$o). thf(ax,axiom,q @ (@-[X: $i]: (p @ X)))."

      assert {:ok, problem} = Tptp.parse_tptp_string(content)
      assert [{"ax", _}] = problem.axioms
    end

    test "reads <identical> (==) as an equality, so it defines a constant" do
      content = "thf(a,type,a : $i). thf(f,type,f : $i). thf(d,definition,f == a)."
      assert {:ok, problem} = Tptp.parse_tptp_string(content)

      assert Map.has_key?(problem.definitions, %Declaration{
               kind: :co,
               name: "f",
               type: Type.new(:i)
             })
    end

    test "reads @= as polymorphic equality" do
      assert {:ok, _} = Tptp.parse_tptp_string("thf(ax,axiom,$true @= $true).")
    end
  end

  describe "<formula_selection>" do
    test "includes only the selected formulas" do
      dir = mk_tmp_dir()
      prev = System.get_env("TPTP_ROOT")
      on_exit(fn -> reset_env("TPTP_ROOT", prev) end)
      System.put_env("TPTP_ROOT", dir)

      File.write!(
        Path.join(dir, "sel.ax"),
        "thf(a_t,type,a:$i). thf(keep,axiom,$true). thf(drop,axiom,$false)."
      )

      assert {:ok, problem} =
               Tptp.parse_tptp_string("include('sel.ax',[a_t,keep]).", "main.p")

      assert Map.has_key?(problem.types, "a")
      assert [{"keep", _}] = problem.axioms
    end

    test "rejects a malformed include directive" do
      assert {:error, msg} = Tptp.parse_tptp_string("include('sel.ax' foo).", "main.p")
      assert String.contains?(msg, "malformed include")
    end
  end

  describe "constructs outside simple type theory" do
    test "reports tuples and sequents" do
      assert {:error, msg} = Tptp.parse_tptp_string("thf(ax,axiom,[$true] --> [$false]).")
      assert String.contains?(msg, "tuples")
    end

    test "reports $let" do
      assert {:error, msg} = Tptp.parse_tptp_string("thf(ax,axiom,$let(q : $o, q := $true, q)).")
      assert String.contains?(msg, "$let")
    end

    test "reports subtype declarations" do
      assert {:error, msg} = Tptp.parse_tptp_string("thf(ax,axiom,a << b).")
      assert String.contains?(msg, "subtype")
    end

    test "reports product and union types" do
      assert {:error, star} = Tptp.parse_tptp_string("thf(f,type,f : ($i * $i) > $o).")
      assert String.contains?(star, "product types")

      assert {:error, plus} = Tptp.parse_tptp_string("thf(f,type,f : ($i + $i) > $o).")
      assert String.contains?(plus, "union types")
    end

    test "reports existential type quantification" do
      assert {:error, msg} = Tptp.parse_tptp_string("thf(f,type,f : ?*[A : $tType] : (A > A)).")
      assert String.contains?(msg, "?*")
    end
  end

  defp mk_tmp_dir do
    dir = Path.join(System.tmp_dir!(), "shot_ds_bnf_test_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    dir
  end

  defp reset_env(_name, nil), do: System.delete_env("TPTP_ROOT")
  defp reset_env(name, value), do: System.put_env(name, value)
end

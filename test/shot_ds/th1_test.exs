defmodule ShotDs.Th1Test do
  use ShotDs.TermFactoryCase

  alias ShotDs.Parser
  alias ShotDs.Tptp
  alias ShotDs.Data.TypeScheme

  ########## Type-constructor application in type expressions ##########

  test "parse_type_scheme/1 parses set @ A with type-constructor application" do
    {:ok, scheme} = Parser.parse_type_scheme("!>[A: $tType]: set @ A > A > $o")

    assert %TypeScheme{vars: [_a_ref]} = scheme
    assert %ShotDs.Data.Type{goal: :o, args: [set_a, a]} = scheme.body
    assert %ShotDs.Data.Type{goal: :set, args: [^a]} = set_a
  end

  test "parse_type_scheme/1 parses nested type-constructor application" do
    {:ok, scheme} = Parser.parse_type_scheme("!>[A: $tType, B: $tType]: map @ A @ B > $o")

    assert %TypeScheme{vars: [_, _]} = scheme
    assert %ShotDs.Data.Type{goal: :o, args: [map_ab]} = scheme.body
    assert %ShotDs.Data.Type{goal: :map} = map_ab
    assert length(map_ab.args) == 2
  end

  test "parse_type!/1 parses single-quoted custom type names" do
    assert Parser.parse_type!("'my_custom_type'") == ShotDs.Data.Type.new(:my_custom_type)
  end

  test "parse_type_scheme/1 parses type with single-quoted type name" do
    {:ok, scheme} = Parser.parse_type_scheme("!>[A: $tType]: 'set' @ A > $o")

    assert %TypeScheme{vars: [_a_ref]} = scheme
    assert %ShotDs.Data.Type{goal: :o, args: [set_a]} = scheme.body
    assert %ShotDs.Data.Type{goal: :set, args: [_]} = set_a
  end

  ########## TH1 formula-level polymorphism ##########

  test "parse/2 handles ![A: $tType, X: A]: X = X (type binder with term variable)" do
    term_id = Parser.parse("![A: $tType, X: A]: X = X") |> ok!()

    assert %ShotDs.Data.Term{type: %ShotDs.Data.Type{goal: :o}} = term!(term_id)
  end

  test "parse/2 handles quantifier with only $tType binders" do
    term_id = Parser.parse("![A: $tType]: $true") |> ok!()
    assert %ShotDs.Data.Term{type: %ShotDs.Data.Type{goal: :o}} = term!(term_id)
  end

  test "parse/2 handles mixed type and term binders" do
    term_id = Parser.parse("![A: $tType, X: A, Y: A]: X = Y") |> ok!()
    assert %ShotDs.Data.Term{type: %ShotDs.Data.Type{goal: :o}} = term!(term_id)
  end

  ########## Polymorphic constants and type erasure ##########

  test "parse/2 erases type argument for polymorphic constant" do
    {:ok, member_scheme} = Parser.parse_type_scheme("!>[A: $tType]: A > set @ A > $o")

    ctx = Context.new() |> Context.put_const("member", member_scheme)

    term_id =
      Parser.parse("![A: $tType, C: A, A3: set @ A]: ( member @ A @ C @ A3 )", ctx: ctx) |> ok!()

    assert %ShotDs.Data.Term{type: %ShotDs.Data.Type{goal: :o}} = term!(term_id)
  end

  test "parse/2 erases single-quoted type arguments" do
    {:ok, nil_scheme} = Parser.parse_type_scheme("!>[A: $tType]: 'ListOf' @ A")

    ctx =
      Context.new()
      |> Context.put_const("nil/0", nil_scheme)

    term_id = Parser.parse("'nil/0' @ 'Polynomial'", ctx: ctx) |> ok!()

    assert %ShotDs.Data.Term{type: %ShotDs.Data.Type{goal: :ListOf, args: [_]}} = term!(term_id)
  end

  test "parse_tptp_string/2 parses a problem whose type names are single-quoted" do
    content = """
    thf('ListOf_type', type, 'ListOf': $tType > $tType).
    thf('Polynomial_type', type, 'Polynomial': $tType).
    thf('nil/0_type', type, 'nil/0': !>[Tv0: $tType]: ( 'ListOf' @ Tv0 )).
    thf('length/1_type', type,
        'length/1': !>[Tv0: $tType]: ( ( 'ListOf' @ Tv0 ) > $int )).
    thf('.def_length_nil_axiom', axiom,
        ( ( 'length/1' @ 'Polynomial' @ ( 'nil/0' @ 'Polynomial' ) ) = 0 )).
    """

    assert {:ok, problem} = Tptp.parse_tptp_string(content, "memory")
    assert length(problem.axioms) == 1
  end

  test "parse_tptp_string/2 parses polymorphic constant applied to term variables without explicit type args" do
    content = """
    thf(leibniz_t, type, l: A > A > $o).
    thf(leibniz_def, definition,
      l = ^[X, Y]: ( ![P]: ( ( P @ X ) => ( P @ Y ) ) )
    ).
    thf(conj, conjecture,
      ![X: $i]: ( l @ X @ X )
    ).
    """

    assert {:ok, problem} = Tptp.parse_tptp_string(content, "memory")
    assert Map.has_key?(problem.types, "l")
    assert {"conj", _} = problem.conjecture
  end

  test "parse_tptp_string/2 parses polymorphic constant under function application in type argument position" do
    content = """
    thf(leibniz_t, type, l: A > A > $o).
    thf(leibniz_def, definition,
      l = ^[X, Y]: ( ![P]: ( ( P @ X ) => ( P @ Y ) ) )
    ).
    thf(conj, conjecture,
      ![X: $i, Y: $i, F: $i > $i]: (
        (l @ X @ Y) => (l @ (F @ X) @ (F @ Y))
      )
    ).
    """

    assert {:ok, problem} = Tptp.parse_tptp_string(content, "memory")
    assert Map.has_key?(problem.types, "l")
    assert {"conj", _} = problem.conjecture
  end

  ########## Full TPTP TH1 problem parsing ##########

  test "parse_tptp_string/2 parses TH1 type declarations with type-constructor application" do
    content = """
    thf(set_type, type, set: $tType > $tType).
    thf(member_type, type, member: !>[A: $tType]: A > set @ A > $o).
    thf(ax1, axiom, ![A: $tType, C: A, A3: set @ A]: ( member @ A @ C @ A3 )).
    """

    assert {:ok, problem} = Tptp.parse_tptp_string(content, "memory")
    assert Map.has_key?(problem.types, "member")
    assert Map.has_key?(problem.types, "set")
    assert length(problem.axioms) == 1
  end

  test "parse_tptp_string/2 parses negated_conjecture role as axiom" do
    content = """
    thf(ax1, axiom, $true).
    thf(nc1, negated_conjecture, $false).
    """

    assert {:ok, problem} = Tptp.parse_tptp_string(content, "memory")
    assert length(problem.axioms) == 2
  end

  test "parse_tptp_string/2 parses the fact_125_subsetD example" do
    content = """
    thf(set_type, type, set: $tType > $tType).
    thf(member_type, type, member: !>[A: $tType]: A > set @ A > $o).
    thf(ord_less_eq_type, type, ord_less_eq: !>[A: $tType]: A > A > $o).
    thf(fact_125_subsetD, axiom,
        ! [A: $tType, A3: set @ A, B2: set @ A, C: A] :
          ( ( ord_less_eq @ (set @ A) @ A3 @ B2 )
         => ( ( member @ A @ C @ A3 )
           => ( member @ A @ C @ B2 ) ) ) ).
    """

    assert {:ok, problem} = Tptp.parse_tptp_string(content, "memory")
    assert length(problem.axioms) == 1
    assert {"fact_125_subsetD", _} = hd(problem.axioms)
  end
end

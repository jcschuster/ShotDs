defmodule ShotDs.Tptp do
  @moduledoc """
  Contains utility to parse files from the TPTP problem library
  (https://tptp.org/TPTP/) as well as custom files in TPTP's TH0 syntax.

  For reference, the TH0 language is defined in
  https://doi.org/10.1007/s10817-017-9407-7.

  ## Coverage of the TPTP syntax BNF

  The parser accepts the THF fragment of the TPTP syntax BNF
  (https://tptp.org/UserDocs/TPTPLanguage/SyntaxBNF.html), including

  - `<thf_annotated>` with an arbitrary `<name>` (`<atomic_word>` or
    `<integer>`), any `<formula_role>` — also in its `<lower_word>-<general_term>`
    form — and optional `<annotations>`, which are accepted and discarded;
  - `<thf_atom_typing>` in both its plain and its (arbitrarily nested)
    parenthesised form;
  - `<include>` with an optional `<formula_selection>`, applied recursively;
  - `<th1_quantified_type>` (`!>`), type application, `$ite`, the choice and
    description binders `@+`/`@-` together with their constant forms
    `@@+`/`@@-`, `@=`, and `<identical>` (`==`), which is read as an equality;
  - the full lexical layer: line and block comments, `<single_quoted>` words
    with escapes, `<distinct_object>`s, `<dollar_word>`s and
    `<dollar_dollar_word>`s, and `<integer>`/`<rational>`/`<real>` literals,
    which become constants of type `$int`/`$rat`/`$real`;
  - the arithmetic `<defined_functor>`s and `<defined_predicate>`s (`$less`,
    `$sum`, `$to_real`, …), which are ad-hoc polymorphic in the numeric sort,
    so that a problem may use them at `$int`, `$rat` and `$real` alike.

  Binders scope over a single `<thf_unit_formula>`; an application chain or a
  binary connective following the body belongs to the enclosing formula, not to
  the binder. See `ShotDs.Parser` for details.

  Some TPTP constructs have no counterpart in Church's simple type theory and
  are rejected with a descriptive error rather than silently mis-parsed:
  `<thf_tuple>`, `<thf_sequent>`, `<thf_subtype>`, `<thf_xprod_type>`,
  `<thf_union_type>`, `<th1_quantified_type>` with `?*`, and `$let`.

  Formulas whose role carries no logical content (`plain`, `interpretation`,
  `unknown`, and any unrecognised `<lower_word>`) are parsed — so that syntax
  and type errors still surface — but are not stored in the `ShotDs.Data.Problem`.
  """

  alias ShotDs.Data.{Context, Problem, Declaration, Term, Type, TypeScheme}
  alias ShotDs.Parser
  alias ShotDs.Util.Lexer
  alias ShotDs.Stt.TermFactory, as: TF
  import ShotDs.Hol.Patterns

  @doc """
  Parses a TPTP file in TH0 syntax at the provided path into a
  `ShotDs.Data.Problem` struct. Returns a tuple `{:ok, result}` or
  `{:error, reason}`.

  This function serves two purposes: parsing a file from the TPTP problem
  library (https://tptp.org/TPTP/) or a custom problem file given by the user.

  `origin` indicates whether it is a file from the TPTP problem library and can
  be accessed via the environment variable `TPTP_ROOT` pointing to the root
  directory of the TPTP library.
  """
  @spec parse_tptp_file(String.t(), :tptp_problem | :tptp_relative | :custom) ::
          {:ok, Problem.t()} | {:error, String.t()}
  def parse_tptp_file(problem, origin \\ :tptp_problem)
      when is_binary(problem) and origin in [:tptp_problem, :tptp_relative, :custom] do
    with {:ok, path} <- resolve_path(problem, origin),
         {:ok, content} <- File.read(path) do
      parse_tptp_string(content, path)
    else
      {:error, reason} when is_binary(reason) ->
        {:error, reason}

      {:error, posix} ->
        {:error, "Could not read file (POSIX error): #{inspect(posix)}"}
    end
  end

  @doc """
  Parses a TPTP file in TH0 syntax at the provided path into a
  `ShotDs.Data.Problem` struct. Raises on errors.

  This function serves two purposes: parsing a file from the TPTP problem
  library (https://tptp.org/TPTP/) or a custom problem file given by the user.

  `origin` indicates whether it is a file from the TPTP problem library and can
  be accessed via the environment variable `TPTP_ROOT` pointing to the root
  directory of the TPTP library.
  """
  @spec parse_tptp_file!(String.t(), :tptp_problem | :tptp_relative | :custom) :: Problem.t()
  def parse_tptp_file!(problem, origin \\ :tptp_problem)
      when is_binary(problem) and origin in [:tptp_problem, :tptp_relative, :custom] do
    path = resolve_path!(problem, origin)
    content = File.read!(path)
    parse_tptp_string!(content, path)
  end

  @doc """
  Parses a string representing full a problem file in TPTP's TH0 syntax into a
  `ShotDs.Data.Problem` struct. Returns a tuple `{:ok, result}` or
  `{:error, reason}`.

  > #### Info {: .info}
  >
  > The parsing of `content` only supports including files from the TPTP problem
  > library. If such includes are present, make sure that the `TPTP_ROOT`
  > environment variable is set.
  """
  @spec parse_tptp_string(String.t(), String.t()) :: {:ok, Problem.t()} | {:error, String.t()}
  def parse_tptp_string(content, path \\ "memory") when is_binary(content) and is_binary(path) do
    case Lexer.tokenize(content) do
      {:ok, tokens, "", _, _, _} ->
        with {:ok, inlined_tokens, include_paths} <- inline_includes(tokens, MapSet.new([path])) do
          process_tokens(inlined_tokens, %Problem{path: path, includes: include_paths})
        end

      {:ok, _tokens, unparsed, _, _, _} ->
        {:error, "Lexer failed to parse entire string. Unparsed: #{unparsed}"}
    end
  end

  @doc """
  Parses a string representing full a problem file in TPTP's TH0 syntax into a
  `ShotDs.Data.Problem` struct. Raises on errors.

  > #### Info {: .info}
  >
  > The parsing of `content` only supports including files from the TPTP problem
  > library. If such includes are present, make sure that the `TPTP_ROOT`
  > environment variable is set.
  """
  @spec parse_tptp_string!(String.t(), String.t()) :: Problem.t()
  def parse_tptp_string!(content, path \\ "memory") when is_binary(content) and is_binary(path) do
    with {:ok, tokens, "", _, _, _} <- Lexer.tokenize(content),
         {:ok, inlined_tokens, include_paths} <- inline_includes(tokens, MapSet.new([path])),
         {:ok, problem} <-
           process_tokens(inlined_tokens, %Problem{path: path, includes: include_paths}) do
      problem
    else
      {:ok, _tokens, unparsed, _, _, _} ->
        raise ArgumentError, message: "Not a valid TPTP string. Failed to tokenize: #{unparsed}"

      {:error, reason} ->
        raise ArgumentError, message: "Not a valid TPTP string: #{reason}"
    end
  end

  defp resolve_path(problem, :tptp_problem) do
    case System.fetch_env("TPTP_ROOT") do
      :error ->
        {:error, "TPTP_ROOT environment variable is not set"}

      {:ok, root} ->
        domain = String.slice(problem, 0..2)

        with_file_ending =
          if String.ends_with?(problem, ".p") do
            problem
          else
            problem <> ".p"
          end

        {:ok, Path.join([root, "Problems", domain, with_file_ending])}
    end
  end

  defp resolve_path(problem, :tptp_relative) do
    case System.fetch_env("TPTP_ROOT") do
      :error -> {:error, "TPTP_ROOT environment variable is not set"}
      {:ok, root} -> {:ok, Path.join(root, problem)}
    end
  end

  defp resolve_path(problem, :custom), do: {:ok, problem}

  defp resolve_path!(problem, :tptp_problem) do
    root = System.fetch_env!("TPTP_ROOT")
    domain = String.slice(problem, 0..2)

    with_file_ending =
      if String.ends_with?(problem, ".p") do
        problem
      else
        problem <> ".p"
      end

    Path.join([root, "Problems", domain, with_file_ending])
  end

  defp resolve_path!(problem, :tptp_relative) do
    root = System.fetch_env!("TPTP_ROOT")
    Path.join(root, problem)
  end

  defp resolve_path!(problem, :custom), do: problem

  # <thf_annotated> ::= thf(<name>,<formula_role>,<thf_formula><annotations>).
  # <name>          ::= <atomic_word> | <integer>
  @role_names %{
    "axiom" => :axiom,
    "hypothesis" => :hypothesis,
    "definition" => :definition,
    "assumption" => :assumption,
    "lemma" => :lemma,
    "theorem" => :theorem,
    "corollary" => :corollary,
    "conjecture" => :conjecture,
    "negated_conjecture" => :negated_conjecture,
    "plain" => :plain,
    "type" => :type,
    "interpretation" => :interpretation,
    "unknown" => :unknown
  }

  defp process_tokens([], problem), do: {:ok, problem}

  defp process_tokens(
         [
           {:keyword, :thf, _},
           {:lparen, _, _},
           {name_kind, name, _},
           {:comma, _, _} | rest
         ],
         problem
       )
       when name_kind in [:atom, :distinct, :distinct_object, :integer] do
    with {:ok, {role, rest_after_role}} <- extract_role(rest),
         {:ok, formula_tokens, remaining_tokens} <- extract_formula(rest_after_role),
         {:ok, new_problem} <- handle_thf_role(role, name, formula_tokens, problem) do
      process_tokens(remaining_tokens, new_problem)
    end
  end

  defp process_tokens([{token_type, value, _offset} | _], _problem) do
    {:error, "Unexpected token: '#{value}' (#{inspect(token_type)})"}
  end

  # <formula_role> ::= <lower_word> | <lower_word>-<general_term>
  # The optional sub-role carries no logical content and is skipped.
  defp extract_role([{:atom, role, _} | rest]) do
    with {:ok, rest_after_suffix} <- skip_to_entry_comma(rest, 0) do
      {:ok, {Map.get(@role_names, role, :plain), rest_after_suffix}}
    end
  end

  defp extract_role(tokens) do
    {:error, "Syntax Error: expected a formula role, found #{inspect(Enum.take(tokens, 1))}"}
  end

  defp handle_thf_role(:type, _name, formula_tokens, problem) do
    with {:ok, {entry_name, type_struct}} <- parse_type_decl(formula_tokens) do
      {:ok, %{problem | types: Map.put(problem.types, entry_name, type_struct)}}
    end
  end

  defp handle_thf_role(role, name, formula_tokens, problem) do
    ctx = build_context(problem)

    with {:ok, term_id} <- Parser.parse_tokens(formula_tokens, ctx: ctx),
         {:ok, new_problem} <- update_problem_statements(problem, role, name, term_id) do
      {:ok, new_problem}
    else
      {:error, reason} -> {:error, "Failed to parse formula '#{name}': #{reason}"}
    end
  end

  # --- Problem Struct Updaters ---

  defp update_problem_statements(problem, :definition, name, term_id) do
    with {:ok, equality(lhs, rhs)} <- TF.get_term(term_id),
         {:ok, %Term{head: decl}} <- TF.get_term(lhs) do
      if match?(%Declaration{kind: :co}, decl) do
        {:ok, %{problem | definitions: Map.put(problem.definitions, decl, rhs)}}
      else
        update_problem_statements(problem, :axiom, name, term_id)
      end
    else
      {:ok, _} -> {:error, "Invalid LHS in definition."}
      _ -> {:error, "Definition is not a valid equation."}
    end
  end

  defp update_problem_statements(problem, role, name, term_id)
       when role in [:axiom, :hypothesis, :lemma, :assumption, :theorem, :corollary] do
    {:ok, %{problem | axioms: problem.axioms ++ [{name, term_id}]}}
  end

  defp update_problem_statements(problem, :conjecture, name, term_id) do
    {:ok, %{problem | conjecture: {name, term_id}}}
  end

  defp update_problem_statements(problem, :negated_conjecture, name, term_id) do
    {:ok, %{problem | axioms: problem.axioms ++ [{name, term_id}]}}
  end

  defp update_problem_statements(problem, _role, _name, _term_id), do: {:ok, problem}

  # Splits off the <thf_formula>, discarding the optional <annotations>
  # (`,<source><optional_info>`) that may follow it.
  defp extract_formula(tokens), do: split_at_entry_end(tokens, 0, [])

  defp split_at_entry_end([{:rparen, _, _}, {:dot, _, _} | rest], 0, acc),
    do: {:ok, Enum.reverse(acc), rest}

  defp split_at_entry_end([{:comma, _, _} | rest], 0, acc) do
    with {:ok, remaining} <- skip_to_entry_end(rest, 0) do
      {:ok, Enum.reverse(acc), remaining}
    end
  end

  defp split_at_entry_end([], _depth, _acc) do
    {:error, "Unexpected end of file. Missing ' thf( ... ). ' closing sequence."}
  end

  defp split_at_entry_end([{open, _, _} = t | rest], depth, acc)
       when open in [:lparen, :lbracket],
       do: split_at_entry_end(rest, depth + 1, [t | acc])

  defp split_at_entry_end([{close, _, _} = t | rest], depth, acc)
       when close in [:rparen, :rbracket],
       do: split_at_entry_end(rest, depth - 1, [t | acc])

  defp split_at_entry_end([t | rest], depth, acc),
    do: split_at_entry_end(rest, depth, [t | acc])

  # Discards tokens up to (and including) the comma ending the current field.
  defp skip_to_entry_comma([{:comma, _, _} | rest], 0), do: {:ok, rest}

  defp skip_to_entry_comma([], _depth),
    do: {:error, "Unexpected end of file inside a ' thf( ... ). ' entry."}

  defp skip_to_entry_comma([{open, _, _} | rest], depth) when open in [:lparen, :lbracket],
    do: skip_to_entry_comma(rest, depth + 1)

  defp skip_to_entry_comma([{close, _, _} | rest], depth) when close in [:rparen, :rbracket],
    do: skip_to_entry_comma(rest, depth - 1)

  defp skip_to_entry_comma([_ | rest], depth), do: skip_to_entry_comma(rest, depth)

  # Discards tokens up to (and including) the ' ). ' closing the current entry.
  defp skip_to_entry_end([{:rparen, _, _}, {:dot, _, _} | rest], 0), do: {:ok, rest}

  defp skip_to_entry_end([], _depth),
    do: {:error, "Unexpected end of file. Missing ' thf( ... ). ' closing sequence."}

  defp skip_to_entry_end([{open, _, _} | rest], depth) when open in [:lparen, :lbracket],
    do: skip_to_entry_end(rest, depth + 1)

  defp skip_to_entry_end([{close, _, _} | rest], depth) when close in [:rparen, :rbracket],
    do: skip_to_entry_end(rest, depth - 1)

  defp skip_to_entry_end([_ | rest], depth), do: skip_to_entry_end(rest, depth)

  # --- Type & Context Helpers ---

  # <thf_atom_typing> ::= <typeable_atom> : <thf_top_level_type>
  #                     | (<thf_atom_typing>)
  # The parenthesised form may be nested arbitrarily deep.
  defp parse_type_decl([{:lparen, _, _} | rest] = tokens) do
    case List.pop_at(rest, -1) do
      {{:rparen, _, _}, inner} -> parse_type_decl(inner)
      _ -> {:error, "Syntax Error: unbalanced parentheses in #{inspect(tokens)}."}
    end
  end

  defp parse_type_decl([{atom_or_distinct, name, _}, {:colon, _, _} | type_tokens])
       when atom_or_distinct in [:atom, :distinct, :distinct_object] do
    if match?([{:system, "$tType", _}], type_tokens) do
      {:ok, {name, :base_type}}
    else
      case Parser.parse_type_scheme_tokens(type_tokens) do
        {:ok, {scheme, []}} -> {:ok, {name, scheme}}
        {:ok, {_, unparsed}} -> {:error, "Could not parse #{inspect(unparsed)} to type."}
        {:error, reason} -> {:error, reason}
      end
    end
  end

  defp parse_type_decl(tokens) do
    {:error, "Syntax Error: #{inspect(tokens)} is not a valid type declaration."}
  end

  defp build_context(problem) do
    ctx_with_types =
      Enum.reduce(problem.types, Context.new(), fn
        {_name, :base_type}, ctx -> ctx
        {name, type_struct}, ctx -> Context.put_const(ctx, name, type_struct)
      end)

    Enum.reduce(problem.definitions, ctx_with_types, fn
      {%Declaration{name: name, type: type}, _rhs_term_id}, ctx ->
        case Context.get_const_scheme(ctx, name) do
          nil -> Context.put_const(ctx, name, TypeScheme.generalize(type, MapSet.new()))
          _scheme -> ctx
        end
    end)
  end

  defp inline_includes(tokens, visited) do
    do_inline(tokens, visited, [], [])
  end

  defp do_inline([], _visited, tok_acc, path_acc),
    do: {:ok, Enum.reverse(tok_acc), Enum.reverse(path_acc)}

  # <include> ::= include(<file_name><formula_selection>).
  defp do_inline(
         [
           {:keyword, :include, _},
           {:lparen, _, _},
           {:distinct, file_path, _} | after_file_name
         ],
         visited,
         tok_acc,
         path_acc
       ) do
    if MapSet.member?(visited, file_path) do
      {:error, "TPTP Parser Error: Cyclic import of #{file_path}"}
    else
      new_visited = MapSet.put(visited, file_path)

      with {:ok, {selection, rest}} <- parse_formula_selection(after_file_name),
           {:ok, resolved_path} <- resolve_path(file_path, :tptp_relative),
           {:ok, content} <- File.read(resolved_path),
           {:ok, file_tokens, "", _, _, _} <- Lexer.tokenize(content),
           {:ok, inlined_tokens, sub_paths} <- do_inline(file_tokens, new_visited, [], []),
           {:ok, selected_tokens} <- select_formulas(inlined_tokens, selection) do
        new_tok_acc = Enum.reverse(selected_tokens) ++ tok_acc
        new_path_acc = Enum.reverse([resolved_path | sub_paths]) ++ path_acc
        do_inline(rest, new_visited, new_tok_acc, new_path_acc)
      else
        {:ok, _, unparsed, _, _, _} ->
          {:error, "Lexer failed to tokenize included file #{file_path}. Unparsed: #{unparsed}"}

        {:error, reason} when is_binary(reason) ->
          {:error, reason}

        {:error, posix} ->
          {:error, "Could not read included file #{file_path}: #{inspect(posix)}"}
      end
    end
  end

  defp do_inline([token | rest], visited, tok_acc, path_acc),
    do: do_inline(rest, visited, [token | tok_acc], path_acc)

  # <formula_selection> ::= ,[<name_list>] | <nothing>
  defp parse_formula_selection([{:rparen, _, _}, {:dot, _, _} | rest]), do: {:ok, {:all, rest}}

  defp parse_formula_selection([{:comma, _, _}, {:lbracket, _, _} | rest]),
    do: parse_name_list(rest, [])

  defp parse_formula_selection(tokens),
    do: {:error, "Syntax Error: malformed include directive at #{inspect(Enum.take(tokens, 3))}"}

  defp parse_name_list([{:rbracket, _, _}, {:rparen, _, _}, {:dot, _, _} | rest], acc),
    do: {:ok, {Enum.reverse(acc), rest}}

  defp parse_name_list([{kind, name, _}, {:comma, _, _} | rest], acc)
       when kind in [:atom, :distinct, :distinct_object, :integer],
       do: parse_name_list(rest, [name | acc])

  defp parse_name_list([{kind, name, _} | rest], acc)
       when kind in [:atom, :distinct, :distinct_object, :integer],
       do: parse_name_list(rest, [name | acc])

  defp parse_name_list(tokens, _acc),
    do: {:error, "Syntax Error: malformed include selection at #{inspect(Enum.take(tokens, 3))}"}

  # Keeps only those statements of an included file whose <name> was selected.
  defp select_formulas(tokens, :all), do: {:ok, tokens}

  defp select_formulas(tokens, names), do: select_statements(tokens, names, [])

  defp select_statements([], _names, acc), do: {:ok, Enum.reverse(acc)}

  defp select_statements([_, _, {_kind, name, _} | _] = tokens, names, acc) do
    with {:ok, statement, rest} <- take_statement(tokens, 0, []) do
      if name in names,
        do: select_statements(rest, names, Enum.reverse(statement, acc)),
        else: select_statements(rest, names, acc)
    end
  end

  defp select_statements(tokens, _names, _acc),
    do: {:error, "Syntax Error: malformed statement in included file: #{inspect(tokens)}"}

  defp take_statement([{:rparen, _, _} = r, {:dot, _, _} = d | rest], 1, acc),
    do: {:ok, Enum.reverse([d, r | acc]), rest}

  defp take_statement([], _depth, _acc),
    do: {:error, "Unexpected end of file inside an included statement."}

  defp take_statement([{open, _, _} = t | rest], depth, acc) when open in [:lparen, :lbracket],
    do: take_statement(rest, depth + 1, [t | acc])

  defp take_statement([{close, _, _} = t | rest], depth, acc) when close in [:rparen, :rbracket],
    do: take_statement(rest, depth - 1, [t | acc])

  defp take_statement([t | rest], depth, acc), do: take_statement(rest, depth, [t | acc])

  ##############################################################################
  # UNPARSING: TPTP THF PROBLEM FORMAT
  ##############################################################################

  @doc """
  Converts a HOL term or a `ShotDs.Data.Problem` struct to a TPTP problem
  string with `thf(...)` annotations.
  Returns `{:ok, tptp_str}` or `{:error, reason}`.
  """
  @spec unparse_problem(Term.term_id() | Problem.t()) ::
          {:ok, String.t()} | TF.lookup_error_t() | {:error, term()}
  def unparse_problem(term_id) when is_integer(term_id) do
    with {:ok, formula_str} <- Parser.unparse(term_id) do
      {:ok, "thf(f1, conjecture,\n    #{formula_str})."}
    end
  end

  def unparse_problem(%Problem{} = problem) do
    try do
      {:ok, build_problem_string(problem)}
    rescue
      e in ArgumentError -> {:error, e.message}
    end
  end

  # --- Problem string builder ---

  defp build_problem_string(%Problem{types: types} = problem) do
    # `α > c` and `c @ α` share a representation, so the unparser needs to know
    # which names were declared with a type-constructor kind (`$tType > …`).
    Parser.with_type_constructors(type_constructor_names(types), fn ->
      do_build_problem_string(problem)
    end)
  end

  defp type_constructor_names(types) do
    for {name, decl} <- types, type_constructor_kind?(decl), do: String.to_atom(name)
  end

  defp type_constructor_kind?(%TypeScheme{body: body}), do: type_constructor_kind?(body)
  defp type_constructor_kind?(%Type{goal: :tType, args: [_ | _]}), do: true
  defp type_constructor_kind?(_decl), do: false

  defp do_build_problem_string(%Problem{
         types: types,
         definitions: defs,
         axioms: axioms,
         conjecture: conj
       }) do
    types_part =
      Enum.map_join(types, "\n", fn
        {name, :base_type} ->
          "thf(#{tptp_atom(name)}, type,\n    #{tptp_atom(name)}: $tType)."

        {name, %TypeScheme{} = scheme} ->
          "thf(#{tptp_atom(name)}, type,\n    #{tptp_atom(name)}: #{Parser.unparse_type_scheme(scheme)})."

        {name, %Type{} = type} ->
          "thf(#{tptp_atom(name)}, type,\n    #{tptp_atom(name)}: #{Parser.unparse_type(type)})."
      end)

    defs_part =
      Enum.map_join(defs, "\n", fn {%Declaration{name: name}, rhs_id} ->
        def_name = tptp_def_annotation(name)
        "thf(#{def_name}, definition,\n    #{tptp_atom(name)} = #{Parser.unparse!(rhs_id)})."
      end)

    axioms_part =
      Enum.map_join(axioms, "\n", fn {name, term_id} ->
        "thf(#{tptp_atom(name)}, axiom,\n    #{unparse_top_level_formula(term_id)})."
      end)

    conj_part =
      case conj do
        nil ->
          nil

        {name, term_id} ->
          "thf(#{tptp_atom(name)}, conjecture,\n    #{unparse_top_level_formula(term_id)})."
      end

    [types_part, defs_part, axioms_part, conj_part]
    |> Enum.reject(&(is_nil(&1) or &1 == ""))
    |> Enum.join("\n\n")
  end

  defp tptp_atom(name) when is_binary(name) do
    if Regex.match?(~r/^[a-z][a-zA-Z0-9_]*$/, name),
      do: name,
      else: "'#{String.replace(name, "'", "\\'")}'"
  end

  defp tptp_atom(ref) when is_reference(ref),
    do: "c#{:erlang.phash2(ref) |> Integer.to_string(36)}"

  # Renders a top-level formula (axiom or conjecture), implicitly universally
  # quantifying over the term's free variables so the output is a valid,
  # self-contained TPTP THF formula.
  defp unparse_top_level_formula(term_id) do
    term = TF.get_term!(term_id)
    body = Parser.unparse!(term_id)

    case Enum.sort_by(MapSet.to_list(term.fvars), &fvar_sort_key/1) do
      [] ->
        body

      fvars ->
        binders =
          Enum.map_join(fvars, ", ", fn %Declaration{name: name, type: type} ->
            "#{fvar_binder_name(name)}: #{Parser.unparse_type(type)}"
          end)

        "![#{binders}]: (#{body})"
    end
  end

  defp fvar_binder_name(name) when is_binary(name), do: name

  defp fvar_binder_name(ref) when is_reference(ref),
    do: "V#{:erlang.phash2(ref) |> Integer.to_string(36)}"

  defp fvar_sort_key(%Declaration{name: name}) when is_binary(name), do: {0, name}

  defp fvar_sort_key(%Declaration{name: name}) when is_reference(name),
    do: {1, :erlang.phash2(name)}

  defp tptp_def_annotation(name) when is_binary(name) do
    if Regex.match?(~r/^[a-z][a-zA-Z0-9_]*$/, name),
      do: name <> "_def",
      else: "def_#{:erlang.phash2(name) |> Integer.to_string(36)}"
  end

  defp tptp_def_annotation(ref) when is_reference(ref),
    do: "def_#{:erlang.phash2(ref) |> Integer.to_string(36)}"
end

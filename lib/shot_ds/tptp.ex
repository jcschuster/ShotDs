defmodule ShotDs.Tptp do
  @moduledoc """
  Contains utility to parse files from the TPTP problem library
  (https://tptp.org/TPTP/) as well as custom files in TPTP's TH0 syntax.

  For reference, the TH0 language is defined in
  https://doi.org/10.1007/s10817-017-9407-7.
  """

  alias ShotDs.Data.{Context, Problem, Declaration}
  alias ShotDs.Parser
  alias ShotDs.Util.Lexer
  alias ShotDs.TermFactory, as: TF

  @doc """
  Parses a TPTP file in TH0 syntax at the provided path into a
  `ShotDs.Data.Problem` struct. Returns `{:error, reason}` if a problem
  occurred.

  This function serves two purposes: parsing a file from the TPTP problem
  library (https://tptp.org/TPTP/) or a custom problem file given by the user.

  `is_tptp` indicates whether it is a file from the TPTP problem library and
  can be accessed via the environment variable `TPTP_ROOT` pointing to the root
  directory of the TPTP library.
  """
  @spec parse_tptp_file(String.t(), boolean()) :: {:ok, Problem.t()} | {:error, String.t()}
  def parse_tptp_file(problem, is_tptp \\ true) when is_binary(problem) do
    with {:ok, path} <- resolve_path(problem, is_tptp),
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
  Parses a string representing full a problem file in TPTP's TH0 syntax into a
  `ShotDs.Data.Problem` struct.

  The parsing of `content` only supports including files from the TPTP problem
  library. If such includes are present, make sure that the `TPTP_ROOT`
  environment variable is set.
  """
  @spec parse_tptp_string(String.t(), String.t()) :: {:ok, Problem.t()} | {:error, String.t()}
  def parse_tptp_string(content, path \\ "memory") when is_binary(content) and is_binary(path) do
    case Lexer.tokenize(content) do
      {:ok, tokens, "", _, _, _} ->
        process_tokens(tokens, %Problem{path: path})

      {:ok, _tokens, unparsed, _, _, _} ->
        {:error, "Lexer failed to parse entire string. Unparsed: #{unparsed}"}
    end
  end

  # --- Path Resolution Helpers ---

  defp resolve_path(problem, true = _is_tptp) do
    case System.get_env("TPTP_ROOT") do
      nil -> {:error, "TPTP Parser Error: TPTP_ROOT environment variable is not set"}
      root -> {:ok, Path.join(root, problem)}
    end
  end

  defp resolve_path(problem, false = _is_tptp), do: {:ok, problem}

  # --- Token Processing ---

  defp process_tokens([], problem), do: {:ok, problem}

  defp process_tokens(
         [
           {:keyword, :include},
           {:lparen, _},
           {:distinct, file_path},
           {:rparen, _},
           {:dot, _} | rest
         ],
         problem
       ) do
    if file_path == problem.path do
      raise "TPTP Parser Error: Cyclic import of #{file_path}"
    end

    case parse_tptp_file(file_path) do
      {:ok, included_problem} ->
        problem
        |> merge_problems(included_problem)
        |> then(&process_tokens(rest, &1))

      error ->
        error
    end
  end

  defp process_tokens(
         [
           {:keyword, :thf},
           {:lparen, _},
           {:atom, name},
           {:comma, _},
           {:role, role},
           {:comma, _} | rest
         ],
         problem
       ) do
    {formula_tokens, remaining_tokens} = extract_formula(rest)

    new_problem =
      if role == :type do
        {entry_name, type_struct} = parse_type_decl(formula_tokens)
        %{problem | types: Map.put(problem.types, entry_name, type_struct)}
      else
        ctx = build_context(problem)
        term_id = Parser.parse_tokens(formula_tokens, ctx)
        update_problem_statements(problem, role, name, term_id)
      end

    process_tokens(remaining_tokens, new_problem)
  end

  defp process_tokens([{token_type, value} | _], _problem) do
    {:error, "Unexpected token: '#{value}' (#{inspect(token_type)})"}
  end

  # --- Problem Struct Updaters ---

  defp update_problem_statements(problem, :definition, name, term_id) do
    %{problem | definitions: Map.put(problem.definitions, name, term_id)}
  end

  defp update_problem_statements(problem, role, name, term_id)
       when role in [:axiom, :hypothesis, :lemma, :assumption] do
    %{problem | axioms: problem.axioms ++ [{name, term_id}]}
  end

  defp update_problem_statements(problem, :conjecture, name, term_id) do
    %{problem | conjecture: {name, term_id}}
  end

  defp update_problem_statements(problem, _role, _name, _term_id), do: problem

  # --- Formula Extraction ---

  defp extract_formula(tokens), do: split_at_entry_end(tokens, 0, [])

  defp split_at_entry_end([{:rparen, _}, {:dot, _} | rest], 0, acc), do: {Enum.reverse(acc), rest}

  defp split_at_entry_end([], _depth, _acc) do
    raise "TPTP Parser Error: Unexpected end of file. Missing ' thf( ... ). ' closing sequence."
  end

  defp split_at_entry_end([{:lparen, _} = t | rest], depth, acc),
    do: split_at_entry_end(rest, depth + 1, [t | acc])

  defp split_at_entry_end([{:rparen, _} = t | rest], depth, acc),
    do: split_at_entry_end(rest, depth - 1, [t | acc])

  defp split_at_entry_end([t | rest], depth, acc), do: split_at_entry_end(rest, depth, [t | acc])

  # --- Type & Context Helpers ---

  defp parse_type_decl([{:atom, name}, {:colon, _} | type_tokens]) do
    if type_tokens == [{:system, "$tType"}] do
      {name, :base_type}
    else
      {type_struct, []} = Parser.parse_type_tokens(type_tokens)
      {name, type_struct}
    end
  end

  defp build_context(problem) do
    ctx_with_types =
      Enum.reduce(problem.types, Context.new(), fn
        {_name, :base_type}, ctx -> ctx
        {name, type_struct}, ctx -> Context.put_const(ctx, name, type_struct)
      end)

    Enum.reduce(problem.definitions, ctx_with_types, fn {_name, term_id}, ctx ->
      case extract_defined_constant(term_id) do
        {name, type} -> Context.put_const(ctx, name, type)
        nil -> ctx
      end
    end)
  end

  # Flattens out the nested struct lookups using 'with'
  defp extract_defined_constant(term_id) do
    term = TF.get_term(term_id)

    with %Declaration{kind: :co, name: "="} <- term.head,
         [lhs_id, _rhs_id] <- term.args,
         lhs_term = TF.get_term(lhs_id),
         %Declaration{kind: :co, name: name, type: type} <- lhs_term.head do
      {name, type}
    else
      _ -> nil
    end
  end

  defp merge_problems(main, included) do
    %{
      main
      | types: Map.merge(main.types, included.types),
        axioms: main.axioms ++ included.axioms,
        definitions: Map.merge(main.definitions, included.definitions),
        includes: main.includes ++ [included.path | included.includes]
    }
  end
end

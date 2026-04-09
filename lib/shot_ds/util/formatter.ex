defmodule ShotDs.Util.Formatter do
  @moduledoc """
  Contains functionality for formatting terms, variable names etc.
  """

  alias ShotDs.Data.{Type, Declaration, Term, Substitution, Problem}
  alias ShotDs.Stt.TermFactory, as: TF
  import ShotDs.Util.TermTraversal

  @infix_ops ["∧", "∨", "⊃", "≡", "=", "≠"]
  @prefix_ops ["¬", "Π", "Σ"]

  @doc """
  Pretty-prints the given HOL object taking the ETS cache into accout for
  recursively traversing term DAGs. This is implemented for singular types,
  declarations, terms (via ID or struct), substitutions and TPTP proof problems.
  Returns a tuple `{:ok, result}` or `{:error, reason}`.
  """
  @spec format(Type.t() | Declaration.t() | Term.t() | Substitution.t() | Problem.t(), boolean()) ::
          {:ok, String.t()} | TF.lookup_error_t() | {:error, :unknown_argument}
  def format(hol_object, hide_types \\ true)

  def format(%Type{} = t, _), do: {:ok, Kernel.to_string(t)}
  def format(%Declaration{} = d, hide_types), do: {:ok, Declaration.format(d, hide_types)}
  def format(%Term{} = t, hide_types), do: format_term(t, hide_types)
  def format(%Substitution{} = s, hide_types), do: format_substitution(s, hide_types)
  def format(%Problem{} = p, hide_types), do: format_problem(p, hide_types)
  def format(term_id, hide_types) when is_integer(term_id), do: format_term(term_id, hide_types)
  def format(_, _), do: {:error, :unknown_argument}

  @doc """
  Pretty-prints the given HOL object taking the ETS cache into accout for
  recursively traversing term DAGs. This is implemented for singular types,
  declarations, terms (via ID or struct), substitutions and TPTP proof problems.
  Raises on errors (for terms, substitutions and problems).
  """
  @spec format!(Type.t() | Declaration.t() | Term.t() | Substitution.t() | Problem.t(), boolean()) ::
          String.t()
  def format!(hol_object, hide_types \\ true)

  def format!(%Type{} = t, _), do: Kernel.to_string(t)
  def format!(%Declaration{} = d, hide_types), do: Declaration.format(d, hide_types)
  def format!(%Term{} = t, hide_types), do: format_term!(t, hide_types)
  def format!(%Substitution{} = s, hide_types), do: format_substitution!(s, hide_types)
  def format!(%Problem{} = p, hide_types), do: format_problem!(p, hide_types)
  def format!(term_id, hide_types) when is_integer(term_id), do: format_term!(term_id, hide_types)

  ##############################################################################
  # TERMS
  ##############################################################################

  @doc """
  Recursively traverses the term DAG to build a pretty-printed string
  representation with minimal bracketing. Type annotations may be enabled.

  Returns a tuple `{:ok, result}` or `{:error, reason}`.
  """
  @spec format_term(Term.term_id() | Term.t(), boolean()) ::
          {:ok, String.t()} | TF.lookup_error_t()
  def format_term(term_or_id, hide_types \\ true)

  def format_term(term_id, hide_types) when is_integer(term_id) do
    case fold_term(term_id, &build_string(&1, &2, hide_types)) do
      {:ok, {{final_str, _is_complex}, _cache}} -> {:ok, final_str}
      {:error, reason} -> {:error, reason}
    end
  end

  def format_term(%Term{id: term_id}, hide_types),
    do: format_term(term_id, hide_types)

  def format_term(_, _), do: {:error, :invalid_id}

  @doc """
  Recursively traverses the term DAG to build a pretty-printed string
  representation with minimal bracketing, raising on errors. Type annotations
  may be enabled.
  """
  @spec format_term!(Term.term_id() | Term.t(), boolean()) :: String.t()
  def format_term!(term_or_id, hide_types \\ true)

  def format_term!(term_id, hide_types) when is_integer(term_id) do
    {{final_str, _is_complex}, _cache} = fold_term!(term_id, &build_string(&1, &2, hide_types))
    final_str
  end

  def format_term!(%Term{id: term_id}, hide_types),
    do: format_term!(term_id, hide_types)

  defp build_string(%Term{bvars: bvars, head: head, type: type}, formatted_args, hide_types) do
    is_complex = bvars != [] || formatted_args != []

    core_str = format_application(head, formatted_args, hide_types)

    bvars_str = String.duplicate("λ", length(bvars))

    main = if bvars_str == "", do: core_str, else: "#{bvars_str}. #{core_str}"

    if hide_types || !is_complex do
      {main, is_complex}
    else
      {"(#{main})_#{type}", false}
    end
  end

  defp format_application(%Declaration{name: name} = head, args, hide_types) do
    head_str = Declaration.format(head, hide_types)

    wrap = fn {str, is_complex} -> if is_complex, do: "(#{str})", else: str end

    cond do
      name in @infix_ops and length(args) == 2 ->
        [a1, a2] = args
        "#{wrap.(a1)} #{head_str} #{wrap.(a2)}"

      name in @prefix_ops and length(args) == 1 ->
        [a1] = args
        "#{head_str}#{wrap.(a1)}"

      # Standard Application
      true ->
        arg_strs = Enum.map(args, wrap)
        if arg_strs == [], do: head_str, else: "#{head_str} #{Enum.join(arg_strs, " ")}"
    end
  end

  ##############################################################################
  # SUBSTITUTIONS
  ##############################################################################

  @doc """
  Pretty-prints a substitution. Returns a tuple `{:ok, result}` or
  `{:error, reason}`.
  """
  @spec format_substitution(Substitution.t(), boolean()) ::
          {:ok, String.t()} | TF.lookup_error_t()
  def format_substitution(%Substitution{fvar: fvar, term_id: term_id}, hide_types \\ true) do
    with {:ok, formatted_term} <- format_term(term_id, hide_types),
         do: "#{formatted_term} / #{Declaration.format(fvar, hide_types)}"
  end

  @doc """
  Pretty-prints a substitution, raising on errors.
  """
  @spec format_substitution!(Substitution.t(), boolean()) :: String.t()
  def format_substitution!(%Substitution{fvar: fvar, term_id: term}, hide_types \\ true),
    do: "#{format_term!(term, hide_types)} / #{Declaration.format(fvar, hide_types)}"

  ##############################################################################
  # PROBLEMS
  ##############################################################################

  @doc """
  Pretty-prints a TPTP proof problem. Returns a tuple `{:ok, result}` or
  `{:error, reason}`.
  """
  @spec format_problem(Problem.t(), boolean()) :: {:ok, String.t()} | {:error, term()}
  def format_problem(%Problem{} = p, hide_types \\ true) do
    try do
      {:ok, format_problem!(p, hide_types)}
    rescue
      e in ArgumentError ->
        {:error, e.message}
    end
  end

  @doc """
  Pretty-prints a TPTP proof problem, raising on errors.
  """
  @spec format_problem!(Problem.t(), boolean()) :: String.t()
  def format_problem!(
        %Problem{
          path: path,
          includes: includes,
          types: types,
          definitions: defs,
          axioms: axioms,
          conjecture: conjecture
        },
        hide_types \\ true
      ) do
    name_string = "Problem " <> if path in ["", "memory"], do: "<unnamed>", else: path

    includes_string =
      if Enum.empty?(includes) do
        ""
      else
        "\nincludes: " <> Enum.join(includes, ", ")
      end

    types_string =
      if Enum.empty?(types) do
        ""
      else
        "\nTypes: " <>
          Enum.map_join(types, ", ", fn
            {name, :base_type} -> "#{name} (base type)"
            {name, type} -> "#{name}::#{type}"
          end)
      end

    defs_string =
      if Enum.empty?(defs) do
        ""
      else
        "\nDefinitions:\n\t" <>
          Enum.map_join(defs, "\n\t", fn {decl, term_id} ->
            "#{decl} := #{format_term!(term_id, hide_types)}"
          end)
      end

    axioms_string =
      if Enum.empty?(axioms) do
        ""
      else
        "\nAxioms:\n\t" <>
          Enum.map_join(axioms, "\n\t", fn {name, term_id} ->
            "#{name}: #{format_term!(term_id, hide_types)}"
          end)
      end

    conjecture_string =
      case conjecture do
        nil -> "\nNo conjecture provided"
        {name, term} -> "\nConjecture #{name}: #{format_term!(term, hide_types)}"
      end

    "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n" <>
      name_string <>
      includes_string <>
      types_string <>
      defs_string <>
      axioms_string <>
      conjecture_string <>
      "\n%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"
  end

  ##############################################################################
  # REFERENCES
  ##############################################################################

  @doc """
  Shortens Erlang references by hashing it and converting it to base 36 for
  display purposes.

  ## Example:

      iex> make_ref() |> short_ref
      "1PO9GZ"
  """
  @spec short_ref(reference()) :: String.t()
  def short_ref(ref) when is_reference(ref) do
    short = ref |> :erlang.phash2() |> Integer.to_string(36)
    "#{short}"
  end
end

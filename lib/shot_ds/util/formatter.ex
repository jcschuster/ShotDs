defmodule ShotDs.Util.Formatter do
  @moduledoc """
  Contains functionality for formatting terms, variable names etc.
  """

  alias ShotDs.Data.{Type, Declaration, Term, Substitution}
  import ShotDs.Util.TermTraversal

  #############################################################################
  # TERMS
  #############################################################################

  @infix_ops ["∧", "∨", "⊃", "≡", "=", "≠"]
  @prefix_ops ["¬", "Π", "Σ"]

  @doc """
  Pretty-prints the given HOL object taking the ETS cache into accout for
  recursively traversing term DAGs. This is implemented for singular types,
  declarations, terms and substitutions.
  """
  @spec format(Type.t() | Declaration.t() | Term.t() | Substitution.t(), boolean()) :: String.t()
  def format(hol_object, hide_types \\ false)

  def format(%Type{} = t, false), do: Kernel.to_string(t)
  def format(%Declaration{} = d, hide_types), do: Declaration.format(d, hide_types)
  def format(%Term{} = t, hide_types), do: format_term(t, hide_types)
  def format(%Substitution{} = s, hide_types), do: format_substitution(s, hide_types)

  @doc """
  Recursively traverses the term DAG to build a pretty-printed string
  representation with minimal bracketing. Type annotations can be hidden.
  """
  @spec format_term(Term.term_id() | Term.t(), boolean()) :: String.t()
  def format_term(term_or_id, hide_types \\ false)

  def format_term(term_id, hide_types) when is_binary(term_id) do
    {final_str, _is_complex} = fold_term(term_id, &build_string(&1, &2, hide_types))

    final_str
  end

  def format_term(%Term{id: term_id}, hide_types),
    do: format_term(term_id, hide_types)

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

  #############################################################################
  # SUBSTITUTIONS
  #############################################################################

  @doc """
  Pretty-prints a substitution.
  """
  @spec format_substitution(Substitution.t(), boolean()) :: String.t()
  def format_substitution(%Substitution{fvar: fvar, term_id: term}, hide_types \\ false),
    do: "#{format_term(term, hide_types)} / #{Declaration.format(fvar, hide_types)}"

  #############################################################################
  # REFERENCES
  #############################################################################

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

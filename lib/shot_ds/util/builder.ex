defmodule ShotDs.Util.Builder do
  @moduledoc """
  Contains expressive functions as shorthand notation for the construction of
  abstractions and applications.
  """

  alias ShotDs.Data.{Type, Declaration, Term}
  alias ShotDs.TermFactory, as: TF
  alias ShotDs.Semantics

  @doc """
  Constructs a lambda abstraction over a list of variable types. Temporary
  fresh free variables will be generated corresponding to the types. Passes the
  generated variable term IDs to the provided `body_fn`. The arity of `body_fn`
  must correspond to the number of given variables.

  ## Examples:

      iex> lambda(Type.new(:i), fn x -> ... end)

      iex> lambda([Type.new(:o), Type.new(:o), Type.new(:o)], fn x, y, z -> ... end)
  """
  @spec lambda([Type.t()] | Type.t(), (... -> Term.term_id())) :: Term.term_id()
  def lambda(var_types, body_fn) when is_function(body_fn) do
    decls =
      var_types
      |> List.wrap()
      |> List.flatten()
      |> Enum.map(&Declaration.fresh_var/1)

    var_terms = Enum.map(decls, &TF.make_term/1)
    body_term_id = apply(body_fn, var_terms)
    List.foldr(decls, body_term_id, &Semantics.make_abstr_term(&2, &1))
  end

  @doc """
  Applies a term to a single argument term or list of argument terms.
  """
  @spec app(Term.term_id(), [Term.term_id()] | Term.term_id()) :: Term.term_id()
  def app(head_id, arg_ids) when is_binary(head_id) and is_list(arg_ids) do
    Semantics.fold_apply(head_id, arg_ids)
  end

  def app(head_id, arg_id) when is_binary(head_id) and is_binary(arg_id) do
    Semantics.make_appl_term(head_id, arg_id)
  end
end

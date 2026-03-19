# credo:disable-for-this-file
defmodule ShotDs.Hol.Equality do
  @moduledoc """
  Provides various terms constructors for different notions of equality. This
  includes variants of Leibniz equality, Andrews equality and extensional
  equality.
  """

  alias ShotDs.Data.{Type, Term}
  import ShotDs.Hol.{Definitions, Dsl}
  import ShotDs.Util.Builder

  @typedoc """
  The connective to use for Leibniz equality.

  Can be one of `:equiv` (logical equivalence), `:imp` (logical implication) or
  `:conv_imp` (converse of logical implication).
  """
  @type connective_t() :: :equiv | :imp | :conv_imp

  @doc """
  Constructor for Leibniz equality on the given type, which defines equality by
  stating that both arguments share the same properties. Generates an
  abstraction which can be applied to two arguments.

  # Examples

      iex> leibniz_equality(type_i(), equivalent_term()) == parse("^[X:$i, Y:$i]: ![P:$i>$o]: P @ X <=> P @ Y")
      true

      iex> leibniz_equality(type_i(), implied_by_term()) == parse("^[X:$i, Y:$i]: ![P:$i>$o]: P @ X <= P @ Y")
      true
  """
  @spec leibniz_equality(Type.t(), connective_t()) :: Term.term_id()
  def leibniz_equality(type, connective \\ :equiv)

  def leibniz_equality(%Type{} = type, :equiv), do: mk_leibniz_equality(type, equivalent_term())

  def leibniz_equality(%Type{} = type, :imp), do: mk_leibniz_equality(type, implies_term())

  def leibniz_equality(%Type{} = type, :conv_imp),
    do: mk_leibniz_equality(type, implied_by_term())

  defp mk_leibniz_equality(type, connective) do
    lambda([type, type], fn x, y ->
      forall(Type.new(:o, type), fn p ->
        app(connective, [app(p, x), app(p, y)])
      end)
    end)
  end

  @doc """
  Constructor for Andrews equality on the given type, which defines equality by
  stating that both arguments share all reflexive relations. Generates an
  abstraction which can be applied to two arguments.

  # Example

      iex> andrews_equality(type_i()) == parse("^[X:$i, Y:$i]: ![Q:$i>$i>$o]: ((![Z:$i]: Q @ Z @ Z) => Q @ X @ Y)")
      true
  """
  @spec andrews_equality(Type.t()) :: Term.term_id()
  def andrews_equality(%Type{} = type) do
    lambda([type, type], fn x, y ->
      forall(Type.new(:o, [type, type]), fn q ->
        forall(type, fn z -> app(q, [z, z]) end) ~> app(q, [x, y])
      end)
    end)
  end

  @doc """
  Constructor for extensional equality on the given function type, which
  defines equality by equality of the extensions. Generates an abstraction
  which can be applied to two arguments.

  # Example

      iex> extensional_equality(type_ii()) == parse("^[X:$i>i, Y:$i>i]: ![Z:$i]: X @ Z = Y @ Z")
      true
  """
  def extensional_equality(%Type{args: [at | _]} = type) do
    lambda([type, type], fn x, y ->
      forall(at, fn z -> eq(app(x, z), app(y, z)) end)
    end)
  end

  def extensional_equality(type) do
    raise "ArgumentError: type for extensional equality must be a function type. Got #{inspect(type)} instead."
  end
end


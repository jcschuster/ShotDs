defmodule ShotDs.Data.Type do
  @moduledoc """
  Provides a data structure for Church's simple types.

  The protocol `String.Chars` is implemented.

  ## Examples

      iex> o = Type.new(:o)
      %ShotDs.Data.Type{goal: :o, args: []}

      iex> io = Type.new(:o, :i)
      %ShotDs.Data.Type{goal: :o, args: [%ShotDs.Data.Type{goal: :i, args: []}]}

      iex> Type.new(io, [o, :o])
      %ShotDs.Data.Type{
        goal: :o,
        args: [
          %ShotDs.Data.Type{goal: :i, args: []},
          %ShotDs.Data.Type{goal: :o, args: []},
          %ShotDs.Data.Type{goal: :o, args: []}
        ]
      }
  """

  @enforce_keys [:goal]
  defstruct [:goal, args: []]

  @typedoc """
  The type of a basic type.

  A basic type is identified as an atom (concrete type) or a reference (type
  variable).
  """
  @type type_id() :: atom() | reference()

  @typedoc """
  The type of a simple type.

  The goal can be a concrete name for the type like `:i` or `:o` or a reference
  denoting a type variable. The arguments of a type are a list of simple types.

  Note that this is an uncurried representation of higher-order types.
  """
  @type t :: %__MODULE__{goal: type_id(), args: [t()]}

  @doc """
  Creates a new simple type. Optionally, a list of arguments can be specified.

  Behaves as identity function on a single argument representing a simple type.
  """
  @spec new(type_id() | t(), type_id() | t() | [type_id() | t()]) :: t()
  def new(goal, args \\ [])

  def new(goal, args) when is_reference(goal) or is_atom(goal) do
    %__MODULE__{goal: goal, args: normalize_args(args)}
  end

  def new(%__MODULE__{goal: goal, args: args1}, args2) do
    %__MODULE__{goal: goal, args: args1 ++ normalize_args(args2)}
  end

  @doc """
  Creates a fresh variable for a simple type using Erlang references.
  """
  @spec fresh_type_var() :: t()
  def fresh_type_var(), do: new(make_ref())

  @doc """
  Checks whether the given type or type identifier is a type variable.
  """
  @spec is_type_var(t() | type_id()) :: boolean()
  def is_type_var(%__MODULE__{goal: g, args: []}) when is_reference(g), do: true
  def is_type_var(type) when is_reference(type), do: true
  def is_type_var(_), do: false

  defp normalize_args(args) do
    args
    |> List.wrap()
    |> List.flatten()
    |> Enum.map(&new/1)
  end
end

defimpl String.Chars, for: ShotDs.Data.Type do
  @delimiter ">"

  def to_string(%{goal: goal, args: []}), do: goal_to_str(goal)

  def to_string(type) do
    type
    |> to_string_inner()
    |> String.slice(1..-2//1)
  end

  defp to_string_inner(%{goal: goal, args: args}) do
    goal_str = goal_to_str(goal)

    case Enum.map_join(args, @delimiter, &to_string_inner/1) do
      "" -> goal_str
      args_str -> "(#{args_str <> @delimiter <> goal_str})"
    end
  end

  defp goal_to_str(goal) when is_atom(goal), do: Atom.to_string(goal)

  defp goal_to_str(goal) when is_reference(goal),
    do: "T[#{ShotDs.Util.Formatter.short_ref(goal)}]"
end

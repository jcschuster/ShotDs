defmodule ShotDs.Data.Context do
  @moduledoc """
  Represents a type environment for parsing and type checking.

  ## Examples

      iex> Context.new()
      %ShotDs.Data.Context{vars: %{}, consts: %{}, constraints: MapSet.new([])}

      iex> Context.new() |> Context.put_var("X", Type.new(:o))
      %ShotDs.Data.Context{
        vars: %{"X" => %ShotDs.Data.Type{goal: :o, args: []}},
        consts: %{},
        constraints: MapSet.new([])
      }
  """

  alias ShotDs.Data.Type

  # The use of MapSet raises opaqueness warnings which can be ignored.
  @dialyzer {:no_opaque, new: 0}

  defstruct vars: %{}, consts: %{}, constraints: MapSet.new()

  @typedoc """
  The type of the type environment.

  A context contains the type of variables (`:vars`) as a `Map` from its name
  to its type. Likewise for the constants (`:consts`). The type constraints
  are represented as a `MapSet` of `ShotDs.Data.Type` pairs.
  """
  @type t() :: %__MODULE__{
          vars: %{String.t() => Type.t()},
          consts: %{String.t() => Type.t()},
          constraints: MapSet.t({Type.t(), Type.t()})
        }

  @doc """
  Creates an empty context.
  """
  @spec new() :: t()
  def new, do: %__MODULE__{}

  @doc """
  Associates the variable with the given name with the given type in the
  context. Overwrites the old value if present.
  """
  @spec put_var(t(), String.t(), Type.t()) :: t()
  def put_var(%__MODULE__{} = ctx, name, %Type{} = type)
      when is_binary(name) or is_reference(name) do
    %{ctx | vars: Map.put(ctx.vars, name, type)}
  end

  @doc """
  Associates the constant with the given name with the given type in the
  context. Overwrites the old value if present.
  """
  def put_const(%__MODULE__{} = ctx, name, %Type{} = type)
      when is_binary(name) or is_reference(name) do
    %{ctx | consts: Map.put(ctx.consts, name, type)}
  end

  @doc """
  Adds a type constraint to the context.
  """
  @spec add_constraint(t(), Type.t(), Type.t()) :: t()
  def add_constraint(%__MODULE__{} = ctx, %Type{} = t1, %Type{} = t2) do
    %{ctx | constraints: MapSet.put(ctx.constraints, {t1, t2})}
  end

  @doc """
  Returns the type of the given name of a constant or variable. Returns `nil`
  if the name is not present in the context.
  """
  @spec get_type(t(), String.t()) :: Type.t() | nil
  def get_type(%__MODULE__{} = ctx, name) when is_binary(name) or is_reference(name) do
    Map.get(ctx.vars, name) || Map.get(ctx.consts, name)
  end
end

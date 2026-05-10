defmodule ShotDs.Data.Context do
  @moduledoc """
  Represents a type environment for parsing and type checking. Can also be
  created by using the `~e` sigil from `ShotDs.Hol.Sigils`.

  Constants are stored as `ShotDs.Data.TypeScheme`, enabling rank-1
  polymorphism: each lookup of a constant via `get_type/2` produces a fresh
  instantiation of its scheme. Constants declared with a bare monotype are
  wrapped in a trivial scheme and behave identically to a monomorphic
  declaration.

  Term variables are always stored as monotypes as Hindley-Milner only enables
  generalization in let-bindings, not in lambda-abstractions.

  ## Examples

      iex> Context.new()
      %ShotDs.Data.Context{vars: %{}, consts: %{}}

      iex> Context.new() |> Context.put_var("X", Type.new(:o))
      %ShotDs.Data.Context{
        vars: %{"X" => %ShotDs.Data.Type{goal: :o, args: []}},
        consts: %{}
      }
  """

  alias ShotDs.Data.TypeScheme
  alias ShotDs.Data.Type

  defstruct vars: %{}, consts: %{}, type_vars: %{}

  @typedoc """
  The type of the type environment.

  A context contains the type of variables (`:vars`) as a `Map` from its name
  to its type. Likewise for the constants (`:consts`). The type constraints
  are represented as a `MapSet` of `ShotDs.Data.Type` pairs.

  The `type_vars` field maps TH1 type-variable names to their `reference()`
  identifiers for use during formula-level polymorphism parsing.
  """
  @type t() :: %__MODULE__{
          vars: %{String.t() => Type.t()},
          consts: %{String.t() => TypeScheme.t()},
          type_vars: %{String.t() => reference()}
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
  @spec put_var(t(), String.t() | reference(), Type.t()) :: t()
  def put_var(%__MODULE__{} = ctx, name, %Type{} = type)
      when is_binary(name) or is_reference(name) do
    %{ctx | vars: Map.put(ctx.vars, name, type)}
  end

  @doc """
  Associates the constant with the given name with the given type or scheme.
  Bare monotypes are wrapped in a trivial scheme. Overwrites the old value if
  present.
  """
  @spec put_const(t(), String.t() | reference(), Type.t() | TypeScheme.t()) :: t()
  def put_const(ctx, name, type_or_scheme)

  def put_const(%__MODULE__{} = ctx, name, %Type{} = type)
      when is_binary(name) or is_reference(name),
      do: put_const(ctx, name, TypeScheme.mono(type))

  def put_const(%__MODULE__{} = ctx, name, %TypeScheme{} = scheme)
      when is_binary(name) or is_reference(name),
      do: %{ctx | consts: Map.put(ctx.consts, name, scheme)}

  @doc """
  Returns the scheme of the constant with the given name, or `nil` if it is not
  bound. Unlike `get_type/2`, this does not instantiate; callers that need the
  raw scheme should use this function.
  """
  @spec get_const_scheme(t(), String.t() | reference()) :: TypeScheme.t() | nil
  def get_const_scheme(%__MODULE__{} = ctx, name) when is_binary(name) or is_reference(name),
    do: Map.get(ctx.consts, name)

  @doc """
  Returns the type of the given name. For variables, the stored monotype is
  returned. For constants, the stored scheme is instantiated producing a fresh
  monotype with new type variables for each quantified parameter.

  Variables shadow constants of the same name. Returns `nil` if the name is
  not bound.

  > #### Note {:.info}
  >
  > Each call for a polymorphic constant returns a different monotype with
  > disjoint fresh type variables.
  """
  @spec get_type(t(), String.t()) :: Type.t() | nil
  def get_type(%__MODULE__{} = ctx, name) when is_binary(name) or is_reference(name) do
    Map.get(ctx.vars, name) ||
      case Map.get(ctx.consts, name) do
        %TypeScheme{} = scheme -> TypeScheme.instantiate(scheme)
        nil -> nil
      end
  end
end

defmodule ShotDs.Data.Declaration do
  @moduledoc """
  Represents free and bound variables as well as constants.
  """

  alias ShotDs.Data.Type

  @enforce_keys [:kind, :name, :type]
  defstruct [:kind, :name, :type]

  @typedoc """
  The type of a declaration. A declaration represents either a free variable, a
  bound variable or a constant.
  """
  @type t :: free_var_t() | bound_var_t() | const_t()

  @typedoc """
  Type of a free variable declaration.
  """
  @type free_var_t :: %__MODULE__{
          kind: :fv,
          name: var_name_t(),
          type: Type.t()
        }

  @typedoc """
  Type of a bound variable declaration.
  """
  @type bound_var_t :: %__MODULE__{
          kind: :bv,
          name: pos_integer(),
          type: Type.t()
        }

  @typedoc """
  Type of a constant declaration.
  """
  @type const_t :: %__MODULE__{
          kind: :co,
          name: const_name_t(),
          type: Type.t()
        }

  @typedoc """
  The name of a free variable is given as a string, a reference (indicating a
  generated fresh variable) or a positive integer representing its de Bruijn
  index.
  """
  @type var_name_t :: String.t() | reference() | pos_integer()

  @typedoc """
  The name of a constant is given as a string or a reference (indicating a
  generated fresh constant).
  """
  @type const_name_t :: String.t() | reference()

  @doc """
  Returns a struct representing a free variable of the given name and type.
  """
  @spec new_free_var(var_name_t(), Type.t()) :: free_var_t()
  def new_free_var(name, %Type{} = type)
      when is_binary(name) or is_reference(name) or is_integer(name),
      do: %__MODULE__{kind: :fv, name: name, type: type}

  @doc false
  @spec new_bound_var(pos_integer(), Type.t()) :: bound_var_t()
  def new_bound_var(name, %Type{} = type) when is_integer(name),
    do: %__MODULE__{kind: :bv, name: name, type: type}

  @doc """
  Returns a struct representing a constant of the given name and type.
  """
  @spec new_const(const_name_t(), Type.t()) :: const_t()
  def new_const(name, %Type{} = type) when is_binary(name) or is_reference(name),
    do: %__MODULE__{kind: :co, name: name, type: type}

  @doc """
  Generates a fresh variable of the given type using Erlang references to
  ensure uniqueness. Useful for γ-instantiations in tableaux.
  """
  @spec fresh_var(Type.t()) :: free_var_t()
  def fresh_var(%Type{} = t), do: new_free_var(make_ref(), t)

  @doc """
  Generates a fresh constant of the given type using Erlang references to
  ensure uniqueness. Useful for skolemization.
  """
  @spec fresh_const(Type.t()) :: const_t()
  def fresh_const(%Type{} = t), do: new_const(make_ref(), t)

  @spec format(t(), boolean()) :: String.t()
  def format(%__MODULE__{kind: kind, name: name, type: type}, hide_type \\ false) do
    prefix = if is_reference(name), do: kind_prefix(kind), else: ""
    suffix = if hide_type, do: "", else: "_#{type}"
    prefix <> format_name(name) <> suffix
  end

  defp format_name(ref) when is_reference(ref), do: "[#{ShotDs.Util.Formatter.short_ref(ref)}]"
  defp format_name(name) when is_binary(name) or is_integer(name), do: Kernel.to_string(name)

  defp kind_prefix(:fv), do: "V"
  defp kind_prefix(:co), do: "C"
end

defimpl String.Chars, for: ShotDs.Data.Declaration do
  def to_string(decl), do: ShotDs.Data.Declaration.format(decl, true)
end


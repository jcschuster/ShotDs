defmodule ShotDs.Data.TypeScheme do
  @moduledoc ~S"""
  Represents a rank-1 polymorphic type scheme:

  $$\forall \alpha_1\dots\alpha_n.\, \tau$$

  The quantified variables in `vars` are type variable references which appear
  inside the body type and are universally quantified at the outermost level
  (prenex form).

  At each use site, schemes are *instantiated* into fresh monotypes via
  `instantiate/1`, which replaces every quantified variable with a fresh
  reference. This is the mechanism that allows polymorphic constants like
  $=^\alpha$ (with scheme $\forall\alpha.\,\alpha\to\alpha\to o$) to be used at
  different types within the same formula.

  Monotypes can be lifted into trivial schemes (with empty `vars`) using
  `mono/1`.

  ## Example

      iex> alpha = make_ref()
      iex> scheme = TypeScheme.new([alpha], Type.new(alpha, alpha))
      iex> match?(%TypeScheme{vars: [^alpha]}, scheme)
      true
  """

  alias ShotDs.Data.Type

  @enforce_keys [:body]
  defstruct [:body, vars: []]

  @typedoc """
  Elixir type of a (rank-1 polymorphic) type scheme.
  """
  @type t :: %__MODULE__{vars: [Type.variable_id()], body: Type.t()}

  @doc """
  Constructs a trivial type scheme representing the given monotype.
  """
  @spec mono(Type.t()) :: t()
  def mono(%Type{} = body), do: %__MODULE__{body: body}

  @doc """
  Constructs a type scheme binding the type variables `vars` in the (possibly
  polymorphic) type `body`.
  """
  @spec new([Type.variable_id()], Type.t()) :: t()
  def new(vars, %Type{} = body) when is_list(vars),
    do: %__MODULE__{vars: vars, body: body}

  @doc """
  Instantiates the bound type variables in the given type scheme with fresh type
  variables.
  """
  @spec instantiate(t()) :: Type.t()
  def instantiate(scheme)

  def instantiate(%__MODULE__{vars: [], body: body}), do: body

  def instantiate(%__MODULE__{vars: vars, body: body}) do
    subst = Map.new(vars, fn v -> {v, make_ref()} end)
    rename(body, subst)
  end

  @doc """
  Like `instantiate/1`, but also returns the list of fresh type-variable
  references created for each bound variable (in order). Used by the TH1
  formula parser to track which fresh refs correspond to the type parameters
  so they can be unified with explicit type arguments during type erasure.
  """
  @spec instantiate_with_refs(t()) :: {Type.t(), [reference()]}
  def instantiate_with_refs(%__MODULE__{vars: [], body: body}), do: {body, []}

  def instantiate_with_refs(%__MODULE__{vars: vars, body: body}) do
    pairs = Enum.map(vars, fn v -> {v, make_ref()} end)
    subst = Map.new(pairs)
    fresh_refs = Enum.map(pairs, fn {_, r} -> r end)
    {rename(body, subst), fresh_refs}
  end

  @doc """
  Returns the set of free type variables in the scheme. This is defined as the
  set of free type variables in the body without the bound type variables.
  """
  @spec free_type_vars(t()) :: MapSet.t(Type.variable_id())
  def free_type_vars(%__MODULE__{vars: vars, body: body}),
    do: MapSet.difference(Type.free_type_vars(body), MapSet.new(vars))

  @doc """
  Generalizes a given type by binding free type variables in a scheme.
  """
  @spec generalize(Type.t(), MapSet.t(Type.variable_id())) :: t()
  def generalize(%Type{} = type, %MapSet{} = env_vars) do
    quantified =
      type
      |> Type.free_type_vars()
      |> MapSet.difference(env_vars)
      |> MapSet.to_list()

    %__MODULE__{vars: quantified, body: type}
  end

  defp rename(%Type{goal: g, args: args}, subst) do
    new_goal =
      if is_reference(g) and is_map_key(subst, g),
        do: Map.fetch!(subst, g),
        else: g

    Type.new(new_goal, Enum.map(args, &rename(&1, subst)))
  end
end

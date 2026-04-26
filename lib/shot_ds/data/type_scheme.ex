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

  @type t :: %__MODULE__{vars: [Type.variable_id()], body: Type.t()}

  def mono(%Type{} = body), do: %__MODULE__{body: body}

  def new(vars, %Type{} = body) when is_list(vars),
    do: %__MODULE__{vars: vars, body: body}

  def instantiate(%__MODULE__{vars: [], body: body}), do: body

  def instantiate(%__MODULE__{vars: vars, body: body}) do
    subst = Map.new(vars, fn v -> {v, make_ref()} end)
    rename(body, subst)
  end

  def free_type_vars(%__MODULE__{vars: vars, body: body}),
    do: MapSet.difference(Type.free_type_vars(body), MapSet.new(vars))

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

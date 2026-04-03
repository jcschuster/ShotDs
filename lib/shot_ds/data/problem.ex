defmodule ShotDs.Data.Problem do
  @moduledoc """
  A data structure to describe a (TPTP) proof problem.

  It contains meta-information about the problem (path to proof file, included
  files) as well as the problem definition which consist of:

  - A map of types which maps symbols (user types or constants) to their type

  - The definitions given by the user

  - The axioms defined by the user

  - The conjecture to be proven based on the axioms and definitions

  Note that definitions are not unfolded in the proof problem but kept as
  constants.
  """
  alias ShotDs.Data.{Type, Declaration, Term}

  defstruct path: "", includes: [], types: %{}, definitions: %{}, axioms: [], conjecture: nil

  @typedoc """
  A `Problem` is a collection holding the relevant information and
  meta-information of a problem stored in separate fields.

  The `:path` to a problem file is given as a string. This also includes the
  paths to the included files in `:includes`.

  The types are given as a map mapping symbol names (or type names) to their
  defined types (can be `:base_type` for user-defined base types).

  The definitions are given as a map from the symbol's name to the equation
  describing it. Note that the equation must first be deconstructed into the
  defined constant on the left hand side and it's definition on the right hand
  side.

  The axioms are stored as a list of pairs containing the axiom's name as
  string and term as its corresponding ID.

  The conjecture is tuple containing the conjecture's name as string and the
  conjecture itself as the term's ID. The field's value is `nil` if no
  conjecture could be found.
  """
  @type t() :: %__MODULE__{
          path: String.t(),
          includes: [String.t()],
          types: %{String.t() => :base_type | Type.t()},
          definitions: %{Declaration.t() => Term.term_id()},
          axioms: [{String.t(), Term.term_id()}],
          conjecture: {String.t(), Term.term_id()} | nil
        }
end

defimpl String.Chars, for: ShotDs.Data.Problem do
  def to_string(%{
        path: path,
        includes: includes,
        types: types,
        definitions: defs,
        axioms: axioms,
        conjecture: conjecture
      }) do
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
        "\nDepends on #{map_size(defs)} definitions: {#{Enum.map_join(defs, ", ", fn {c, _t} -> Kernel.to_string(c) end)}}"
      end

    axioms_string =
      if Enum.empty?(axioms) do
        ""
      else
        "\n#{length(axioms)} axioms: {#{Enum.map_join(axioms, ", ", fn {c, _t} -> Kernel.to_string(c) end)}}"
      end

    conjecture_string =
      case conjecture do
        nil -> "\nNo conjecture provided"
        {name, _term} -> "\nDefines conjecture: #{name}"
      end

    name_string <>
      includes_string <> types_string <> defs_string <> axioms_string <> conjecture_string
  end
end

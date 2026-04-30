defmodule ShotDs.Hol.Patterns do
  @moduledoc """
  Contains various macros for pattern matching on HOL terms.
  """

  alias ShotDs.Data.{Type, Declaration, Term}

  @o %Type{goal: :o, args: []}
  @oo %Type{goal: :o, args: [@o]}
  @ooo %Type{goal: :o, args: [@o, @o]}

  defmacro __using__(_opts) do
    quote do
      alias ShotDs.Data.{Type, Declaration, Term}
      require ShotDs.Hol.Patterns
      import ShotDs.Hol.Patterns
    end
  end

  @doc """
  Matches a term representing truth.
  """
  defmacro truth() do
    o = Macro.escape(@o)

    quote do
      %Term{bvars: [], head: %Declaration{name: "⊤", type: unquote(o)}, args: []}
    end
  end

  @doc """
  Matches a term representing falsity.
  """
  defmacro falsity() do
    o = Macro.escape(@o)

    quote do
      %Term{bvars: [], head: %Declaration{name: "⊥", type: unquote(o)}, args: []}
    end
  end

  @doc """
  Matches a term representing the negation of `term_id`.
  """
  defmacro negated(term_id) do
    oo = Macro.escape(@oo)

    quote do
      %Term{
        bvars: [],
        head: %Declaration{name: "¬", type: unquote(oo)},
        args: [unquote(term_id)]
      }
    end
  end

  @doc """
  Matches a term representing the disjunction of `p_id` and `q_id`.
  """
  defmacro disjunction(p_id, q_id) do
    ooo = Macro.escape(@ooo)

    quote do
      %Term{
        bvars: [],
        head: %Declaration{name: "∨", type: unquote(ooo)},
        args: [unquote(p_id), unquote(q_id)]
      }
    end
  end

  @doc """
  Matches a term representing the conjunction of `p_id` and `q_id`.
  """
  defmacro conjunction(p_id, q_id) do
    ooo = Macro.escape(@ooo)

    quote do
      %Term{
        bvars: [],
        head: %Declaration{name: "∧", type: unquote(ooo)},
        args: [unquote(p_id), unquote(q_id)]
      }
    end
  end

  @doc """
  Matches a term representing the implication of `p_id` and `q_id`, i.e. `p`
  implies `q`.
  """
  defmacro implication(p_id, q_id) do
    ooo = Macro.escape(@ooo)

    quote do
      %Term{
        bvars: [],
        head: %Declaration{name: "⊃", type: unquote(ooo)},
        args: [unquote(p_id), unquote(q_id)]
      }
    end
  end

  @doc """
  Matches a term representing the equivalence of `p_id` and `q_id`.
  """
  defmacro equivalence(p_id, q_id) do
    ooo = Macro.escape(@ooo)

    quote do
      %Term{
        bvars: [],
        head: %Declaration{name: "≡", type: unquote(ooo)},
        args: [unquote(p_id), unquote(q_id)]
      }
    end
  end

  @doc """
  Matches a term representing the equality of `p_id` and `q_id`.
  """
  defmacro equality(a_id, b_id) do
    quote do
      %Term{
        bvars: [],
        head: %Declaration{name: "=", type: %Type{goal: :o, args: [_, _]}},
        args: [unquote(a_id), unquote(b_id)]
      }
    end
  end

  @doc """
  Matches a term representing the equality of `p_id` and `q_id` with respect to
  their type.
  """
  defmacro typed_equality(a_id, b_id, type) do
    quote do
      %Term{
        bvars: [],
        head: %Declaration{name: "=", type: %Type{goal: :o, args: [unquote(type), unquote(type)]}},
        args: [unquote(a_id), unquote(b_id)]
      }
    end
  end

  @doc """
  Matches a term representing the universal quantification of the predicate
  `body_id`.
  """
  defmacro universal_quantification(body_id) do
    quote do
      %Term{
        bvars: [],
        head: %Declaration{name: "∀", type: %Type{goal: :o, args: [%Type{goal: :o, args: [_]}]}},
        args: [unquote(body_id)]
      }
    end
  end

  @doc """
  Matches a term representing the universal quantification of the predicate
  `body_id` with respect to the element type `type`.
  """
  defmacro typed_universal_quantification(body_id, type) do
    quote do
      %Term{
        bvars: [],
        head: %Declaration{
          name: "∀",
          type: %Type{goal: :o, args: [%Type{goal: :o, args: [unquote(type)]}]}
        },
        args: [unquote(body_id)]
      }
    end
  end

  @doc """
  Matches a term representing the universal quantification of the predicate
  `body_id`.
  """
  defmacro existential_quantification(body_id) do
    quote do
      %Term{
        bvars: [],
        head: %Declaration{name: "∃", type: %Type{goal: :o, args: [%Type{goal: :o, args: [_]}]}},
        args: [unquote(body_id)]
      }
    end
  end

  @doc """
  Matches a term representing the universal quantification of the predicate
  `body_id` with respect to the element type `type`.
  """
  defmacro typed_existential_quantification(body_id, type) do
    quote do
      %Term{
        bvars: [],
        head: %Declaration{
          name: "∃",
          type: %Type{goal: :o, args: [%Type{goal: :o, args: [unquote(type)]}]}
        },
        args: [unquote(body_id)]
      }
    end
  end
end

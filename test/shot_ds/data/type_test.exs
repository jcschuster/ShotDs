defmodule ShotDs.Data.TypeTest do
  use ExUnit.Case, async: true

  alias ShotDs.Data.Type

  test "new/2 normalizes and flattens argument lists" do
    type = Type.new(:o, [:i, Type.new(:o), [:i]])

    assert %Type{goal: :o, args: [%Type{goal: :i}, %Type{goal: :o}, %Type{goal: :i}]} = type
  end

  test "new/2 appends arguments when goal is already a type" do
    base = Type.new(:o, :i)
    extended = Type.new(base, :o)

    assert to_string(extended) == "i>o>o"
  end

  test "fresh_type_var/0 returns a type variable with no args" do
    %Type{goal: goal, args: args} = Type.fresh_type_var()

    assert is_reference(goal)
    assert args == []
  end

  test "String.Chars renders base and functional types" do
    assert to_string(Type.new(:o)) == "o"
    assert to_string(Type.new(:o, [:i, :o])) == "i>o>o"
    assert to_string(Type.new(:o, [Type.new(:i, :i), :o])) == "(i>i)>o>o"
  end

  test "String.Chars includes short marker for type variables" do
    rendered = Type.fresh_type_var() |> to_string()

    assert String.starts_with?(rendered, "T[")
    assert String.ends_with?(rendered, "]")
  end
end

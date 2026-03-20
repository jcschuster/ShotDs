defmodule ShotDs.Application do
  @moduledoc false
  use Application

  @impl true
  def start(_type, _args) do
    children = [
      ShotDs.TermPoolOwner
    ]

    opts = [strategy: :one_for_one, name: ShotDs.Supervisor]
    Supervisor.start_link(children, opts)
  end
end

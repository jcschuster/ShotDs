alias ShotDs.Stt.Semantics

beam = :code.which(Semantics)
IO.inspect(beam, label: "beam")

{:ok, {_, [{:abstract_code, {:raw_abstract_v1, forms}}]}} = :beam_lib.chunks(beam, [:abstract_code])

inst =
	Enum.find(forms, fn
		{:function, _, :instantiate, 4, _} -> true
		_ -> false
	end)

IO.inspect(inst, label: "instantiate_abstract")

import graphs.iso

lemma mor_ext {G H : graph} (α : G ↦ H) (β : G ↦ H) (hv : α.vertex_map = β.vertex_map) (he : α.edge_map = β.edge_map) : α = β :=
begin
  cases α,
  cases β,
  rw morphism.mk.inj_eq,
  exact ⟨hv, he⟩,
end
import graphs.ext

lemma eq_mor_eq_vmap {G H : graph} (α : G ↦ H) (β : G ↦ H) (hyp : α = β) : α.vertex_map = β.vertex_map :=
begin
  cases α,
  cases β,
  rw morphism.mk.inj_eq at hyp,
  exact hyp.1,
end

lemma eq_mor_eq_emap {G H : graph} (α : G ↦ H) (β : G ↦ H) (hyp : α = β) : α.edge_map = β.edge_map :=
begin
  cases α,
  cases β,
  rw morphism.mk.inj_eq at hyp,
  exact hyp.2,
end
import graphs.definitions

def compose {G H K : graph} (β : H ↦ K) (α : G ↦ H) : G ↦ K :=
  morphism.mk (β.vertex_map ∘ α.vertex_map) (β.edge_map ∘ α.edge_map) (by exact compatability α β)

infix `⊚`:80 := compose

lemma mor_assoc {G H K L : graph} (α : G ↦ H) (β : H ↦ K) (γ : K ↦ L) : γ ⊚ (β ⊚ α) = (γ ⊚ β) ⊚ α :=
begin
  refl,
end
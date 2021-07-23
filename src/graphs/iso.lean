import graphs.id

def 𝕀 (G : graph) : G ↦ G :=
  morphism.mk (id) (id) (by exact id_compatability G)

def isomorphism {G H : graph} (α : G ↦ H) : Prop :=
  ∃ β : H ↦ G, α ⊚ β = 𝕀 H ∧ β ⊚ α = 𝕀 G


lemma id_is_iso (G : graph) : isomorphism (𝕀 G) :=
begin
  use 𝕀 G,
  split,
  refl,
  refl,
end
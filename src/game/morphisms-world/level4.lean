import graphs.id

/-
Now we can define the identity morphism.
-/

def 𝕀 (G : graph) : G ↦ G :=
  morphism.mk (id) (id) (by exact id_compatability G)

/-
Next we turn our attention to defining an isomorphism.
-/

def isomorphism {G H : graph} (α : G ↦ H) : Prop :=
  ∃ β : H ↦ G, α ⊚ β = 𝕀 H ∧ β ⊚ α = 𝕀 G

/-
This is a sanity check: proving that the identity is an isomorphism.
-/
/- Lemma : The identity morphism is an isomorphism.
-/
lemma id_is_iso (G : graph) : isomorphism (𝕀 G) :=
begin
  sorry,
end

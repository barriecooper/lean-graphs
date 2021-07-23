import graphs.definitions

/-
Now that we know the compatability condition holds, we can go ahead and 
define composition of morphisms.
-/

def compose {G H K : graph} (β : H ↦ K) (α : G ↦ H) : G ↦ K :=
  morphism.mk (β.vertex_map ∘ α.vertex_map) (β.edge_map ∘ α.edge_map) (by exact compatability α β)

/-
We want a convenient infix operator for composition of morphisms.
-/

infix `⊚`:80 := compose

/-
Proving associativity of composition is now trivial ...
-/

/- Lemma :
For all morphisms $α : G → H$, $β : H → K$ and $γ : K → L$, we have
$γ ∘ (β ∘ α) = (γ ∘ β) ∘ α$.
-/
lemma mor_assoc {G H K L : graph} (α : G ↦ H) (β : H ↦ K) (γ : K ↦ L) : γ ⊚ (β ⊚ α) = (γ ⊚ β) ⊚ α :=
begin
  sorry,
end

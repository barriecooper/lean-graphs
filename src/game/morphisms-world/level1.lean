import data.sym2
open function

/-
We begin by defining a graph as a triple:
- vertices;
- edges;
- and an endpoint map taking each edge to the unordered pair of its endpoints.
-/

structure graph :=
  (vertices : Type)
  (edges : Type)
  (endpoints : edges → sym2 vertices)

/-
This theorem is a sanity check to see that sym2 works as we want.
-/

theorem endpoint_sym (G : graph) (a b : G.vertices) : ⟦(a,b)⟧ = ⟦(b,a)⟧ :=
begin
  exact sym2.eq_swap,
end

/-
Now we can define adjacency.
-/

def are_adjacent (G : graph) (a b : G.vertices) : Prop := ∃ e : G.edges, G.endpoints(e) = ⟦(a,b)⟧

/-
We now define a morphism of graphs to be a triple:
- a map on vertices;
- a map on edges;
- and a compatability condition between the two maps.
-/

structure morphism (G : graph) (H : graph) :=
  (vertex_map : G.vertices → H.vertices)
  (edge_map : G.edges → H.edges)
  (compatability : H.endpoints ∘ edge_map = sym2.map vertex_map ∘ G.endpoints)

/-
I want a convenient infix notation for a morphism.
I tried to overload the usual → arrow, but Lean got confused
(or probably I did it incorrectly).
-/

infix `↦` :50 := morphism

/-
We want to define composition of morphisms, but we need to prove that the
compatability condition needed holds when we do the `obvious' thing ...
-/

theorem compatability {G H K : graph} (α : G ↦ H) (β : H ↦ K) : K.endpoints ∘ β.edge_map ∘ α.edge_map = sym2.map (β.vertex_map ∘ α.vertex_map) ∘ G.endpoints :=
begin
  calc K.endpoints ∘ β.edge_map ∘ α.edge_map = (sym2.map β.vertex_map ∘ H.endpoints) ∘ α.edge_map : by rw ← β.compatability
                                         ... = sym2.map β.vertex_map ∘ (sym2.map α.vertex_map ∘ G.endpoints) : by rw ← α.compatability
                                         ... = (sym2.map β.vertex_map ∘ sym2.map α.vertex_map) ∘ G.endpoints : by refl
                                         ... = sym2.map (β.vertex_map ∘ α.vertex_map) ∘ G.endpoints : by rw ← sym2.map_comp,
end

/-
Now that we know the compatability condition holds, we can go ahead and 
define composition of morphisms.
-/

def compose {G H K : graph} (β : H ↦ K) (α : G ↦ H) : G ↦ K :=
  morphism.mk (β.vertex_map ∘ α.vertex_map) (β.edge_map ∘ α.edge_map) (by exact compatability α β)

/-
We want a convenient infix operator for composition of morphisms.
After my experience of trying to overload → I decided not to even attempt
to overload ∘.
-/

infix `⊚`:80 := compose

/-
Proving associativity of composition is now trivial ...
-/

theorem mor_assoc {G H K L : graph} (α : G ↦ H) (β : H ↦ K) (γ : K ↦ L) : γ ⊚ (β ⊚ α) = (γ ⊚ β) ⊚ α :=
begin
  refl,
end

/-
We want to define the identity morphism, but that requires a compatability proof.
-/

theorem id_compatability (G : graph) : G.endpoints ∘ id = sym2.map id ∘ G.endpoints :=
begin
  rw sym2.map_id,
  refl,
end

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

theorem id_is_iso (G : graph) : isomorphism (𝕀 G) :=
begin
  use 𝕀 G,
  split,
  refl,
  refl,
end

/-
Proving equality on structures is a pain, so we should prove an extensionality
theorem.  Basically, it suffices for the respective vertex maps and edge maps to 
be equal.
-/

theorem mor_ext {G H : graph} (α : G ↦ H) (β : G ↦ H) (hv : α.vertex_map = β.vertex_map) (he : α.edge_map = β.edge_map) : α = β :=
begin
  cases α,
  cases β,
  rw morphism.mk.inj_eq,
  exact ⟨hv, he⟩,
end

/-
The next two are helpful so that we don't have to keep repeating silly proofs.
Basically, we show that equal morphisms have equal vertex maps and edge maps.
-/

theorem eq_mor_eq_vmap {G H : graph} (α : G ↦ H) (β : G ↦ H) (hyp : α = β) : α.vertex_map = β.vertex_map :=
begin
  cases α,
  cases β,
  rw morphism.mk.inj_eq at hyp,
  exact hyp.1,
end

theorem eq_mor_eq_emap {G H : graph} (α : G ↦ H) (β : G ↦ H) (hyp : α = β) : α.edge_map = β.edge_map :=
begin
  cases α,
  cases β,
  rw morphism.mk.inj_eq at hyp,
  exact hyp.2,
end

/-
Our final two results are proving that a morphism is an isomorphism if and
only if the vertex map and edge map are both bijective.  Of course, we are
leaning very heavily on the corresponding results for functions.
-/

theorem iso.bij {G H : graph} (α : G ↦ H) (hyp : isomorphism α) : bijective α.vertex_map ∧ bijective α.edge_map :=
begin
  cases hyp with β hβ,
  cases hβ with h₁ h₂,
  split,
  split,
  have h₃ : left_inverse β.vertex_map α.vertex_map,
  {
    intro x,
    calc β.vertex_map (α.vertex_map x) = (β ⊚ α).vertex_map x : by refl
                                   ... = (𝕀 G).vertex_map x : by rw eq_mor_eq_vmap (β ⊚ α) (𝕀 G) (h₂)
                                   ... = x : by refl,
  },
  apply left_inverse.injective h₃,

  have h₃ : right_inverse β.vertex_map α.vertex_map,
  {
    intro x,
    calc α.vertex_map (β.vertex_map x) = (α ⊚ β).vertex_map x : by refl
                                   ... = (𝕀 H).vertex_map x : by rw eq_mor_eq_vmap (α ⊚ β) (𝕀 H) (h₁)
                                   ... = x : by refl,
  },
  apply right_inverse.surjective h₃,

  split,
  have h₃ : left_inverse β.edge_map α.edge_map,
  {
    intro x,
    calc β.edge_map (α.edge_map x) = (β ⊚ α).edge_map x : by refl
                                   ... = (𝕀 G).edge_map x : by rw eq_mor_eq_emap (β ⊚ α) (𝕀 G) (h₂)
                                   ... = x : by refl,
  },
  apply left_inverse.injective h₃,

  have h₃ : right_inverse β.edge_map α.edge_map,
  {
    intro x,
    calc α.edge_map (β.edge_map x) = (α ⊚ β).edge_map x : by refl
                                   ... = (𝕀 H).edge_map x : by rw eq_mor_eq_emap (α ⊚ β) (𝕀 H) (h₁)
                                   ... = x : by refl,
  },
  apply right_inverse.surjective h₃,
end

theorem bij.iso {G H : graph} (α : G ↦ H) (hv : bijective α.vertex_map) (he : bijective α.edge_map) : isomorphism α :=
begin
  let φ := α.vertex_map,
  let ψ := α.edge_map,

  rw bijective_iff_has_inverse at hv,
  cases hv with φ' hφ',
  rw bijective_iff_has_inverse at he,
  cases he with ψ' hψ',

  have comp' : G.endpoints ∘ ψ' = sym2.map φ' ∘ H.endpoints,
  {
    calc G.endpoints ∘ ψ' = id ∘ G.endpoints ∘ ψ' : by refl
                      ... = sym2.map id ∘ G.endpoints ∘ ψ' : by rw sym2.map_id
                      ... = sym2.map (φ' ∘ φ) ∘ G.endpoints ∘ ψ' : by rw left_inverse.id hφ'.1
                      ... = sym2.map φ' ∘ sym2.map φ ∘ G.endpoints ∘ ψ' : by rw sym2.map_comp
                      ... = sym2.map φ' ∘ (H.endpoints ∘ ψ) ∘ ψ' : by rw α.compatability
                      ... = sym2.map φ' ∘ H.endpoints ∘ (ψ ∘ ψ') : by refl
                      ... = sym2.map φ' ∘ H.endpoints ∘ id : by rw right_inverse.id hψ'.2
                      ... = sym2.map φ' ∘ H.endpoints : by refl,
  },

  let β := morphism.mk (φ') (ψ') (comp'),
  use β,
  split,

  {
    apply mor_ext,
    {
      calc (α ⊚ β).vertex_map = α.vertex_map ∘ β.vertex_map : by refl
                          ... = φ ∘ φ' : by refl
                          ... = id : by exact left_inverse.id hφ'.2
                          ... = (𝕀 H).vertex_map : by refl,
    },
    {
      calc (α ⊚ β).edge_map = α.edge_map ∘ β.edge_map : by refl
                          ... = ψ ∘ ψ' : by refl
                          ... = id : by exact left_inverse.id hψ'.2
                          ... = (𝕀 H).edge_map : by refl,
    },
  },
  
  {
    apply mor_ext,
    {
      calc (β ⊚ α).vertex_map = β.vertex_map ∘ α.vertex_map : by refl
                          ... = φ' ∘ φ : by refl
                          ... = id : by exact left_inverse.id hφ'.1
                          ... = (𝕀 G).vertex_map : by refl,
    },
    {
      calc (β ⊚ α).edge_map = β.edge_map ∘ α.edge_map : by refl
                          ... = ψ' ∘ ψ : by refl
                          ... = id : by exact left_inverse.id hψ'.1
                          ... = (𝕀 G).edge_map : by refl,
    },
  },
end
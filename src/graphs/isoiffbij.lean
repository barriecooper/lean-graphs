import graphs.allexts
open function

lemma iso.bij {G H : graph} (α : G ↦ H) (hyp : isomorphism α) : bijective α.vertex_map ∧ bijective α.edge_map :=
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

lemma bij.iso {G H : graph} (α : G ↦ H) (hv : bijective α.vertex_map) (he : bijective α.edge_map) : isomorphism α :=
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
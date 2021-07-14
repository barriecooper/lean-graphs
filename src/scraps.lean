--import data.set
import data.sym2
open set function

--open_locale classical

--universe u
--variable {U : Type u}

--def P₁ (A : set U) : set (set U) := { B : set U | ∃ a ∈ A, B = {a} }
--def P₂ (A : set U) : set (set U) := { B : set U | ∃ a b ∈ A, a ≠ b ∧ B = {a, b}}

--variables V E : set U
--variable ε : E → P₁(V) ∪ P₂(V)

--#check P₁ V

structure digraph :=
  mk :: (vertices : Type) (arrows : Type) (endpoints : arrows → vertices × vertices)

--#check (∅ : set U)

/-theorem empty_one : P₁((∅ : set U)) = ∅ :=
begin
  apply eq_of_subset_of_subset,
  {
    assume x,
    intro h₁,
    cases h₁ with a ha,
    rw mem_empty_eq,
    cases ha with H hH,
    rw ← mem_empty_eq a,
    exact H,
  },
  {
    exact empty_subset _,
  },
end-/

--variables a b : U
--variable G : graph

#check digraph

--def are_adjacent (G : digraph) (a b : G.vertices) : Prop := ∃ e : G.arrows, G.endpoints(e) = (a,b) ∨ G.endpoints(e) = (b,a)

/-def twist (α : Type × Type) : Type × Type := 
  prod.mk (prod.snd α) (prod.fst α)

#check twist
variable α : Type × Type
#reduce twist α

def rel (α : Type × Type) (β : Type × Type) : Prop :=
  β = α ∨ β = twist(α)

#check rel
#check quot rel
#reduce quot rel

variable V : Type
#check prod.mk V V
#check quot.mk rel
#check quot.mk rel (V,V)
-/

structure graph :=
  (vertices : Type)
  (edges : Type)
  (endpoints : edges → sym2 vertices)

#check graph

/-variable G : graph
#check G.vertices
variables a b : G.vertices
#check a
#check ⟦(a,b)⟧-/

theorem endpoint_sym (G : graph) (a b : G.vertices) : ⟦(a,b)⟧ = ⟦(b,a)⟧ :=
begin
  exact sym2.eq_swap,
end

def are_adjacent (G : graph) (a b : G.vertices) : Prop := ∃ e : G.edges, G.endpoints(e) = ⟦(a,b)⟧

structure morphism (G : graph) (H : graph) :=
  (vertex_map : G.vertices → H.vertices)
  (edge_map : G.edges → H.edges)
  (compatability : H.endpoints ∘ edge_map = sym2.map vertex_map ∘ G.endpoints)

variable G : graph
variable H : graph
variable K : graph
infix `↦` :50 := morphism

variable α : G ↦ H
variable β : morphism H K
#check α
#check β

#check K.endpoints ∘ β.edge_map ∘ α.edge_map
#check β.vertex_map ∘ α.vertex_map
#check G.endpoints
#check α.compatability
#check β.compatability

theorem compatability {G H K : graph} (α : G ↦ H) (β : H ↦ K) : K.endpoints ∘ β.edge_map ∘ α.edge_map = sym2.map (β.vertex_map ∘ α.vertex_map) ∘ G.endpoints :=
begin
  have h₁ : K.endpoints ∘ β.edge_map ∘ α.edge_map = sym2.map β.vertex_map ∘ H.endpoints ∘ α.edge_map,
  {
    rw ← comp.assoc K.endpoints β.edge_map α.edge_map,
    rw β.compatability,
  },
  have h₂ : sym2.map (β.vertex_map) ∘ H.endpoints ∘ α.edge_map = sym2.map (β.vertex_map) ∘ sym2.map (α.vertex_map) ∘ G.endpoints,
  {
    rw α.compatability,
  },
  have h₃ : sym2.map (β.vertex_map ∘ α.vertex_map) = sym2.map (β.vertex_map) ∘ sym2.map (α.vertex_map),
  {
    by exact sym2.map_comp,
  },
  rw h₁,
  rw h₂,
  rw h₃,
end

def compose {G H K : graph} (β : H ↦ K) (α : G ↦ H) : G ↦ K :=
  morphism.mk (β.vertex_map ∘ α.vertex_map) (β.edge_map ∘ α.edge_map) (by exact compatability α β)

#check compose β α
infix `⊚`:80 := compose
variable L : graph
variable γ : K ↦ L
#check γ
#check β ⊚ α
#check γ ⊚ β

theorem mor_assoc {G H K L : graph} (α : G ↦ H) (β : H ↦ K) (γ : K ↦ L) : γ ⊚ (β ⊚ α) = (γ ⊚ β) ⊚ α :=
begin
  refl,
end

theorem id_compatability (G : graph) : G.endpoints ∘ id = sym2.map id ∘ G.endpoints :=
begin
  rw sym2.map_id,
  refl,
end

#check id_compatability G

def 𝕀 (G : graph) : G ↦ G :=
  morphism.mk (id) (id) (by exact id_compatability G)

variable {U : Type}
variables {V E : set U}
#check V
variable {ε : E → sym2 V}
#check ε
#reduce 𝕀 G

def s := graph.mk (V) (E) (ε)
#check s

def isomorphism {G H : graph} (α : G ↦ H) : Prop :=
  ∃ β : H ↦ G, α ⊚ β = 𝕀 H ∧ β ⊚ α = 𝕀 G

theorem id_is_iso (G : graph) : isomorphism (𝕀 G) :=
begin
  use 𝕀 G,
  split,
  refl,
  refl,
end

#check id H.vertices
#check (𝕀 H).vertex_map
#reduce (𝕀 H).vertex_map

theorem mor_ext {G H : graph} (α : G ↦ H) (β : G ↦ H) (hv : α.vertex_map = β.vertex_map) (he : α.edge_map = β.edge_map) : α = β :=
begin
  cases α,
  cases β,
  rw morphism.mk.inj_eq,
  exact ⟨hv, he⟩,
end

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

#reduce (β ⊚ α).vertex_map
#check eq_mor_eq_vmap (β ⊚ α) (β ⊚ α) (rfl)

theorem iso.bij {G H : graph} (α : G ↦ H) (hyp : isomorphism α) : bijective α.vertex_map ∧ bijective α.edge_map :=
begin
  cases hyp with β hβ,
  cases hβ with h₁ h₂,
  split,
  split,
  /-
  have h₃ := eq_mor_eq_vmap (β ⊚ α) (𝕀 G) (h₂),
  have h₄ : (𝕀 G).vertex_map = λ (x : G.vertices), x,
  {
    refl,
  },
  have h₅ : (β ⊚ α).vertex_map = β.vertex_map ∘ α.vertex_map,
  {
    refl,
  },
  have h₆ : left_inverse β.vertex_map α.vertex_map,
  {
    intro x,
    have h₇ : (β ⊚ α).vertex_map x = β.vertex_map (α.vertex_map x),
    {
      refl,
    },
    rw ← h₇,
    have h₈ : (β ⊚ α).vertex_map x = (𝕀 G).vertex_map x,
    {
      rw h₃,
    },
    rw h₈,
    rw h₄,
  },
  -/
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
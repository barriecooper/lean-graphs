import data.sym2

structure graph :=
  (vertices : Type)
  (edges : Type)
  (endpoints : edges → sym2 vertices)

structure morphism (G : graph) (H : graph) :=
  (vertex_map : G.vertices → H.vertices)
  (edge_map : G.edges → H.edges)
  (compatability : H.endpoints ∘ edge_map = sym2.map vertex_map ∘ G.endpoints)

infix `↦` :50 := morphism

lemma compatability {G H K : graph} (α : G ↦ H) (β : H ↦ K) : K.endpoints ∘ β.edge_map ∘ α.edge_map = sym2.map (β.vertex_map ∘ α.vertex_map) ∘ G.endpoints :=
begin
  calc K.endpoints ∘ β.edge_map ∘ α.edge_map = (sym2.map β.vertex_map ∘ H.endpoints) ∘ α.edge_map : by rw ← β.compatability
                                         ... = sym2.map β.vertex_map ∘ (sym2.map α.vertex_map ∘ G.endpoints) : by rw ← α.compatability
                                         ... = (sym2.map β.vertex_map ∘ sym2.map α.vertex_map) ∘ G.endpoints : by refl
                                         ... = sym2.map (β.vertex_map ∘ α.vertex_map) ∘ G.endpoints : by rw ← sym2.map_comp,
end

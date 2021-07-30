import data.sym2 -- allows us to use unordered pairs

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
We want a convenient infix notation for a morphism.
-/

infix `↦` :50 := morphism

/-
We want to define composition of morphisms, so your first task is to prove that the
compatability condition needed holds when we do the `obvious' thing ... you will want 
to use the result sym2.map_comp.
-/

/- Lemma :
For all graphs $G$, $H$ and $K$ and for all morphisms $α : G → H$ and $β : H → K$, we have
$ε_K ∘ β_e ∘ α_e = sym2 (β_v ∘ α_v) ∘ ε_G$.
-/
lemma compatability {G H K : graph} (α : G ↦ H) (β : H ↦ K) : K.endpoints ∘ β.edge_map ∘ α.edge_map = sym2.map (β.vertex_map ∘ α.vertex_map) ∘ G.endpoints :=
begin
  sorry,




  
end
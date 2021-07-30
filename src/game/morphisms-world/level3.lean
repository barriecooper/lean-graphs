import graphs.composition

/-
We want to define the identity morphism, but that requires a compatability proof.  
You will need to use sym2.map_id.
-/

/- Lemma : The identity maps on vertices and edges satisfy the compatability condition.
-/
lemma id_compatability (G : graph) : G.endpoints ∘ id = sym2.map id ∘ G.endpoints :=
begin
  sorry,




  
end

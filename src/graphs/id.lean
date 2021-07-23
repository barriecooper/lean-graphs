import graphs.composition

lemma id_compatability (G : graph) : G.endpoints ∘ id = sym2.map id ∘ G.endpoints :=
begin
  rw sym2.map_id,
  refl,
end
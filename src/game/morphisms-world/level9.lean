import graphs.allexts
open function -- allows us to use key results about functions

/-
... and now for the converse ...
-/
/- Lemma :
-/
lemma bij.iso {G H : graph} (α : G ↦ H) (hv : bijective α.vertex_map) (he : bijective α.edge_map) : isomorphism α :=
begin
  sorry,
end
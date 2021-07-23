import graphs.allexts
open function -- allows us to use key results about functions

/-
Our final two results are proving that a morphism is an isomorphism if and
only if the vertex map and edge map are both bijective.  Of course, we are
leaning very heavily on the corresponding results for functions.

You will probably want to use the definitions of left_inverse and right_inverse 
and to apply the results left_inverse.injective and right_inverse.surjective.
-/
/- Lemma :
-/
lemma iso.bij {G H : graph} (α : G ↦ H) (hyp : isomorphism α) : bijective α.vertex_map ∧ bijective α.edge_map :=
begin
  sorry,
end

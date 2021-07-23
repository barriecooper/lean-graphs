import graphs.ext

/-
The next two are helpful so that we don't have to keep repeating silly proofs.
Basically, we show that equal morphisms have equal vertex maps and edge maps 
using essentially the same argument as for our more general extensionality 
theorem.
-/
/- Lemma :
-/
lemma eq_mor_eq_vmap {G H : graph} (α : G ↦ H) (β : G ↦ H) (hyp : α = β) : α.vertex_map = β.vertex_map :=
begin
  sorry,
end

import graphs.iso

/-
Proving equality on structures is a pain, so we should prove an extensionality
theorem.  Basically, it suffices for the respective vertex maps and edge maps to 
be equal.

You will need to use cases to write out α and β, and then rewrite with 
morphism.mk.inj_eq, which splits the equality of structures into separate goals.
-/
/- Lemma : 
-/
lemma mor_ext {G H : graph} (α : G ↦ H) (β : G ↦ H) (hv : α.vertex_map = β.vertex_map) (he : α.edge_map = β.edge_map) : α = β :=
begin
  sorry,




  
end

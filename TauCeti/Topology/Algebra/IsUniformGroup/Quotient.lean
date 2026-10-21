/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# Completeness of open quotients of right-uniform additive groups

Mathlib's `QuotientAddGroup.completeSpace_right` makes the quotient `G ⧸ N` of a complete first
countable right-uniform additive group complete for its right uniformity. An additive group `H`
receiving an open quotient map `f : G → H` is that quotient in disguise: the induced isomorphism
`G ⧸ ker f ≃+ H` is a homeomorphism, hence a uniform embedding for any uniformity making `H` a
right-uniform additive group (for instance a uniform additive group). So `H` is complete, whatever
such uniformity it carries. No commutativity is needed.

This is the form in which completeness is needed for a ring presented as an open quotient of a
complete ring, such as an algebra topologically of finite type over a Tate ring.

## Main results

* `IsOpenQuotientMap.completeSpace`: a right-uniform additive group admitting an open quotient
  map from a complete first countable right-uniform additive group is complete.

## References

* [N. Bourbaki, *General Topology*][bourbaki1966b], IX.3.1 Proposition 4.
-/

public section

open Topology

variable {G H : Type*} [AddGroup G] [UniformSpace G] [IsRightUniformAddGroup G] [CompleteSpace G]
  [FirstCountableTopology G] [AddGroup H] [UniformSpace H] [IsRightUniformAddGroup H]
  {F : Type*} [FunLike F G H] [AddMonoidHomClass F G H] {f : F}

/-- **An open quotient of a complete first countable right-uniform additive group is
complete.** If `f : G → H` is a continuous open surjective additive homomorphism, `G` is complete
and first countable, and `H` is a right-uniform additive group, then `H` is complete: `f`
identifies `H` with `G ⧸ ker f`, which is complete by `QuotientAddGroup.completeSpace_right`. -/
theorem IsOpenQuotientMap.completeSpace (hf : IsOpenQuotientMap f) : CompleteSpace H := by
  let N := AddMonoidHom.ker (f : G →+ H)
  let _ : UniformSpace (G ⧸ N) := IsTopologicalAddGroup.rightUniformSpace (G ⧸ N)
  have _ : CompleteSpace (G ⧸ N) := QuotientAddGroup.completeSpace_right G N
  let e := QuotientAddGroup.quotientKerEquivOfSurjective (f : G →+ H) hf.surjective
  -- `e` composed with the quotient map is `f`
  have hef : (e : G ⧸ N → H) ∘ ((↑) : G → G ⧸ N) = f :=
    funext fun g ↦ TauCeti.QuotientAddGroup.quotientKerEquivOfSurjective_apply_mk _ _ g
  have heq : IsQuotientMap e :=
    (QuotientAddGroup.isQuotientMap_mk N).of_comp_iff.mp (hef ▸ hf.isQuotientMap)
  have hemb : IsEmbedding e :=
    (isHomeomorph_iff_isQuotientMap_injective.mpr ⟨heq, e.injective⟩).isEmbedding
  -- An inducing homomorphism induces the right uniformities via neighborhoods of zero.
  have _ : IsRightUniformAddGroup (G ⧸ N) := ⟨rfl⟩
  have he : IsUniformEmbedding e := ⟨⟨by
    simp [uniformity_eq_comap_nhds_zero, Filter.comap_comap, Function.comp_def,
      hemb.nhds_eq_comap]⟩, e.injective⟩
  exact (completeSpace_congr (e := e.toEquiv) he).mp inferInstance

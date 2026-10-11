/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# Completeness of open quotients of uniform additive groups

Mathlib's `QuotientAddGroup.completeSpace_right` makes the quotient `G ⧸ N` of a complete first
countable uniform additive group complete for its canonical uniformity. An additive group `H`
receiving an open quotient map `f : G → H` is that quotient in disguise: the induced isomorphism
`G ⧸ ker f ≃+ H` is a homeomorphism, hence a uniform embedding for any uniformity making `H` a
uniform additive group. So `H` is complete, whatever compatible uniformity it carries.

This is the form in which completeness is needed for a ring presented as an open quotient of a
complete ring, such as an algebra topologically of finite type over a Tate ring.

## Main results

* `IsOpenQuotientMap.completeSpace`: a commutative uniform additive group admitting an open
  quotient map from a complete first countable uniform additive group is complete.

## References

* [N. Bourbaki, *General Topology*][bourbaki1966b], IX.3.1 Proposition 4.
-/

public section

open Topology

variable {G H : Type*} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] [CompleteSpace G]
  [FirstCountableTopology G] [AddCommGroup H] [UniformSpace H] [IsUniformAddGroup H]
  {F : Type*} [FunLike F G H] [AddMonoidHomClass F G H] {f : F}

/-- **An open quotient of a complete first countable commutative uniform additive group is
complete.** If `f : G → H` is a continuous open surjective additive homomorphism, `G` is complete
and first countable, and `H` is a uniform additive group, then `H` is complete: `f` identifies `H`
with `G ⧸ ker f`, which is complete by `QuotientAddGroup.completeSpace_right`. -/
theorem IsOpenQuotientMap.completeSpace (hf : IsOpenQuotientMap f) : CompleteSpace H := by
  let N := AddMonoidHom.ker (f : G →+ H)
  let _ : UniformSpace (G ⧸ N) := IsTopologicalAddGroup.rightUniformSpace (G ⧸ N)
  have _ : IsUniformAddGroup (G ⧸ N) := isUniformAddGroup_of_addCommGroup
  have _ : CompleteSpace (G ⧸ N) := QuotientAddGroup.completeSpace_right G N
  let e := QuotientAddGroup.quotientKerEquivOfSurjective (f : G →+ H) hf.surjective
  -- `e` composed with the quotient map is `f`
  have hef : (e : G ⧸ N → H) ∘ ((↑) : G → G ⧸ N) = f :=
    funext fun g ↦ TauCeti.QuotientAddGroup.quotientKerEquivOfSurjective_apply_mk _ _ g
  have hcont : Continuous e := (QuotientAddGroup.isQuotientMap_mk N).continuous_iff.mpr
    (hef ▸ hf.continuous)
  have hopen : IsOpenMap e := fun U hU ↦ by
    rw [← Set.image_preimage_eq U QuotientAddGroup.mk_surjective, ← Set.image_comp, hef]
    exact hf.isOpenMap _ (hU.preimage QuotientAddGroup.continuous_mk)
  have he : IsUniformEmbedding e := AddMonoidHom.isUniformEmbedding_of_isEmbedding
    (IsOpenEmbedding.of_continuous_injective_isOpenMap hcont e.injective hopen).isEmbedding
  exact (completeSpace_congr (e := e.toEquiv) he).mp inferInstance

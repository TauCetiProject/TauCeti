/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Gluing.GlueData

/-!
# Gluing open subsets of a manifold

Mathlib's `TopCat.GlueData.ofOpenSubsets U` glues a family `U` of open subsets of a space `X`
along their pairwise intersections. Its glued space embeds into `X` by
`TopCat.GlueData.fromOpenSubsetsGlue`, with image the union of the family, and it is homeomorphic
to `X` when the family covers `X` (`TopCat.GlueData.openCoverGlueHomeo`).

When `X` is a charted space, every piece `U i` and every overlap, an open subset of `U i`, carries
the atlas it inherits as an open subset. With these atlases the gluing is compatible
(`TopCat.GlueData.isCompatible_ofOpenSubsets`), for any model and regularity, so the results on
compatible gluings apply. If `X` is a `C^n` manifold, then the comparison map into `X` is a `C^n`
local diffeomorphism for the glued atlas `TopCat.GlueData.chartedSpace`
(`TopCat.GlueData.isLocalDiffeomorph_fromOpenSubsetsGlue`). For an open cover the glued manifold
is diffeomorphic to `X` (`TopCat.GlueData.openCoverGlueDiffeomorph`): gluing the charts of an
open cover recovers the manifold structure it started from.

## Main declarations

* `TopCat.GlueData.isCompatible_ofOpenSubsets`: open subsets of a charted space form a compatible
  gluing.
* `TopCat.GlueData.isLocalDiffeomorph_fromOpenSubsetsGlue`: the glued manifold maps into `X` by a
  `C^n` local diffeomorphism.
* `TopCat.GlueData.openCoverGlueDiffeomorph`: the gluing of an open cover is diffeomorphic to `X`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 1 (the smooth manifold chart lemma).
-/

public section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace TopCat.GlueData

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {X : Type u} [TopologicalSpace X] [ChartedSpace H X] {J : Type u} (U : J → Opens X)

/-- Each piece of the gluing of a family of open subsets carries its atlas as an open subset. -/
noncomputable instance instChartedSpaceOfOpenSubsetsU (i : (ofOpenSubsets U).J) :
    ChartedSpace H ((ofOpenSubsets U).U i) :=
  inferInstanceAs (ChartedSpace H (U i))

/-- The overlap of the pieces `U i` and `U j` is the open subset of `U i` of points lying in
`U j`, with its atlas as an open subset of `U i`. -/
noncomputable instance instChartedSpaceOfOpenSubsetsV (p : (ofOpenSubsets U).J ×
    (ofOpenSubsets U).J) : ChartedSpace H ((ofOpenSubsets U).V p) :=
  inferInstanceAs (ChartedSpace H (⟨Subtype.val ⁻¹' (U p.2 : Set X),
    (U p.2).isOpen.preimage continuous_subtype_val⟩ : Opens (U p.1)))

/-- Each piece of the gluing of open subsets of a `C^n` manifold is a `C^n` manifold. -/
instance instIsManifoldOfOpenSubsetsU [IsManifold I n X] (i : (ofOpenSubsets U).J) :
    IsManifold I n ((ofOpenSubsets U).U i) :=
  inferInstanceAs (IsManifold I n (U i))

/-- **Open subsets form a compatible gluing.** The overlap of `U i` and `U j` includes into both
pieces as an open subset, so both maps out of it are `C^n` local diffeomorphisms. -/
theorem isCompatible_ofOpenSubsets : (ofOpenSubsets U).IsCompatible I n := by
  have hU (k : J) : IsLocalDiffeomorph I I n (Subtype.val : U k → X) :=
    TauCeti.isLocalDiffeomorph_subtype_val
  -- By definition (`ofOpenSubsets_toGlueData_f`), each map `f k l` is the inclusion of an open
  -- subset of `U k`.
  have hf (k l : (ofOpenSubsets U).J) : IsLocalDiffeomorph I I n ((ofOpenSubsets U).f k l) :=
    TauCeti.isLocalDiffeomorph_subtype_val
  refine .of_isLocalDiffeomorph_t hf fun i j x ↦ ?_
  -- Followed by the inclusions into `U j` and `X`, the transition is the inclusion of the
  -- overlap into `U i` followed by the inclusion into `X`.
  exact IsLocalDiffeomorphAt.of_comp_left ((hf i j x).comp (hg := hU i _))
    ((hf j i _).comp (hg := hU j _)) ((ofOpenSubsets U).t i j).hom.continuous.continuousAt

variable [IsManifold I n X]

/-- The glued manifold of a family of open subsets of a `C^n` manifold `X` maps into `X` by a
`C^n` local diffeomorphism, the canonical open embedding onto the union of the family. -/
theorem isLocalDiffeomorph_fromOpenSubsetsGlue :
    letI := (ofOpenSubsets U).chartedSpace H
    IsLocalDiffeomorph I I n (fromOpenSubsetsGlue U) := by
  refine (isCompatible_ofOpenSubsets U).isLocalDiffeomorph_iff.2 fun i ↦ ?_
  -- On the piece `U i`, the comparison map is the inclusion of `U i` into `X`.
  have h : fromOpenSubsetsGlue U ∘ (ofOpenSubsets U).toGlueData.ι i = (Subtype.val : U i → X) :=
    funext (ι_fromOpenSubsetsGlue_apply U i)
  rw [h]
  exact TauCeti.isLocalDiffeomorph_subtype_val

/-- **Gluing the sets of an open cover recovers the manifold.** If the open subsets `U i` cover a
`C^n` manifold `X`, then their gluing, with the glued atlas, is `C^n` diffeomorphic to `X` by the
canonical map `fromOpenSubsetsGlue U`. -/
noncomputable def openCoverGlueDiffeomorph (h : ⋃ i, (U i : Set X) = univ) :
    letI := (ofOpenSubsets U).chartedSpace H
    (ofOpenSubsets U).toGlueData.glued ≃ₘ^n⟮I, I⟯ X :=
  letI := (ofOpenSubsets U).chartedSpace H
  (isLocalDiffeomorph_fromOpenSubsetsGlue U).diffeomorphOfBijective
    (openCoverGlueHomeo U h).bijective

/-- The diffeomorphism from the gluing of an open cover is the canonical map. -/
@[simp]
theorem coe_openCoverGlueDiffeomorph (h : ⋃ i, (U i : Set X) = univ) :
    letI := (ofOpenSubsets U).chartedSpace H
    ⇑(openCoverGlueDiffeomorph (I := I) (n := n) U h) = fromOpenSubsetsGlue U :=
  letI := (ofOpenSubsets U).chartedSpace H
  IsLocalDiffeomorph.coe_diffeomorphOfBijective _ _

/-- The diffeomorphism from the gluing of an open cover has Mathlib's homeomorphism
`openCoverGlueHomeo` as its underlying homeomorphism. -/
@[simp]
theorem toHomeomorph_openCoverGlueDiffeomorph (h : ⋃ i, (U i : Set X) = univ) :
    letI := (ofOpenSubsets U).chartedSpace H
    (openCoverGlueDiffeomorph (I := I) (n := n) U h).toHomeomorph = openCoverGlueHomeo U h :=
  Homeomorph.ext fun x ↦ congrFun (coe_openCoverGlueDiffeomorph U h) x

end TopCat.GlueData

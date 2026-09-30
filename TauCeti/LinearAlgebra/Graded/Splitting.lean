/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import TauCeti.Algebra.Module.GradedModule.Internal

/-!
# Homogeneous splittings of surjective linear maps

A surjective homogeneous linear map between internally graded vector spaces admits a homogeneous
linear right inverse.  The construction splits the restriction to each homogeneous piece and
assembles the chosen sections through the internal direct-sum decompositions.  This is the graded
form of the familiar fact that every short exact sequence of vector spaces splits.

The degree of the section is the negative of the degree of the original map.  In particular, a
degree-zero quotient map admits homogeneous representatives, while a degree-one differential
admits a degree-minus-one choice of preimages on its range.  Those are the two splittings used to
contract a complex of vector spaces onto its cohomology.

## Main result

* `TauCeti.LinearMap.IsHomogeneous.exists_rightInverse`: a surjective homogeneous map of degree
  `r` has a homogeneous right inverse of degree `-r`.
-/

public section

open scoped DirectSum

namespace TauCeti.LinearMap.IsHomogeneous

universe uK uM uN

variable {K : Type uK} {M : Type uM} {N : Type uN} [DivisionRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {G : InternalGrading K M} {H : InternalGrading K N} {f : M →ₗ[K] N} {r : ℤ}

/-- The restriction of a homogeneous map of degree `r` from degree `q - r` to degree `q`. -/
private def pieceMap (hf : IsHomogeneous f G.piece H.piece r) (q : ℤ) :
    G.piece (q - r) →ₗ[K] H.piece q :=
  (f.domRestrict (G.piece (q - r))).codRestrict (H.piece q) fun x ↦ by
    simpa only [LinearMap.domRestrict_apply, sub_add_cancel] using hf.map_mem x.2

/-- The restriction of a surjective homogeneous map to the pieces meeting a fixed target piece is
surjective. -/
private theorem pieceMap_surjective (hf : IsHomogeneous f G.piece H.piece r)
    (hsurj : Function.Surjective f) (q : ℤ) : Function.Surjective (pieceMap hf q) := by
  intro y
  obtain ⟨x, hx⟩ := hsurj (y : N)
  refine ⟨⟨DirectSum.decompose G.piece x (q - r),
    (DirectSum.decompose G.piece x (q - r)).2⟩, ?_⟩
  apply Subtype.ext
  -- Expose the subtype values so `map_decompose` applies to the ambient equality.
  change f (DirectSum.decompose G.piece x (q - r) : M) = (y : N)
  rw [hf.map_decompose, sub_add_cancel, hx]
  exact DirectSum.decompose_of_mem_same (ℳ := H.piece) y.2

/-- A chosen section of the restriction of a surjective homogeneous map to one target piece. -/
private noncomputable def pieceSection (hf : IsHomogeneous f G.piece H.piece r)
    (hsurj : Function.Surjective f) (q : ℤ) : H.piece q →ₗ[K] G.piece (q - r) :=
  Classical.choose ((pieceMap hf q).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (pieceMap_surjective hf hsurj q)))

/-- The chosen piecewise section is a right inverse. -/
private theorem pieceMap_comp_pieceSection (hf : IsHomogeneous f G.piece H.piece r)
    (hsurj : Function.Surjective f) (q : ℤ) :
    pieceMap hf q ∘ₗ pieceSection hf hsurj q = LinearMap.id :=
  Classical.choose_spec ((pieceMap hf q).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (pieceMap_surjective hf hsurj q)))

/-- The homogeneous right inverse obtained by assembling sections of all homogeneous pieces. -/
private noncomputable def rightInverse (hf : IsHomogeneous f G.piece H.piece r)
    (hsurj : Function.Surjective f) : N →ₗ[K] M :=
  DirectSum.toModule K ℤ M (fun q ↦
      (G.piece (q - r)).subtype ∘ₗ pieceSection hf hsurj q) ∘ₗ
    (DirectSum.decomposeLinearEquiv (ℳ := H.piece)).toLinearMap

/-- On a homogeneous input, the assembled right inverse is its chosen piecewise section. -/
private theorem rightInverse_apply_of_mem (hf : IsHomogeneous f G.piece H.piece r)
    (hsurj : Function.Surjective f) {q : ℤ} (y : N) (hy : y ∈ H.piece q) :
    rightInverse hf hsurj y = pieceSection hf hsurj q ⟨y, hy⟩ := by
  rw [rightInverse, LinearMap.comp_apply]
  -- Expose the direct-sum assembly; its input is definitionally the homogeneous decomposition.
  change (DirectSum.toModule K ℤ M fun q ↦
    (G.piece (q - r)).subtype ∘ₗ pieceSection hf hsurj q) (DirectSum.decompose H.piece y) = _
  rw [DirectSum.decompose_of_mem (ℳ := H.piece) hy,
    ← DirectSum.lof_eq_of K ℤ (fun i ↦ H.piece i) q ⟨y, hy⟩,
    DirectSum.toModule_lof, LinearMap.comp_apply, Submodule.coe_subtype]

/-- A surjective homogeneous linear map of degree `r` between internally graded vector spaces has
a homogeneous right inverse of degree `-r`. -/
theorem exists_rightInverse (hf : IsHomogeneous f G.piece H.piece r)
    (hsurj : Function.Surjective f) :
    ∃ g : N →ₗ[K] M, f ∘ₗ g = LinearMap.id ∧ IsHomogeneous g H.piece G.piece (-r) := by
  refine ⟨rightInverse hf hsurj, ?_, ?_⟩
  · apply H.linearMap_ext
    intro q y hy
    rw [LinearMap.comp_apply, rightInverse_apply_of_mem hf hsurj y hy, LinearMap.id_apply]
    have h := LinearMap.congr_fun (pieceMap_comp_pieceSection hf hsurj q) ⟨y, hy⟩
    exact congrArg Subtype.val h
  · rw [isHomogeneous_def]
    intro q y hy
    rw [← sub_eq_add_neg, rightInverse_apply_of_mem hf hsurj y hy]
    exact (pieceSection hf hsurj q ⟨y, hy⟩).2

end TauCeti.LinearMap.IsHomogeneous

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import TauCeti.Algebra.Module.GradedModule.Internal

/-!
# Homogeneous splittings of surjective linear maps

A surjective homogeneous linear map between internally graded modules admits a homogeneous
linear right inverse when its target is projective. Starting with an ordinary linear section,
retain the appropriate homogeneous component on each target piece and assemble these maps through
the internal direct-sum decomposition. Over a division ring the target is automatically projective,
so every surjective homogeneous map of vector spaces splits.

The degree of the section is the negative of the degree of the original map. For vector spaces,
a degree-zero quotient map admits homogeneous representatives, while a degree-one differential
admits a degree-minus-one choice of preimages on its range. Those are the two splittings used to
contract a complex of vector spaces onto its cohomology.

## Main result

* `TauCeti.LinearMap.IsHomogeneous.exists_rightInverse`: a surjective homogeneous map of degree
  `r` onto a projective module has a homogeneous right inverse of degree `-r`.
-/

public section

open scoped DirectSum

namespace TauCeti.LinearMap.IsHomogeneous

universe uR uM uN

variable {R : Type uR} {M : Type uM} {N : Type uN} [Semiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  {G : InternalGrading R M} {H : InternalGrading R N} {f : M →ₗ[R] N} {r : ℤ}

/-- A surjective homogeneous linear map of degree `r` between internally graded modules has a
homogeneous right inverse of degree `-r` if its target is projective. -/
theorem exists_rightInverse [Module.Projective R N] (hf : IsHomogeneous f G.piece H.piece r)
    (hsurj : Function.Surjective f) :
    ∃ g : N →ₗ[R] M, f ∘ₗ g = LinearMap.id ∧ IsHomogeneous g H.piece G.piece (-r) := by
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  let gq (q : ℤ) : H.piece q →ₗ[R] G.piece (q - r) :=
    DirectSum.component R ℤ (fun p ↦ G.piece p) (q - r) ∘ₗ
      (DirectSum.decomposeLinearEquiv G.piece).toLinearMap ∘ₗ s ∘ₗ (H.piece q).subtype
  let g : N →ₗ[R] M :=
    DirectSum.toModule R ℤ M (fun q ↦ (G.piece (q - r)).subtype ∘ₗ gq q) ∘ₗ
      (DirectSum.decomposeLinearEquiv H.piece).toLinearMap
  have hg (q : ℤ) (y : H.piece q) :
      g y = (DirectSum.decompose G.piece (s y) (q - r) : M) := by
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe,
      DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.toModule_lof]
    rfl
  refine ⟨g, ?_, ?_⟩
  · apply H.linearMap_ext
    intro q y hy
    rw [LinearMap.comp_apply, hg q ⟨y, hy⟩, hf.map_decompose, sub_add_cancel]
    have hsy : f (s y) = y := LinearMap.congr_fun hs y
    rw [hsy]
    exact DirectSum.decompose_of_mem_same (ℳ := H.piece) hy
  · rw [isHomogeneous_def]
    intro q y hy
    rw [hg q ⟨y, hy⟩, ← sub_eq_add_neg]
    exact (DirectSum.decompose G.piece (s y) (q - r)).2

end TauCeti.LinearMap.IsHomogeneous

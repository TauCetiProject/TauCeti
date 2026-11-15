/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.MoorePenrose
public import TauCeti.Analysis.InnerProductSpace.Positive.SquareRoot

/-!
# Inverting a symmetric operator on its range

A symmetric endomorphism with finite-dimensional range restricts to an automorphism of its
range. In a finite-dimensional ambient inner product space, its inverse, preceded by orthogonal
projection onto the range and followed by inclusion, is the Moore–Penrose inverse. For a positive
operator the restricted quadratic form is positive definite, even when the operator is singular.

These statements allow a singular covariance to be inverted on the subspace on which its
Gaussian law lives. They include the zero operator and the zero-dimensional space: the range
automorphism then acts on the zero subspace.

The construction uses Mathlib's `LinearMap.IsSymmetric.orthogonal_range` and
`LinearEquiv.ofBijective`; the comparison uses `LinearMap.IsMoorePenroseInverse.unique`.

## References

* A. Ben-Israel, T. N. E. Greville, *Generalized Inverses: Theory and Applications*,
  second edition, Springer (2003), Chapter 1.
* T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*,
  third edition, Wiley (2003), Chapter 2.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace LinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {T : E →ₗ[𝕜] E}

namespace IsSymmetric

/-- The restriction of a symmetric operator to its range is injective. -/
theorem injective_restrict_range (hT : T.IsSymmetric) :
    Function.Injective (T.restrict (fun x (_ : x ∈ T.range) ↦ T.mem_range_self x)) := by
  rw [LinearMap.injective_restrict_iff, ← hT.orthogonal_range]
  exact T.range.orthogonal_disjoint

/-- Projecting onto the range does not change the value of a symmetric operator. -/
@[simp]
theorem apply_starProjection_range (hT : T.IsSymmetric) [T.range.HasOrthogonalProjection]
    (x : E) : T (T.range.starProjection x) = T x := by
  have h := T.range.sub_starProjection_mem_orthogonal x
  rw [hT.orthogonal_range, mem_ker, map_sub, sub_eq_zero] at h
  exact h.symm

section FiniteRange

variable [FiniteDimensional 𝕜 T.range]

/-- A symmetric operator, restricted to its range, as a linear automorphism. Its inverse solves
`T x = y` uniquely with `x` in the range of `T`. -/
def rangeEquiv (hT : T.IsSymmetric) : T.range ≃ₗ[𝕜] T.range :=
  LinearEquiv.ofBijective (T.restrict (fun x (_ : x ∈ T.range) ↦ T.mem_range_self x))
    ⟨hT.injective_restrict_range,
      injective_iff_surjective.mp hT.injective_restrict_range⟩

/-- The underlying map of the range automorphism is the restriction of the operator. -/
@[simp]
theorem rangeEquiv_toLinearMap (hT : T.IsSymmetric) :
    hT.rangeEquiv.toLinearMap =
      T.restrict (fun x (_ : x ∈ T.range) ↦ T.mem_range_self x) := (rfl)

/-- The range automorphism acts by the original operator. -/
@[simp]
theorem rangeEquiv_apply (hT : T.IsSymmetric) (x : T.range) :
    (hT.rangeEquiv x : E) = T x := (rfl)

/-- Applying the operator to its range inverse recovers the input. -/
@[simp]
theorem apply_rangeEquiv_symm (hT : T.IsSymmetric) (x : T.range) :
    T (hT.rangeEquiv.symm x : E) = x := by
  exact (hT.rangeEquiv_apply _).symm.trans
    (congrArg Subtype.val (hT.rangeEquiv.apply_symm_apply x))

end FiniteRange

variable [FiniteDimensional 𝕜 E]

/-- The inverse on the range, extended by zero on its orthogonal complement, is the
Moore–Penrose inverse of a symmetric operator. -/
theorem moorePenroseInverse_eq_rangeEquiv_symm_comp (hT : T.IsSymmetric) :
    T.moorePenroseInverse = T.range.subtype ∘ₗ hT.rangeEquiv.symm.toLinearMap ∘ₗ
      T.range.orthogonalProjectionOnto.toLinearMap := by
  symm
  let B := T.range.subtype ∘ₗ hT.rangeEquiv.symm.toLinearMap ∘ₗ
    T.range.orthogonalProjectionOnto.toLinearMap
  have hTB : T ∘ₗ B = T.range.starProjection.toLinearMap := by
    ext x
    exact hT.apply_rangeEquiv_symm _
  have hBT : B ∘ₗ T = T.range.starProjection.toLinearMap := by
    ext x
    have hproj : T.range.orthogonalProjectionOnto (T x) =
        hT.rangeEquiv (T.range.orthogonalProjectionOnto x) := by
      apply Subtype.ext
      simp only [Submodule.coe_orthogonalProjectionOnto_apply, rangeEquiv_apply,
        hT.apply_starProjection_range,
        Submodule.starProjection_eq_self_iff.mpr (T.mem_range_self x)]
    simp only [B, comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
      ContinuousLinearMap.coe_coe, hproj, LinearEquiv.symm_apply_apply,
      Submodule.coe_orthogonalProjectionOnto_apply]
  refine (isMoorePenroseInverse_iff_eq_moorePenroseInverse T).mp
    ⟨?_, ?_, hTB ▸ T.range.starProjection_isSymmetric,
      hBT ▸ T.range.starProjection_isSymmetric⟩
  · rw [← comp_assoc, hTB]
    ext x
    exact T.range.starProjection_eq_self_iff.mpr (T.mem_range_self x)
  · rw [← comp_assoc, hBT]
    ext x
    exact T.range.starProjection_eq_self_iff.mpr (SetLike.coe_mem _)

end IsSymmetric

variable [FiniteDimensional 𝕜 T.range]

/-- A positive operator's quadratic form is strictly positive on each nonzero vector in its
range. This is positive definiteness on the range, without ambient invertibility. -/
theorem IsPositive.re_inner_pos_of_mem_range (hT : T.IsPositive) {x : E}
    (hx : x ∈ T.range) (hx0 : x ≠ 0) : 0 < RCLike.re ⟪T x, x⟫_𝕜 := by
  let R := T.restrict (fun y (_ : y ∈ T.range) ↦ T.mem_range_self y)
  have hR : R.IsPositive :=
    ⟨hT.isSymmetric.restrict_invariant _, fun y ↦ hT.re_inner_nonneg_left y⟩
  let y : T.range := ⟨x, hx⟩
  refine lt_of_le_of_ne (hT.re_inner_nonneg_left x) ?_
  intro hzero
  have hsqrt : hR.sqrt y = 0 := by
    apply norm_eq_zero.mp
    apply sq_eq_zero_iff.mp
    rw [hR.norm_sqrt_apply_sq]
    simpa only [Submodule.coe_inner, R, coe_restrict_apply] using hzero.symm
  have hy : R y = 0 := by
    rw [← mem_ker, ← hR.ker_sqrt, mem_ker]
    exact hsqrt
  exact hx0 (congrArg Subtype.val
    (hT.isSymmetric.injective_restrict_range (hy.trans (map_zero R).symm)))

/-- A positive operator's range automorphism has positive-definite quadratic form. -/
theorem IsPositive.re_inner_rangeEquiv_pos (hT : T.IsPositive) {x : T.range} (hx : x ≠ 0) :
    0 < RCLike.re ⟪hT.isSymmetric.rangeEquiv x, x⟫_𝕜 := by
  simpa only [Submodule.coe_inner, IsSymmetric.rangeEquiv_apply] using
    hT.re_inner_pos_of_mem_range x.property (fun h ↦ hx (Subtype.ext h))

end LinearMap

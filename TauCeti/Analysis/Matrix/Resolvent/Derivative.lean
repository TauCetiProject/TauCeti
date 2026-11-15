/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Resolvent.Basic
public import TauCeti.Analysis.Matrix.L2OpNorm
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Derivative of a matrix resolvent

For Hermitian `A` and `B`, differentiating the resolvent of `A + t • B` along a real parameter
gives `-R * B * R`, where `R = (A + t • B - z • 1)⁻¹` and `z` is nonreal.

## Main results

* `Matrix.IsHermitian.hasDerivAt_inv_add_smul_sub_smul_one` gives the matrix derivative.
* `Matrix.IsHermitian.hasDerivAt_inv_add_smul_sub_smul_one_apply` gives the entrywise derivative.
* `Matrix.IsHermitian.hasDerivAt_inv_add_smul_single_sub_smul_one_apply` specializes to a
  diagonal matrix unit: the derivative of entry `(i,j)` is `-R i k * R k j`.
-/

public section

noncomputable section

open scoped Matrix.Norms.L2Operator

/-- The real normed algebra structure induced by the matrix Euclidean operator norm. -/
local instance matrixComplexNormedAlgebraReal (n : Type*) [Fintype n] [DecidableEq n] :
    NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.l2OpNormedAlgebraReal

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
include hA hB

/-- The derivative of the resolvent along a Hermitian perturbation. -/
theorem hasDerivAt_inv_add_smul_sub_smul_one (t : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ (A + s • B - z • 1)⁻¹)
      (-((A + t • B - z • 1)⁻¹ * B * (A + t • B - z • 1)⁻¹)) t := by
  have h : (A + t • B).IsHermitian := by
    apply hA.add
    exact hB.smul (by simp [IsSelfAdjoint])
  obtain ⟨u, hu⟩ := h.isUnit_sub_smul_one_of_im_ne_zero hz
  have hd : HasDerivAt (fun s : ℝ ↦ A + s • B - z • 1) B t := by
    simpa only [one_smul] using! (((hasDerivAt_id t).smul_const B).const_add A).sub_const
      (z • (1 : Matrix n n ℂ))
  have hi := (hasFDerivAt_ringInverse (𝕜 := ℝ) u).comp_hasDerivAt_of_eq t hd hu
  simpa [Matrix.nonsing_inv_eq_ringInverse, hu, ContinuousLinearMap.mulLeftRight_apply] using! hi

/-- The derivative of an individual entry of the resolvent. -/
theorem hasDerivAt_inv_add_smul_sub_smul_one_apply (t : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (i j : n) :
    HasDerivAt (fun s : ℝ ↦ (A + s • B - z • 1)⁻¹ i j)
      (-((A + t • B - z • 1)⁻¹ * B * (A + t • B - z • 1)⁻¹) i j) t := by
  have h := (entryLinearMap ℝ ℂ i j).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (hA.hasDerivAt_inv_add_smul_sub_smul_one hB t hz)
  simpa using! h

end Matrix.IsHermitian

namespace Matrix

/-- Perturbing one diagonal entry gives the negative product of the corresponding column and row
of the resolvent. -/
theorem IsHermitian.hasDerivAt_inv_add_smul_single_sub_smul_one_apply
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (t : ℝ) {z : ℂ} (hz : z.im ≠ 0) (i j k : n) :
    HasDerivAt (fun s : ℝ ↦ (A + s • single k k (1 : ℂ) - z • 1)⁻¹ i j)
      (-((A + t • single k k (1 : ℂ) - z • 1)⁻¹ i k *
        (A + t • single k k (1 : ℂ) - z • 1)⁻¹ k j)) t := by
  have hB : (single k k (1 : ℂ)).IsHermitian := by
    simp [IsHermitian, conjTranspose_single]
  have h := hA.hasDerivAt_inv_add_smul_sub_smul_one_apply hB t hz i j
  have hm (R : Matrix n n ℂ) : (R * single k k (1 : ℂ) * R) i j = R i k * R k j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single k]
    · simp
    · intro b _ hbk
      rw [mul_single_apply_of_ne _ k k i b hbk]
      simp
    · simp
  simpa only [hm, neg_apply] using h

end Matrix

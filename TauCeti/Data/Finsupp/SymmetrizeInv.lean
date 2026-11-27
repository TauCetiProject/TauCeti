/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finsupp.Order
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Symmetrizing finitely supported weights under inversion

Averaging a weight with its relabeling by inversion gives an inversion-invariant weight.
For nonnegative weights the support becomes the union of the original support and its inverse
image under inversion. In a weighted sum one can instead average the observable, so in
particular the sum is unchanged for an inversion-invariant observable. This applies to real
parts of functions paired by complex conjugation, as in weighted Riesz remainders.
-/

public section

namespace Finsupp

variable {ι : Type*} [InvolutiveInv ι]

/-- Average a real weight with the weight transported by inversion of its indices. -/
noncomputable def symmetrizeInv (w : ι →₀ ℝ) : ι →₀ ℝ :=
  (2 : ℝ)⁻¹ • (w + w.equivMapDomain (Equiv.inv ι))

/-- The weight at an index is the mean of the original weights at the index and its inverse. -/
@[simp]
theorem symmetrizeInv_apply (w : ι →₀ ℝ) (i : ι) :
    w.symmetrizeInv i = (w i + w i⁻¹) / 2 := by
  simp [symmetrizeInv, smul_eq_mul, div_eq_inv_mul, mul_add]

/-- The empty family stays empty under symmetrization. -/
@[simp]
theorem symmetrizeInv_zero : (0 : ι →₀ ℝ).symmetrizeInv = 0 := by
  ext i
  simp

/-- The symmetrized weight is fixed by inversion of the index. -/
theorem symmetrizeInv_apply_inv (w : ι →₀ ℝ) (i : ι) :
    w.symmetrizeInv i⁻¹ = w.symmetrizeInv i := by
  simp only [symmetrizeInv_apply, inv_inv, add_comm (w i⁻¹)]

/-- The fixed points of symmetrization are exactly the inversion-invariant weights. -/
@[simp]
theorem symmetrizeInv_eq_self_iff (w : ι →₀ ℝ) :
    w.symmetrizeInv = w ↔ ∀ i, w i⁻¹ = w i := by
  constructor
  · intro h i
    simpa only [h] using w.symmetrizeInv_apply_inv i
  · intro h
    ext i
    rw [symmetrizeInv_apply, h, add_self_div_two]

/-- Averaging an already symmetrized weight has no effect. -/
@[simp]
theorem symmetrizeInv_symmetrizeInv (w : ι →₀ ℝ) :
    w.symmetrizeInv.symmetrizeInv = w.symmetrizeInv :=
  (symmetrizeInv_eq_self_iff _).2 w.symmetrizeInv_apply_inv

/-- Symmetrization preserves nonnegativity. -/
theorem symmetrizeInv_nonneg {w : ι →₀ ℝ} (hw : 0 ≤ w) : 0 ≤ w.symmetrizeInv := by
  rw [Finsupp.le_def]
  intro i
  simp only [zero_apply, symmetrizeInv_apply]
  exact div_nonneg (add_nonneg (Finsupp.le_def.mp hw i) (Finsupp.le_def.mp hw _)) (by norm_num)

/-- Without cancellation, an index belongs to the symmetrized support exactly when it or its
inverse belongs to the original support. -/
theorem mem_support_symmetrizeInv {w : ι →₀ ℝ} (hw : 0 ≤ w) (i : ι) :
    i ∈ w.symmetrizeInv.support ↔ i ∈ w.support ∨ i⁻¹ ∈ w.support := by
  have hn (j : ι) : 0 ≤ w j := by simpa using Finsupp.le_def.mp hw j
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  simp only [mem_support_iff, symmetrizeInv_apply, div_ne_zero_iff, htwo, not_false_eq_true,
    and_true, ne_eq, add_eq_zero_iff_of_nonneg (hn i) (hn i⁻¹), not_and_or]

/-- A sum with symmetrized weights equals the original weighted sum of the averaged observable.
This does not require sign conditions on the weights. -/
theorem sum_symmetrizeInv_smul {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (w : ι →₀ ℝ) (f : ι → M) :
    w.symmetrizeInv.sum (fun i c ↦ c • f i) =
      w.sum (fun i c ↦ c • ((2 : ℝ)⁻¹ • (f i + f i⁻¹))) := by
  rw [symmetrizeInv, sum_smul_index (by simp)]
  simp only [mul_smul, ← smul_sum]
  rw [sum_add_index' (h := fun i (c : ℝ) ↦ c • f i) (by simp) (by simp [add_smul]),
    sum_equivMapDomain, ← sum_add]
  rw [smul_sum]
  simp only [smul_add, smul_comm (2 : ℝ)⁻¹, Equiv.inv_apply]

/-- Symmetrizing the weights does not affect a sum of an inversion-invariant observable. -/
theorem sum_symmetrizeInv_smul_of_apply_inv_eq {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (w : ι →₀ ℝ) (f : ι → M) (hf : ∀ i, f i⁻¹ = f i) :
    w.symmetrizeInv.sum (fun i c ↦ c • f i) = w.sum (fun i c ↦ c • f i) := by
  simp only [sum_symmetrizeInv_smul, hf, ← two_smul ℝ, smul_smul, inv_mul_cancel₀
    (by norm_num : (2 : ℝ) ≠ 0), one_smul]

end Finsupp

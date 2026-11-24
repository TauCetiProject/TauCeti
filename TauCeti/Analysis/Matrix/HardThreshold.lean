/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.EntrywiseOpNorm
public import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Entrywise hard thresholding of matrices

Hard thresholding keeps entries with norm strictly greater than the threshold.
The operator norm error is controlled by the entrywise tolerance and the operator norm
of the support pattern of the reference matrix.

## References

* M. J. Wainwright, *High-Dimensional Statistics* (2019), Theorem 6.23.
-/

public section

open MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {m n 𝕜 : Type*}

/-- Retain entries whose norm strictly exceeds `τ`, and replace every other entry by zero. -/
noncomputable def hardThreshold [Norm 𝕜] [Zero 𝕜] (A : Matrix m n 𝕜) (τ : ℝ) :
    Matrix m n 𝕜 :=
  A.map fun a ↦ if τ < ‖a‖ then a else 0

/-- The entry at the threshold itself is mapped to zero. -/
@[simp]
theorem hardThreshold_apply [Norm 𝕜] [Zero 𝕜] (A : Matrix m n 𝕜) (τ : ℝ) (i : m) (j : n) :
    A.hardThreshold τ i j = if τ < ‖A i j‖ then A i j else 0 :=
  (rfl)

/-- A zero or negative threshold leaves a matrix unchanged. -/
theorem hardThreshold_of_nonpos [NormedAddGroup 𝕜] (A : Matrix m n 𝕜)
    {τ : ℝ} (hτ : τ ≤ 0) : A.hardThreshold τ = A := by
  ext i j
  rw [hardThreshold_apply]
  split_ifs with h
  · rfl
  · exact (norm_eq_zero.mp (le_antisymm ((le_of_not_gt h).trans hτ) (norm_nonneg _))).symm

/-- Applying hard thresholding twice at the same threshold leaves the first result unchanged. -/
@[simp]
theorem hardThreshold_hardThreshold [Norm 𝕜] [Zero 𝕜] (A : Matrix m n 𝕜) (τ : ℝ) :
    (A.hardThreshold τ).hardThreshold τ = A.hardThreshold τ := by
  ext i j
  by_cases h : τ < ‖A i j‖ <;> simp [h]

/-- Hard thresholding preserves Hermitian symmetry. -/
theorem IsHermitian.hardThreshold [SeminormedAddCommGroup 𝕜] [StarAddMonoid 𝕜]
    [NormedStarGroup 𝕜] {A : Matrix n n 𝕜} (hA : A.IsHermitian) (τ : ℝ) :
    (A.hardThreshold τ).IsHermitian := by
  refine IsHermitian.ext fun i j ↦ ?_
  simp only [hardThreshold_apply, apply_ite star, star_zero, ← norm_star (A j i), hA.apply]

open scoped Matrix.Norms.L2Operator in
/-- If each row has at most `s` retained entries and each has norm at most `M`,
the hard-thresholded Hermitian matrix has Euclidean operator norm at most `s * M`. -/
theorem IsHermitian.l2_opNorm_hardThreshold_le [RCLike 𝕜] [Fintype n] [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (t : ℝ) {s : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (hs : ∀ i, (Finset.univ.filter fun j ↦ t < ‖A i j‖).card ≤ s)
    (hentry : ∀ i j, t < ‖A i j‖ → ‖A i j‖ ≤ M) :
    ‖A.hardThreshold t‖ ≤ s * M := by
  apply (hA.hardThreshold t).l2_opNorm_le_of_row_sum_le (mul_nonneg (Nat.cast_nonneg _) hM)
  intro i
  calc
    _ ≤ ∑ _j ∈ Finset.univ.filter (fun j ↦ t < ‖A i j‖), M := by
      simp_rw [hardThreshold_apply, apply_ite norm, norm_zero, ← Finset.sum_filter]
      exact Finset.sum_le_sum fun j hj ↦ hentry i j (Finset.mem_filter.1 hj).2
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 (hs i)) hM

/-- Hard thresholding is measurable in the matrix at any fixed threshold. -/
@[fun_prop]
theorem measurable_hardThreshold [SeminormedAddGroup 𝕜] [MeasurableSpace 𝕜]
    [OpensMeasurableSpace 𝕜] (τ : ℝ) :
    Measurable (fun A : Matrix m n 𝕜 ↦ A.hardThreshold τ) := by
  refine Matrix.measurable_iff.2 fun i j ↦ ?_
  simp only [hardThreshold_apply]
  have h : Measurable fun A : Matrix m n 𝕜 ↦ A i j := Matrix.measurable_apply
  exact h.ite
    (measurableSet_lt measurable_const (continuous_norm.measurable.comp h)) measurable_const

open Classical in
/-- The real `0–1` matrix indicating the nonzero entries, including those on the diagonal. -/
noncomputable def supportPattern [Zero 𝕜] (A : Matrix m n 𝕜) : Matrix m n ℝ :=
  A.map fun a ↦ if a = 0 then 0 else 1

open Classical in
/-- The support indicator is zero on precisely the zero entries. -/
@[simp]
theorem supportPattern_apply [Zero 𝕜] (A : Matrix m n 𝕜) (i : m) (j : n) :
    A.supportPattern i j = if A i j = 0 then 0 else 1 :=
  (rfl)

/-- The support pattern of a Hermitian matrix is Hermitian. -/
theorem IsHermitian.supportPattern [AddMonoid 𝕜] [StarAddMonoid 𝕜]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) : A.supportPattern.IsHermitian := by
  refine IsHermitian.ext fun i j ↦ ?_
  have hzero : A j i = 0 ↔ A i j = 0 := by rw [← hA.apply i j, star_eq_zero]
  by_cases h : A j i = 0
  · simp [h, hzero.mp h]
  · simp [h, mt hzero.mpr h]

/-- The absolute row sum of the support pattern counts the nonzero entries in that row. -/
theorem sum_norm_supportPattern_apply [Fintype n] [Zero 𝕜]
    [DecidablePred fun a : 𝕜 ↦ a ≠ 0] (A : Matrix m n 𝕜) (i : m) :
    ∑ j, ‖A.supportPattern i j‖ = ((Finset.univ.filter fun j ↦ A i j ≠ 0).card : ℝ) := by
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : A i j = 0 <;> simp [hj]

/-- A row sparsity bound controls the Euclidean operator norm of the support pattern of a
Hermitian matrix. -/
theorem IsHermitian.l2_opNorm_supportPattern_le [Fintype n] [DecidableEq n]
    [AddMonoid 𝕜] [StarAddMonoid 𝕜] [DecidablePred fun a : 𝕜 ↦ a ≠ 0]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {s : ℕ}
    (hs : ∀ i, (Finset.univ.filter fun j ↦ A i j ≠ 0).card ≤ s) :
    ‖A.supportPattern‖ ≤ (s : ℝ) := by
  apply hA.supportPattern.l2_opNorm_le_of_row_sum_le (by positivity)
  intro i
  rw [sum_norm_supportPattern_apply]
  exact_mod_cast hs i

/-- Where the population entry is zero, thresholding removes an estimation error of at
most `τ`. Each nonzero population entry incurs an error of at most `2 * τ`. -/
theorem norm_hardThreshold_sub_apply_le [SeminormedAddGroup 𝕜]
    (A B : Matrix m n 𝕜) {τ : ℝ} (i : m) (j : n) (h : ‖A i j - B i j‖ ≤ τ) :
    ‖(A.hardThreshold τ - B) i j‖ ≤ 2 * τ * B.supportPattern i j := by
  have hτ : 0 ≤ τ := (norm_nonneg _).trans h
  by_cases hB : B i j = 0
  · simp only [hB, sub_zero] at h
    simp [hardThreshold_apply, hB, not_lt.mpr h]
  simp only [Matrix.sub_apply, supportPattern_apply, ite_eq_right hB, mul_one, hardThreshold_apply]
  split_ifs with hA
  · linarith
  · rw [zero_sub, norm_neg]
    calc
      ‖B i j‖ ≤ ‖A i j‖ + ‖A i j - B i j‖ := norm_le_norm_add_norm_sub _ _
      _ ≤ 2 * τ := by linarith [not_lt.mp hA]

/-- The operator norm of the thresholded error is bounded by twice the entrywise
tolerance times the operator norm of the population support pattern. -/
theorem l2_opNorm_hardThreshold_sub_le [RCLike 𝕜] [Fintype m] [Fintype n] [DecidableEq n]
    (A B : Matrix m n 𝕜) {τ : ℝ} (h : ∀ i j, ‖A i j - B i j‖ ≤ τ) :
    ‖A.hardThreshold τ - B‖ ≤ 2 * τ * ‖B.supportPattern‖ := by
  rcases isEmpty_or_nonempty m with hm | ⟨⟨i⟩⟩
  · rw [Subsingleton.elim (A.hardThreshold τ - B) 0, Subsingleton.elim B.supportPattern 0]
    simp
  rcases isEmpty_or_nonempty n with hn | ⟨⟨j⟩⟩
  · rw [Subsingleton.elim (A.hardThreshold τ - B) 0, Subsingleton.elim B.supportPattern 0]
    simp
  have hτ : 0 ≤ τ := (norm_nonneg _).trans (h i j)
  calc
    _ ≤ ‖(2 * τ) • B.supportPattern‖ :=
      (A.hardThreshold τ - B).l2_opNorm_le_of_norm_apply_le _ fun k l ↦
        norm_hardThreshold_sub_apply_le A B k l (h k l)
    _ = _ := by rw [norm_smul, Real.norm_of_nonneg (by positivity)]

end Matrix

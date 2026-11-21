/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Resolvent.LeaveOneOut
public import TauCeti.Analysis.Matrix.Resolvent.RankBound
import TauCeti.LinearAlgebra.Matrix.Trace.Basic
import TauCeti.Analysis.Matrix.L2OpNorm
import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Resolvent trace estimates from principal minors

Deleting a row and column changes the unnormalized resolvent trace by at most
`3 / |Im z|`. The scalar Schur complement then expresses the error in the quadratic
equation for the normalized trace in terms of the errors in its leave-one-out quadratic forms.
This is the deterministic part of the resolvent proof of the Wigner semicircle law.

## References

* G. W. Anderson, A. Guionnet, and O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press, 2010, §2.4.1.
-/

public section

noncomputable section

open MeasureTheory Matrix
open scoped NNReal Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The quadratic form of column `i` against the minor resolvent minus the minor trace
times the variance `v / Fintype.card n`. -/
def minorQuadraticError (A : Matrix n n ℂ) (i : n) (z : ℂ) (v : ℝ≥0) : ℂ :=
  let a : {j // j ≠ i} → ℂ := fun j ↦ A j i
  star a ⬝ᵥ A.minorResolvent i z *ᵥ a -
    ((v : ℂ) / (Fintype.card n : ℂ)) * (A.minorResolvent i z).trace

/-- The defining formula for the variance-centered minor quadratic form. -/
theorem minorQuadraticError_def (A : Matrix n n ℂ) (i : n) (z : ℂ) (v : ℝ≥0) :
    A.minorQuadraticError i z v =
      star (fun j : {j // j ≠ i} ↦ A j i) ⬝ᵥ
        A.minorResolvent i z *ᵥ (fun j : {j // j ≠ i} ↦ A j i) -
        ((v : ℂ) / (Fintype.card n : ℂ)) * (A.minorResolvent i z).trace := by
  rw [minorQuadraticError]

end Matrix

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

/-- Removing one row and column changes the unnormalized resolvent trace by at most
`3 / |Im z|`. The trace of the empty minor of a one-by-one matrix is zero. -/
theorem norm_trace_inv_sub_smul_one_sub_trace_submatrix_le (hA : A.IsHermitian)
    (i : n) {z : ℂ} (hz : z.im ≠ 0) :
    ‖(A - z • 1)⁻¹.trace -
      (A.minorResolvent i z).trace‖ ≤
      3 / |z.im| := by
  let e := Equiv.sumCompl (· = i)
  let B : Matrix {j // j ≠ i} {j // j ≠ i} ℂ := A.submatrix (↑) (↑)
  let C : Matrix ({j // j = i} ⊕ {j // j ≠ i}) _ ℂ :=
    Matrix.fromBlocks (0 : Matrix {j // j = i} {j // j = i} ℂ) 0 0 B
  have hB : B.IsHermitian := hA.submatrix _
  have hC : C.IsHermitian := isHermitian_zero.fromBlocks (by simp) hB
  have hsplit : A.submatrix e e - C =
      vecMulVec (fun j ↦ A (e j) i) (fun j ↦ if e j = i then 1 else 0) +
        vecMulVec (fun j ↦ if e j = i then 1 else 0)
          (fun j ↦ if e j = i then 0 else A i (e j)) := by
    ext (⟨j, hj⟩ | ⟨j, hj⟩) (⟨k, hk⟩ | ⟨k, hk⟩) <;>
      simp [e, C, B, hj, hk, vecMulVec_apply]
  have hrank : (A.submatrix e e - C).rank ≤ 2 := by
    rw [hsplit]
    exact (rank_add_le _ _).trans (add_le_add (rank_vecMulVec_le _ _) (rank_vecMulVec_le _ _))
  have htrace :
      (C - z • 1)⁻¹.trace = (-z)⁻¹ + (B - z • 1)⁻¹.trace := by
    have hblock : C - z • 1 = Matrix.fromBlocks (-z • 1) 0 0 (B - z • 1) := by
      ext (j | j) (k | k) <;> simp [C, Matrix.one_apply]
    have hinv := inv_fromBlocks_zero₂₁_of_isUnit_iff
      (-z • (1 : Matrix {j // j = i} {j // j = i} ℂ)) 0 (B - z • 1)
    have hu : IsUnit (-z • (1 : Matrix {j // j = i} {j // j = i} ℂ)) := by
      simpa only [zero_sub, neg_smul] using
        (isHermitian_zero (n := {j // j = i}) (α := ℂ)).isUnit_sub_smul_one_of_im_ne_zero hz
    rw [hblock, hinv (iff_of_true hu (hB.isUnit_sub_smul_one_of_im_ne_zero hz))]
    simp [Matrix.trace, Fintype.sum_sum_type, inv_subsingleton, smul_one_eq_diagonal]
  have h := (hA.submatrix e).norm_trace_inv_sub_smul_one_sub_le_rank hC hz
  have hreindex : (A.submatrix e e - z • 1)⁻¹.trace = (A - z • 1)⁻¹.trace := by
    have hshift : (A - z • 1).submatrix e e = A.submatrix e e - z • 1 := by
      simp only [submatrix_sub, submatrix_smul, Pi.sub_apply, Pi.smul_apply, submatrix_one_equiv]
    rw [← hshift, inv_submatrix_equiv]
    exact trace_reindex_self e.symm _
  rw [hreindex, htrace] at h
  rw [minorResolvent_def]
  calc
    _ ≤ ‖(A - z • 1)⁻¹.trace - ((-z)⁻¹ + (B - z • 1)⁻¹.trace)‖ + ‖(-z)⁻¹‖ := by
      simpa only [add_sub_cancel_right, norm_neg] using
        norm_sub_le_norm_sub_add_norm_sub (A - z • 1)⁻¹.trace
          ((-z)⁻¹ + (B - z • 1)⁻¹.trace) (B - z • 1)⁻¹.trace
    _ ≤ 2 / |z.im| + 1 / |z.im| := by
      refine add_le_add (h.trans (div_le_div_of_nonneg_right (by exact_mod_cast hrank)
        (abs_nonneg _))) ?_
      rw [norm_inv, norm_neg, one_div]
      exact inv_anti₀ (abs_pos.mpr hz) (Complex.abs_im_le_norm _)
    _ = _ := by ring

/-- Normalizing the principal-minor trace by the original dimension bounds its difference
from the original spectral transform by `3 / (card n * |Im z|)`. -/
theorem norm_normalized_minor_trace_sub_resolventTransform_le [Nonempty n]
    (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (i : n) :
    ‖(Fintype.card n : ℂ)⁻¹ * (A.minorResolvent i z).trace -
      resolventTransform (A.spectralMeasure hA : Measure ℝ) z‖ ≤
      3 / ((Fintype.card n : ℝ) * |z.im|) := by
  rw [resolventTransform_spectralMeasure A hA (hA.notMem_spectrum_of_im_ne_zero hz),
    ← mul_sub, norm_mul, norm_inv, Complex.norm_natCast, norm_sub_rev]
  exact (mul_le_mul_of_nonneg_left (hA.norm_trace_inv_sub_smul_one_sub_trace_submatrix_le i hz)
    (by positivity)).trans_eq (by ring)

/-- The quadratic residual of a normalized Hermitian resolvent trace is bounded by its
mean absolute leave-one-out error divided by `Im z`. -/
theorem norm_resolventTransform_spectralMeasure_quadratic_le [Nonempty n]
    (hA : A.IsHermitian) {z : ℂ} (hz : 0 < z.im) (v : ℂ) :
    let m := resolventTransform (A.spectralMeasure hA : Measure ℝ) z
    ‖v * (m * m) + z * m + 1‖ ≤ (z.im * Fintype.card n)⁻¹ * ∑ i,
      ‖A i i + v * m - star (fun j : {j // j ≠ i} ↦ A j i) ⬝ᵥ
        (A.minorResolvent i z *ᵥ fun j : {j // j ≠ i} ↦ A j i)‖ := by
  classical
  intro m
  let R := (A - z • 1)⁻¹
  have hm : m = (Fintype.card n : ℂ)⁻¹ * R.trace :=
    resolventTransform_spectralMeasure A hA (hA.notMem_spectrum_of_im_ne_zero hz.ne')
  have hc : (Fintype.card n : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have havg :
      v * (m * m) + z * m + 1 = (Fintype.card n : ℂ)⁻¹ * ∑ i, (1 + R i i * (z + v * m)) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    simp only [Matrix.trace, Matrix.diag] at hm
    linear_combination (z + v * m) * hm + (inv_mul_cancel₀ hc).symm
  rw [havg, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card n : ℝ)⁻¹ * ∑ i, ‖1 + R i i * (z + v * m)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (Fintype.card n : ℝ)⁻¹ * ∑ i, (z.im)⁻¹ *
        ‖A i i + v * m - star (fun j : {j // j ≠ i} ↦ A j i) ⬝ᵥ
          (A.minorResolvent i z *ᵥ fun j : {j // j ≠ i} ↦ A j i)‖ := by
      gcongr with i _
      have hmul := mul_inv_cancel₀ (ne_of_apply_ne Complex.im
        (by simpa using (hA.im_inv_sub_smul_one_apply_self_pos hz i).ne') : R i i ≠ 0)
      rw [hA.inv_inv_sub_smul_one_apply_self hz.ne' i] at hmul
      have hid : 1 + R i i * (z + v * m) = R i i *
          (A i i + v * m - star (fun j : {j // j ≠ i} ↦ A j i) ⬝ᵥ
            (A.minorResolvent i z *ᵥ fun j : {j // j ≠ i} ↦ A j i)) := by
        linear_combination -hmul
      rw [hid, norm_mul]
      refine mul_le_mul_of_nonneg_right
        ((Matrix.norm_apply_le_l2_opNorm _ _ _).trans ?_) (norm_nonneg _)
      simpa only [R, RCLike.im_eq_complex_im, abs_of_pos hz] using
        hA.l2_opNorm_inv_sub_smul_one_le hz.ne'
    _ = _ := by rw [← Finset.mul_sum]; ring

end Matrix.IsHermitian

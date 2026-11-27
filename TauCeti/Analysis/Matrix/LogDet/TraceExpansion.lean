/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import TauCeti.Analysis.Matrix.Eigenvalues.Schur.Basic
import TauCeti.Analysis.Matrix.Frobenius
import TauCeti.LinearAlgebra.Matrix.Triangular

/-!
# The trace expansion of the determinant near the identity

For a complex square matrix `Y` of Frobenius norm `‖Y‖ < 1`, the determinant `det (1 + Y)` is the
exponential of the trace of the logarithm series of `1 + Y`:
`det (1 + Y) = exp (∑ j ≥ 1, (-1) ^ (j + 1) tr (Y ^ j) / j)`. The series is the analytic logarithm
of `det (1 + Y)` normalized to vanish at `Y = 0`. It need not be the principal logarithm
`Complex.log (det (1 + Y))`: the two can differ by a multiple of `2πi`, since in large dimension
the arguments of the factors `1 + λ` over the eigenvalues `λ` of `Y` can add up to more than `π`.
This file proves the truncated form with an explicit remainder: for `k ≥ 1`,
`det (1 + Y) = exp (∑ j ≤ k, (-1) ^ (j + 1) tr (Y ^ j) / j + r)` with
`‖r‖ ≤ ‖Y‖ ^ (k + 1) / ((k + 1) (1 - ‖Y‖))`.

The bound does not depend on the size of `Y`. This is why the Frobenius norm is used: the
eigenvalues `λ` of `Y` satisfy `∑ |λ| ^ 2 ≤ ‖Y‖ ^ 2` (Schur's inequality), so for `k ≥ 1` the
remainders `∑ |λ| ^ (k + 1)` are at most `‖Y‖ ^ (k + 1)`. For `k = 0` no such bound holds: the
first-order term `tr Y` is not small compared with `‖Y‖` in large dimension.

The proof triangularizes `Y` by a unitary matrix (`Matrix.exists_unitary_isUpperTriangular`), which
turns `det (1 + Y)` into the product of the `1 + λ` and `tr (Y ^ j)` into the sum of the `λ ^ j`
over the diagonal entries `λ`, and applies the bound
`Complex.norm_log_sub_logTaylor_le` for the scalar logarithm to each diagonal entry.

## Main results

* `Matrix.exists_det_one_add_eq_exp_sum_trace_pow`: the expansion of `det (1 + Y)` to order `k`
  with the remainder bound above.

## References

* I. Schur, *Über die charakteristischen Wurzeln einer linearen Substitution mit einer Anwendung
  auf die Theorie der Integralgleichungen*, Math. Ann. 66 (1909), 488–510.
-/

public section

open Finset Complex
open scoped Matrix Matrix.Norms.Frobenius

namespace Matrix

variable {n : Type*} [Fintype n]

/-- The remainders of the logarithm series at numbers `t i` of norm at most `y < 1` whose squared
norms sum to at most `y ^ 2` add up to at most `y ^ (k + 1) / ((k + 1) (1 - y))`, for `k ≥ 1`. -/
private theorem norm_sum_log_sub_logTaylor_le {t : n → ℂ} {y : ℝ} (hy0 : 0 ≤ y) (hy : y < 1)
    (hti : ∀ i, ‖t i‖ ≤ y) (hsq : ∑ i, ‖t i‖ ^ 2 ≤ y ^ 2) {k : ℕ} (hk : 1 ≤ k) :
    ‖∑ i, (log (1 + t i) - logTaylor (k + 1) (t i))‖ ≤ y ^ (k + 1) * (1 - y)⁻¹ / (k + 1) := by
  have : 0 < 1 - y := by linarith
  calc ‖∑ i, (log (1 + t i) - logTaylor (k + 1) (t i))‖
      ≤ ∑ i, ‖t i‖ ^ (k + 1) * (1 - ‖t i‖)⁻¹ / (k + 1) :=
        (norm_sum_le _ _).trans (sum_le_sum fun i _ ↦
          norm_log_sub_logTaylor_le k ((hti i).trans_lt hy))
    _ ≤ ∑ i, y ^ (k - 1) * ‖t i‖ ^ 2 * (1 - y)⁻¹ / (k + 1) := by
        refine sum_le_sum fun i _ ↦ ?_
        have hpow : ‖t i‖ ^ (k + 1) ≤ y ^ (k - 1) * ‖t i‖ ^ 2 := by
          obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
          rw [show l + 1 + 1 = l + 2 by ring, pow_add, show l + 1 - 1 = l by omega]
          gcongr
          exact hti i
        have h2 : 0 ≤ (1 - ‖t i‖)⁻¹ := inv_nonneg.mpr (by linarith [hti i])
        gcongr
        exact hti i
    _ = y ^ (k - 1) * (∑ i, ‖t i‖ ^ 2) * (1 - y)⁻¹ / (k + 1) := by
        rw [mul_sum, sum_mul, sum_div]
    _ ≤ y ^ (k - 1) * y ^ 2 * (1 - y)⁻¹ / (k + 1) := by gcongr
    _ = y ^ (k + 1) * (1 - y)⁻¹ / (k + 1) := by
        rw [← pow_add, show k - 1 + 2 = k + 1 by omega]

/-- The expansion for an index type with a linear order, which the triangularization uses. -/
private theorem exists_det_one_add_eq_exp_sum_trace_pow_aux [LinearOrder n] (Y : Matrix n n ℂ)
    (hY : ‖Y‖ < 1) {k : ℕ} (hk : 1 ≤ k) :
    ∃ r : ℂ, (1 + Y).det =
        Complex.exp (∑ j ∈ range (k + 1), (-1) ^ (j + 1) * (Y ^ j).trace / j + r) ∧
      ‖r‖ ≤ ‖Y‖ ^ (k + 1) * (1 - ‖Y‖)⁻¹ / (k + 1) := by
  obtain ⟨U, hT⟩ := Y.exists_unitary_isUpperTriangular
  set T := star U.val * Y * U.val with hTdef
  have hUU : star U.val * U.val = 1 := UnitaryGroup.star_mul_self U
  have hUU' : U.val * star U.val = 1 := mem_unitaryGroup_iff.mp U.property
  have hY' : Y = U.val * T * star U.val := by
    simp only [hTdef, ← Matrix.mul_assoc, hUU', Matrix.one_mul]
    rw [Matrix.mul_assoc, hUU', Matrix.mul_one]
  -- `t` lists the eigenvalues of `Y`, the diagonal entries of `T`
  set t : n → ℂ := fun i ↦ T i i
  have hTnorm : ‖T‖ = ‖Y‖ := by
    rw [UnitaryGroup.frobenius_norm_mul_right U, ← Unitary.coe_star,
      UnitaryGroup.frobenius_norm_mul_left]
  have hti (i : n) : ‖t i‖ ≤ ‖Y‖ := hTnorm ▸ norm_apply_le_frobenius_norm T i i
  have hsq : ∑ i, ‖t i‖ ^ 2 ≤ ‖Y‖ ^ 2 := by
    rw [← hTnorm, frobenius_norm_sq_eq_sum_norm_sq]
    exact sum_le_sum fun i _ ↦ single_le_sum (f := fun j ↦ ‖T i j‖ ^ 2)
      (fun _ _ ↦ sq_nonneg _) (mem_univ i)
  have hdet : (1 + Y).det = ∏ i, (1 + t i) := by
    have h1 : 1 + Y = U.val * (1 + T) * star U.val := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hUU', ← hY']
    rw [h1, det_conj_of_mul_eq_one hUU' hUU, det_of_isUpperTriangular (blockTriangular_one.add hT)]
    simp [t]
  have htr (j : ℕ) : (Y ^ j).trace = ∑ i, t i ^ j := by
    have hpow : Y ^ j = U.val * T ^ j * star U.val :=
      hY' ▸ Units.conj_pow ⟨U.val, star U.val, hUU', hUU⟩ T j
    rw [hpow, trace_mul_cycle, hUU, Matrix.one_mul]
    simp [trace, t, pow_apply_diag_of_isUpperTriangular hT]
  refine ⟨∑ i, (log (1 + t i) - logTaylor (k + 1) (t i)), ?_, ?_⟩
  · have hne (i : n) : 1 + t i ≠ 0 := by
      intro h
      have : ‖t i‖ = 1 := by rw [eq_neg_of_add_eq_zero_right h, norm_neg, norm_one]
      linarith [hti i]
    have hlog : ∑ j ∈ range (k + 1), (-1) ^ (j + 1) * (Y ^ j).trace / j =
        ∑ i, logTaylor (k + 1) (t i) := by
      simp only [htr, logTaylor, mul_sum, sum_div]
      exact sum_comm
    rw [hdet, hlog, ← sum_add_distrib]
    simp only [add_sub_cancel, Complex.exp_sum]
    exact prod_congr rfl fun i _ ↦ (Complex.exp_log (hne i)).symm
  · exact norm_sum_log_sub_logTaylor_le (norm_nonneg _) hY hti hsq hk

/-- **The trace expansion of the determinant with a remainder independent of the size.** For a
complex square matrix `Y` of Frobenius norm `‖Y‖ < 1` and `k ≥ 1`,
`det (1 + Y) = exp (∑ j ≤ k, (-1) ^ (j + 1) tr (Y ^ j) / j + r)` with
`‖r‖ ≤ ‖Y‖ ^ (k + 1) / ((k + 1) (1 - ‖Y‖))`. (The term `j = 0` of the sum is `0`.) The sum
truncates at order `k` the logarithm series, the analytic logarithm of `det (1 + Y)` normalized to
vanish at `Y = 0`, which can differ from the principal logarithm `Complex.log (det (1 + Y))` by a
multiple of `2πi`. -/
theorem exists_det_one_add_eq_exp_sum_trace_pow [DecidableEq n] (Y : Matrix n n ℂ)
    (hY : ‖Y‖ < 1) {k : ℕ} (hk : 1 ≤ k) :
    ∃ r : ℂ, (1 + Y).det =
        Complex.exp (∑ j ∈ range (k + 1), (-1) ^ (j + 1) * (Y ^ j).trace / j + r) ∧
      ‖r‖ ≤ ‖Y‖ ^ (k + 1) * (1 - ‖Y‖)⁻¹ / (k + 1) := by
  let _ : LinearOrder n := LinearOrder.lift' _ (Fintype.equivFin n).injective
  -- the decidable equality of the order agrees with the given one up to `Subsingleton`
  convert exists_det_one_add_eq_exp_sum_trace_pow_aux Y hY hk

end Matrix

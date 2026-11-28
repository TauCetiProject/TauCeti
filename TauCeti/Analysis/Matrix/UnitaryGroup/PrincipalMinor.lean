/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.LinearAlgebra.Matrix.Minor
import TauCeti.Analysis.Matrix.Frobenius
import TauCeti.Analysis.Matrix.PosSemidef.Determinant
import TauCeti.Analysis.Matrix.UnitaryGroup.Basic

/-!
# Principal minors of unitary matrices

Let `k` be a unitary matrix, `s` a finite set of indices and `P` the coordinate projection onto
`s`. The principal minor of `k` on `s` is small when `k` moves the coordinates in `s` far from
themselves: `‖det k_s‖ ^ 2 ≤ exp (-‖[P, k]‖ ^ 2 / 2)` in the Frobenius norm.

Write `a = k_s` for the block of `k` on `s`. The rows and the columns of `k` are unit vectors, so
the block of `k` on `s × sᶜ` and the block on `sᶜ × s` both have squared norm `#s - ‖a‖ ^ 2`, and
`‖[P, k]‖ ^ 2`, the sum of these two, is `2 (#s - ‖a‖ ^ 2)`. On the other hand
`‖det a‖ ^ 2 = det (a aᴴ) ≤ exp (tr (a aᴴ) - #s) = exp (‖a‖ ^ 2 - #s)` by the determinant–trace
inequality `Matrix.PosSemidef.re_det_le_exp_re_trace_sub_card`.

## Main results

* `Matrix.norm_principalMinor_sq_le_exp`: `‖det k_s‖ ^ 2 ≤ exp (-‖[P, k]‖ ^ 2 / 2)` for a unitary
  matrix `k`.
-/

public section

open scoped ComplexOrder Matrix Matrix.Norms.Frobenius

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- **A principal minor of a unitary matrix is small when the matrix moves its coordinates.**
For a unitary matrix `k`, a finite set `s` of indices and the coordinate projection `P` onto `s`,
`‖det k_s‖ ^ 2 ≤ exp (-‖[P, k]‖ ^ 2 / 2)`, in the Frobenius norm. -/
theorem norm_principalMinor_sq_le_exp (k : Matrix n n 𝕜) (hk : k ∈ unitaryGroup n 𝕜)
    (s : Finset n) :
    ‖k.principalMinor s‖ ^ 2 ≤
      Real.exp (-‖⁅diagonal fun i ↦ if i ∈ s then (1 : 𝕜) else 0, k⁆‖ ^ 2 / 2) := by
  set a := k.submatrix (Subtype.val : s → n) (Subtype.val : s → n)
  -- `q` is the real indicator of `s`
  set q : n → ℝ := fun i ↦ if i ∈ s then 1 else 0
  have hqa : ‖a‖ ^ 2 = ∑ i, ∑ j, q i * q j * ‖k i j‖ ^ 2 := by
    calc ‖a‖ ^ 2 = ∑ i : s, ∑ j : s, ‖k i j‖ ^ 2 := frobenius_norm_sq_eq_sum_norm_sq a
      _ = ∑ i ∈ s, ∑ j ∈ s, ‖k i j‖ ^ 2 := by
          rw [Finset.sum_coe_sort s fun i ↦ ∑ j : s, ‖k i j‖ ^ 2]
          exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_coe_sort s fun j ↦ ‖k i j‖ ^ 2
      _ = _ := by simp [q, ite_mul, Finset.sum_ite_mem]
  have hcomm : ‖⁅diagonal fun i ↦ if i ∈ s then (1 : 𝕜) else 0, k⁆‖ ^ 2 =
      ∑ i, ∑ j, (q i + q j - 2 * q i * q j) * ‖k i j‖ ^ 2 := by
    rw [frobenius_norm_sq_eq_sum_norm_sq]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases hi : i ∈ s <;> by_cases hj : j ∈ s <;>
      simp [Ring.lie_def, hi, hj, q, one_add_one_eq_two]
  have hrow : ∑ i, ∑ j, q i * ‖k i j‖ ^ 2 = s.card := by
    simp only [← Finset.mul_sum, sum_norm_sq_row_of_mem_unitaryGroup hk, mul_one, q,
      Finset.sum_boole]
    simp
  have hcol : ∑ i, ∑ j, q j * ‖k i j‖ ^ 2 = s.card := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, sum_norm_sq_col_of_mem_unitaryGroup hk, mul_one, q,
      Finset.sum_boole]
    simp
  have hsplit : ∑ i, ∑ j, (q i + q j - 2 * q i * q j) * ‖k i j‖ ^ 2 =
      ∑ i, ∑ j, q i * ‖k i j‖ ^ 2 + ∑ i, ∑ j, q j * ‖k i j‖ ^ 2 -
        2 * ∑ i, ∑ j, q i * q j * ‖k i j‖ ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  have hdet : ‖k.principalMinor s‖ ^ 2 = RCLike.re (a * aᴴ).det := by
    rw [principalMinor_def, det_mul, det_conjTranspose, RCLike.star_def, RCLike.mul_conj,
      ← RCLike.ofReal_pow, RCLike.ofReal_re]
  have htr : RCLike.re (a * aᴴ).trace = ‖a‖ ^ 2 := by
    rw [re_trace_mul_conjTranspose_self, frobenius_norm_sq_eq_sum_norm_sq]
  rw [hdet, hcomm, hsplit, hrow, hcol, ← hqa]
  refine (posSemidef_self_mul_conjTranspose a).re_det_le_exp_re_trace_sub_card.trans_eq ?_
  rw [htr, Fintype.card_coe]
  ring_nf

end Matrix

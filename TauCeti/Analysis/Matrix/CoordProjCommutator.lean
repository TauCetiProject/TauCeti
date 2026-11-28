/-
Copyright (c) 2026 TauCeti Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Data.Int.Interval
public import Mathlib.LinearAlgebra.Matrix.Trace

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

/-!
# Commutator Frobenius-norm and trace sums over threshold coordinate projections

For an integer weight `w : n → ℤ` taking values in `[a, b]` and threshold projections
`P_t = Matrix.diagonal (fun i ↦ if t ≤ w i then 1 else 0)` (`a < t ≤ b`), this file proves:

* `TauCeti.gapWeightedNormSq`: the quadratic form `∑ i, ∑ j, |w i - w j| * ‖X i j‖ ^ 2`.
* `TauCeti.gapWeightedNormSq_nonneg`: nonnegativity of `gapWeightedNormSq w X`.
* `TauCeti.sum_norm_commutator_coordProj_sq`: the squared Frobenius norms of the commutators
  `P_t * X - X * P_t` summed over `t ∈ Ioc a b` equal `gapWeightedNormSq w X`.
* `TauCeti.sum_trace_coordProj_mul`: over any commutative ring `R`, the traces `(P_t * X).trace`
  summed over `t ∈ Ioc a b` equal `(diagonal (w ·) * X).trace - a * X.trace`.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file
`src/New/Appendix/DiscreteSeries/GaussianShape.lean` (`New.DiscreteSeries.gapWeightedNormSq`,
`New.DiscreteSeries.gapWeightedNormSq_nonneg`, `New.DiscreteSeries.sum_norm_lie_coordProj_sq`,
`New.DiscreteSeries.sum_trace_coordProj_mul`).
-/

@[expose] public section

namespace TauCeti

open Finset Matrix

/-- The gap-weighted squared Frobenius quadratic form
`Q_w (X) = ∑_{i, j} |w i - w j| * ‖X i j‖ ^ 2`. -/
noncomputable def gapWeightedNormSq {n : Type*} [Fintype n] (w : n → ℤ) (X : Matrix n n ℂ) : ℝ :=
  ∑ i : n, ∑ j : n, (|w i - w j| : ℝ) * ‖X i j‖ ^ 2

/-- The gap-weighted quadratic form `gapWeightedNormSq w X` is nonnegative. -/
theorem gapWeightedNormSq_nonneg {n : Type*} [Fintype n] (w : n → ℤ) (X : Matrix n n ℂ) :
    0 ≤ gapWeightedNormSq w X := by
  unfold gapWeightedNormSq
  positivity

section Frobenius

open Matrix.Norms.Frobenius

/-- Let the entries of `w : n → ℤ` lie in `[a, b]`, and let `P_t` be the diagonal projection onto
`{i | t ≤ w i}`. The squared Frobenius norms of the commutators `P_t * X - X * P_t` for
`t ∈ Ioc a b` sum to `gapWeightedNormSq w X`, because exactly `|w i - w j|` thresholds separate
`i` from `j`. -/
theorem sum_norm_commutator_coordProj_sq {n : Type*} [Fintype n] [DecidableEq n] {w : n → ℤ}
    {a b : ℤ} (hw : ∀ i : n, a ≤ w i ∧ w i ≤ b) (X : Matrix n n ℂ) :
    ∑ t ∈ Ioc a b,
        ‖diagonal (fun i ↦ if t ≤ w i then (1 : ℂ) else 0) * X -
          X * diagonal (fun i ↦ if t ≤ w i then (1 : ℂ) else 0)‖ ^ 2 =
      gapWeightedNormSq w X := by
  have h_card (i j : n) : (#{t ∈ Ioc a b | ¬(t ≤ w i ↔ t ≤ w j)} : ℤ) = |w i - w j| := by
    rw [show {t ∈ Ioc a b | ¬(t ≤ w i ↔ t ≤ w j)} = Ioc (w i ⊓ w j) (w i ⊔ w j) by grind,
      Int.card_Ioc, max_sub_min_eq_abs', Int.toNat_of_nonneg (abs_nonneg _)]
  have h_sq (B : Matrix n n ℂ) : ‖B‖ ^ 2 = ∑ i : n, ∑ j : n, ‖B i j‖ ^ 2 := by
    rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
    simp
  have h_entry (t : ℤ) (i j : n) :
      ‖(diagonal (fun k ↦ if t ≤ w k then (1 : ℂ) else 0) * X -
          X * diagonal (fun k ↦ if t ≤ w k then (1 : ℂ) else 0)) i j‖ ^ 2 =
        if t ≤ w i ↔ t ≤ w j then 0 else ‖X i j‖ ^ 2 := by
    by_cases hi : t ≤ w i <;> by_cases hj : t ≤ w j <;>
      simp [Matrix.sub_apply, diagonal_mul, mul_diagonal, hi, hj]
  simp only [h_sq, h_entry, gapWeightedNormSq, (Ioc a b).sum_comm]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  rw [sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul]
  exact congrArg (· * ‖X i j‖ ^ 2) (by exact_mod_cast h_card i j)

end Frobenius

/-- If the entries of `w : n → ℤ` lie in `[a, b]`, the threshold coordinate projections onto
`{i | t ≤ w i}` for `t ∈ Ioc a b` sum to `diagonal w - a • 1`; taking traces against `X` yields
the corresponding trace identity over any commutative ring `R`. -/
theorem sum_trace_coordProj_mul {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    {w : n → ℤ} {a b : ℤ} (hw : ∀ i : n, a ≤ w i ∧ w i ≤ b) (X : Matrix n n R) :
    ∑ t ∈ Ioc a b, (diagonal (fun i ↦ if t ≤ w i then (1 : R) else 0) * X).trace =
      (diagonal (fun i ↦ (w i : R)) * X).trace - (a : R) * X.trace := by
  have h_card (i : n) : (#{t ∈ Ioc a b | t ≤ w i} : ℤ) = w i - a := by
    rw [show {t ∈ Ioc a b | t ≤ w i} = Ioc a (w i) by grind, Int.card_Ioc,
      Int.toNat_of_nonneg (sub_nonneg.mpr (hw i).left)]
  simp only [trace, diag_apply, diagonal_mul, (Ioc a b).sum_comm, mul_sum,
    ← sum_sub_distrib, ← sub_mul]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← sum_mul, sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one,
    ← Int.cast_sub, ← h_card i, Int.cast_natCast]

end TauCeti

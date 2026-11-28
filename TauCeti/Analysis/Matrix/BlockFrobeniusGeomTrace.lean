/-
Copyright (c) 2026 TauCeti Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Block Frobenius norm bounds and traced matrix geometric series

For a finite block splitting `e : X ⊕ Y ≃ n` and complex matrices with the Frobenius norm, this
file proves:

* `TauCeti.norm_submatrix_inl_le`: the Frobenius norm of the `X × X` principal block of `A` is at
  most `‖A‖`.
* `TauCeti.norm_sq_le_rows_add_columns_add_block`: `‖A‖ ^ 2` is bounded by the sum of the squared
  Frobenius norms of the off-`X` rows, the off-`X` columns, and the `X × X` block of `A`.
* `TauCeti.hasSum_trace_geom`: for `‖A‖ ≤ 2⁻¹` and `r ∈ [0, 1]`, the geometric series for
  `(1 + r • A)⁻¹` may be multiplied by `D` and `A` and traced term by term.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file
`src/New/Appendix/DiscreteSeries/Localization.lean` (`New.DiscreteSeries.norm_onBlock_le`,
`New.DiscreteSeries.norm_sq_le_rows_add_columns_add_block`,
`New.DiscreteSeries.hasSum_trace_geom`).
-/

@[expose] public section

namespace TauCeti

open Finset Matrix
open Matrix.Norms.Frobenius

/-- The Frobenius norm of the principal block `A.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)` is at most
the Frobenius norm of `A`. -/
theorem norm_submatrix_inl_le {X Y n : Type*} [Fintype X] [Fintype n]
    (e : X ⊕ Y ≃ n) (A : Matrix n n ℂ) :
    ‖A.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)‖ ≤ ‖A‖ := by
  have : Fintype Y := Fintype.ofInjective (e ∘ Sum.inr) (e.injective.comp Sum.inr_injective)
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Matrix.frobenius_norm_def,
    Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  simp only [Real.rpow_two, submatrix_apply, Function.comp_apply, ← e.sum_comp,
    Fintype.sum_sum_type, sum_add_distrib, add_assoc, le_add_iff_nonneg_right]
  positivity

/-- The squared Frobenius norm of `A` is at most the sum of the squared Frobenius norms of its
rows off `X`, its columns off `X`, and its `X × X` principal block under `e : X ⊕ Y ≃ n`. -/
theorem norm_sq_le_rows_add_columns_add_block {X Y n : Type*} [Fintype X]
    [Fintype n] [DecidableEq n] (e : X ⊕ Y ≃ n) (A : Matrix n n ℂ) :
    ‖A‖ ^ 2 ≤
      ‖diagonal (fun i ↦ (e.symm i).elim (fun _ ↦ (0 : ℂ)) (fun _ ↦ 1)) * A‖ ^ 2 +
        ‖A * diagonal (fun i ↦ (e.symm i).elim (fun _ ↦ (0 : ℂ)) (fun _ ↦ 1))‖ ^ 2 +
        ‖A.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)‖ ^ 2 := by
  have : Fintype Y := Fintype.ofInjective (e ∘ Sum.inr) (e.injective.comp Sum.inr_injective)
  have h_count :
      ‖diagonal (fun i ↦ (e.symm i).elim (fun _ ↦ (0 : ℂ)) (fun _ ↦ 1)) * A‖ ^ 2 +
          ‖A * diagonal (fun i ↦ (e.symm i).elim (fun _ ↦ (0 : ℂ)) (fun _ ↦ 1))‖ ^ 2 +
          ‖A.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)‖ ^ 2 =
        ‖A‖ ^ 2 + ∑ a : Y, ∑ b : Y, ‖A (e (.inr a)) (e (.inr b))‖ ^ 2 := by
    simp only [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.rpow_two]
    repeat rw [Real.sq_sqrt (by positivity)]
    simp only [diagonal_mul, mul_diagonal, submatrix_apply, Function.comp_apply,
      ← e.sum_comp, Fintype.sum_sum_type, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr,
      zero_mul, mul_zero, one_mul, mul_one, norm_zero, zero_pow two_ne_zero, sum_const_zero,
      zero_add, sum_add_distrib]
    ring
  rw [h_count, le_add_iff_nonneg_right]
  positivity

/-- For `‖A‖ ≤ 1 / 2` in the Frobenius norm and `0 ≤ r ≤ 1`, the geometric series of
`(1 + r • A)⁻¹` may be multiplied by `D` and `A` and traced term by term. -/
theorem hasSum_trace_geom {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : ‖A‖ ≤ 2⁻¹) (D : Matrix n n ℂ) {r : ℝ} (hr : r ∈ Set.Icc 0 1) :
    HasSum (fun i : ℕ ↦ (D * ((-(r • A)) ^ i * A)).trace)
      (D * ((1 + r • A)⁻¹ * A)).trace := by
  have h_small : ‖-(r • A)‖ < 1 := by
    rw [norm_neg, norm_smul, Real.norm_of_nonneg hr.left]
    calc r * ‖A‖ ≤ 1 * 2⁻¹ := mul_le_mul hr.right hA (norm_nonneg A) zero_le_one
      _ < 1 := by norm_num
  have h_geom : HasSum (fun i : ℕ ↦ D * ((-(r • A)) ^ i * A))
      (D * (Ring.inverse (1 - -(r • A)) * A)) :=
    ((hasSum_geom_series_inverse (-(r • A)) h_small).mul_right A).mul_left D
  simpa [← nonsing_inv_eq_ringInverse] using
    h_geom.mapL (traceLinearMap n ℂ ℂ).toContinuousLinearMap

end TauCeti

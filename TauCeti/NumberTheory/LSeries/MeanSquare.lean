/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Convergence
public import TauCeti.Analysis.Asymptotics.Sum.Norm
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Absolute convergence from mean-square coefficient bounds

If the partial sums of `‖aₙ‖²` are `O(n^r)`, with `r ≥ -1`, then the Dirichlet series of
`aₙ` converges absolutely on `Re s > (r+1)/2`. Cauchy–Schwarz bounds the partial sums of
`‖aₙ‖`, and Mathlib's `LSeriesSummable_of_sum_norm_bigO` applies Abel summation to them.
No bound on individual coefficients or multiplicativity hypothesis is needed.

For cusp-form coefficients the mean-square exponent is the weight, so the resulting abscissa
bound is `(k+1)/2`. In particular it gives abscissa at most one in weight one.
-/

public section

open Asymptotics Filter Finset

namespace TauCeti

/-- Mean-square growth `O(n^r)` implies absolute convergence of the coefficient Dirichlet
series on `Re s > (r+1)/2`. -/
theorem LSeriesSummable_of_sum_norm_sq_bigO {f : ℕ → ℂ} {r : ℝ} {s : ℂ}
    (h : (fun n ↦ ∑ j ∈ Icc 1 n, ‖f j‖ ^ 2) =O[atTop] fun n ↦ (n : ℝ) ^ r)
    (hr : -1 ≤ r) (hs : (r + 1) / 2 < s.re) : LSeriesSummable f s :=
  LSeriesSummable_of_sum_norm_bigO (isBigO_sum_norm_Icc_of_sum_norm_sq h) (by linarith) hs

namespace LSeries

/-- A mean-square coefficient bound with exponent `r ≥ -1` bounds the abscissa of absolute
convergence by `(r+1)/2`. -/
theorem abscissaOfAbsConv_le_of_sum_norm_sq_bigO {f : ℕ → ℂ} {r : ℝ}
    (h : (fun n ↦ ∑ j ∈ Icc 1 n, ‖f j‖ ^ 2) =O[atTop] fun n ↦ (n : ℝ) ^ r)
    (hr : -1 ≤ r) : _root_.LSeries.abscissaOfAbsConv f ≤ (((r + 1) / 2 : ℝ) : EReal) := by
  refine _root_.LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦ ?_
  exact LSeriesSummable_of_sum_norm_sq_bigO h hr (by simpa using hy)

end LSeries

end TauCeti

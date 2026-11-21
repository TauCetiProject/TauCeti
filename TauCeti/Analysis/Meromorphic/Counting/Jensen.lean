/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.JensenFormula
public import TauCeti.Analysis.Meromorphic.Counting.Basic

/-!
# Jensen's bound for zero counts

Let `f` be analytic on `closedBall c R` and bounded by `M ≥ 1` on `sphere c R`, and let
`0 < r < R`. Jensen's formula bounds the number of zeros of `f` in `closedBall c r`, counted with
multiplicity:

* by `log (M / ‖f c‖) / log (R / r)` when `f c ≠ 0`;
* by `m + (log (M / ‖a‖) - m log R) / log (R / r)` when `f` has finite order `m` at `c` with
  trailing coefficient `a = meromorphicTrailingCoeffAt f c`.

Here both are stated for `TauCeti.zeroCount f U S`, for any region `S ⊆ closedBall c r` and any
domain `U`: the count with respect to `U` never exceeds the count with respect to the disc
(`AnalyticOnNhd.zeroCount_le_finsum_divisor`). Only upper bounds transfer from discs to smaller
regions such as the rectangles that lie in the disc through their corners. These local counts
bound the number of zeros of an entire function of finite order, and of a completed L-function in
a disc of bounded radius.

## Main results

* `AnalyticOnNhd.zeroCount_le` — Jensen's bound when `f c ≠ 0`.
* `AnalyticOnNhd.zeroCount_le_analyticOrderNatAt_add` — Jensen's bound in terms of the order and
  the trailing coefficient of `f` at the centre.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., GTM 74, §11.
* E. C. Titchmarsh, *The Theory of Functions*, 2nd ed., §3.61.
-/

public section

open Metric MeromorphicOn Real

variable {c : ℂ} {r R M : ℝ} {f : ℂ → ℂ} {S : Set ℂ}

/-- **Jensen's bound for a zero count.** Let `f` be analytic on `closedBall c R`, bounded by
`M ≥ 1` on `sphere c R` and nonzero at `c`. For `0 < r < R`, the number of zeros of `f` in any
`S ⊆ closedBall c r`, counted with multiplicity with respect to any domain `U`, is at most
`log (M / ‖f c‖) / log (R / r)`. This is Mathlib's `AnalyticOnNhd.sum_divisor_le`. -/
theorem AnalyticOnNhd.zeroCount_le (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hfc : f c ≠ 0)
    (hbound : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (U : Set ℂ) (hS : S ⊆ closedBall c r) :
    (TauCeti.zeroCount f U S : ℝ) ≤ log (M / ‖f c‖) / log (R / r) := by
  have hR : 0 < R := hr.trans hrR
  have hle := (hf.mono (closedBall_subset_closedBall hrR.le)).zeroCount_le_finsum_divisor
    (isCompact_closedBall c r) U hS
  have hjensen := AnalyticOnNhd.sum_divisor_le (c := c) (r := r) (R := R) (abs_pos.2 hr.ne')
    (by rwa [abs_of_pos hr, abs_of_pos hR]) hM (by rwa [abs_of_pos hR]) hfc
    (by rwa [abs_of_pos hR])
  rw [abs_of_pos hr] at hjensen
  exact (Int.cast_le.2 hle).trans hjensen

/-- **Jensen's bound for a zero count, trailing-coefficient form.** Let `f` be analytic on
`closedBall c R`, bounded by `M ≥ 1` on `sphere c R`, and of finite order `m` at `c` with
trailing coefficient `a`. For `0 < r < R`, the number of zeros of `f` in any
`S ⊆ closedBall c r`, counted with multiplicity with respect to any domain `U`, is at most
`m + (log (M / ‖a‖) - m log R) / log (R / r)`. -/
theorem AnalyticOnNhd.zeroCount_le_analyticOrderNatAt_add (hr : 0 < r) (hrR : r < R)
    (hM : 1 ≤ M) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hfc : analyticOrderAt f c ≠ ⊤)
    (hbound : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (U : Set ℂ) (hS : S ⊆ closedBall c r) :
    (TauCeti.zeroCount f U S : ℝ) ≤
      analyticOrderNatAt f c + (log (M / ‖meromorphicTrailingCoeffAt f c‖) -
        analyticOrderNatAt f c * log R) / log (R / r) :=
  (Int.cast_le.2 <| (hf.mono (closedBall_subset_closedBall hrR.le)).zeroCount_le_finsum_divisor
    (isCompact_closedBall c r) U hS).trans
      (hf.sum_divisor_le_analyticOrderNatAt_add hr hrR hM hfc hbound)

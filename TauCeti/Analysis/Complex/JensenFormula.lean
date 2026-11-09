/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.JensenFormula
import TauCeti.Analysis.Meromorphic.Divisor

/-!
# Jensen's inequality at a zero of the centre

Mathlib's `AnalyticOnNhd.sum_divisor_le` bounds the number of zeros of `f` in `closedBall c r` by
`log (M / ‖f c‖) / log (R / r)` when `f` is analytic on `closedBall c R`, bounded by `M ≥ 1` on
`sphere c R`, and nonzero at the centre. This file removes the last hypothesis: if `f` vanishes to
finite order `m` at `c`, with trailing coefficient `a = meromorphicTrailingCoeffAt f c`, then the
number of zeros in `closedBall c r` is at most `m + (log (M / ‖a‖) - m log R) / log (R / r)`.
For `m = 0` the trailing coefficient is `f c` and this is Mathlib's bound.

The value `‖a‖` cannot simply replace `‖f c‖` in Mathlib's bound: for `f z = z`, `c = 0`,
`r = 1/4`, `R = 1/2` and `M = 1` there is one zero in `closedBall 0 (1/4)` while
`log (M / ‖a‖) / log (R / r) = 0`. Here the bound is `1 + log 2 / log 2 = 2`.

## Main results

* `AnalyticOnNhd.sum_divisor_le_analyticOrderNatAt_add` — Jensen's bound for the number of zeros
  of `f` in a disc about a point where `f` has finite order.

## Implementation notes

The termwise comparison of the two discs adapts the proof of Mathlib's
`AnalyticOnNhd.sum_divisor_le` by Stefan Kebekus. The centre, whose term in Jensen's sum vanishes,
is kept separately with its order `m` and trailing coefficient instead of being excluded by
`f c ≠ 0`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., GTM 74, §11.
* E. C. Titchmarsh, *The Theory of Functions*, 2nd ed., §3.61.
-/

public section

open Metric MeromorphicOn Real

variable {c : ℂ} {r R : ℝ} {f : ℂ → ℂ}

/-- Termwise comparison behind Jensen's bound: a zero `u ≠ c` of `f` in `closedBall c r`
contributes at least `log (R / r)` to the sum in Jensen's formula on `closedBall c R`, other
points of `closedBall c R` contribute nonnegatively, and the centre, whose term in that sum
vanishes, is accounted for separately. -/
private lemma divisor_mul_log_le (hr : 0 < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (u : ℂ) :
    (divisor f (closedBall c r) u : ℝ) * log (R / r) ≤
      divisor f (closedBall c R) u * log (R * ‖c - u‖⁻¹) +
        if u = c then analyticOrderNatAt f c * log (R / r) else 0 := by
  have hR : 0 < R := hr.trans hrR
  have hrRball : closedBall c r ⊆ closedBall c R := closedBall_subset_closedBall hrR.le
  have hfr : AnalyticOnNhd ℂ f (closedBall c r) := hf.mono hrRball
  by_cases huc : u = c
  · subst huc
    simp [hfr.meromorphicOn.divisor_eq_analyticOrderNatAt (hf u (mem_closedBall_self hR.le))
      (mem_closedBall_self hr.le)]
  simp only [huc, ↓reduceIte, add_zero]
  by_cases huR : u ∈ closedBall c R
  · have hnonneg : (0 : ℝ) ≤ divisor f (closedBall c R) u := mod_cast hf.divisor_nonneg u
    have hdist : 0 < ‖c - u‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm huc))
    by_cases hur : u ∈ closedBall c r
    · rw [hfr.meromorphicOn.divisor_apply hur, ← hf.meromorphicOn.divisor_apply huR]
      refine mul_le_mul_of_nonneg_left (log_le_log (div_pos hR hr) ?_) hnonneg
      rw [← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left hR.le hdist (by simpa [dist_eq_norm'] using hur)
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hur, Int.cast_zero, zero_mul]
      refine mul_nonneg hnonneg (log_nonneg ?_)
      rw [← div_eq_mul_inv, one_le_div hdist]
      simpa [dist_eq_norm'] using huR
  · have hur : u ∉ closedBall c r := fun h ↦ huR (hrRball h)
    simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hur,
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ huR]

/-- The sum of `divisor_mul_log_le` over all points: the number of zeros in `closedBall c r`,
times `log (R / r)`, is at most the zero sum of Jensen's formula on `closedBall c R` plus
`m log (R / r)`, where `m` is the order at the centre. -/
private lemma sum_divisor_mul_log_le (hr : 0 < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) :
    ((∑ᶠ u, divisor f (closedBall c r) u : ℤ) : ℝ) * log (R / r) ≤
      ∑ᶠ u, divisor f (closedBall c R) u * log (R * ‖c - u‖⁻¹) +
        analyticOrderNatAt f c * log (R / r) := by
  set L := (analyticOrderNatAt f c : ℝ) * log (R / r)
  have hDr := (divisor f (closedBall c r)).finiteSupport (isCompact_closedBall c r)
  have hDR := (divisor f (closedBall c R)).finiteSupport (isCompact_closedBall c R)
  have hmul {D : ℂ → ℤ} (g : ℂ → ℝ) : (fun u ↦ (D u : ℝ) * g u).support ⊆ D.support :=
    (Function.support_mul_subset_left _ _).trans (Function.support_comp_subset Int.cast_zero _)
  have hite : (fun u : ℂ ↦ if u = c then L else 0).support ⊆ {c} := fun u hu ↦
    by_contra fun h ↦ hu (by simp [Set.mem_singleton_iff.not.1 h])
  have hsingle : ∑ᶠ u : ℂ, (if u = c then L else 0) = L := by
    rw [finsum_eq_single _ c fun u hu ↦ by simp [hu]]
    simp
  have hcast : ((∑ᶠ u, divisor f (closedBall c r) u : ℤ) : ℝ) =
      ∑ᶠ u, (divisor f (closedBall c r) u : ℝ) := map_finsum (Int.castRingHom ℝ) hDr
  rw [hcast, finsum_mul, ← hsingle, ← finsum_add_distrib (hDR.subset (hmul _))
    ((Set.finite_singleton c).subset hite)]
  refine finsum_le_finsum (hDr.subset (hmul _)) ((hDR.union (Set.finite_singleton c)).subset
    ((Function.support_add _ _).trans (Set.union_subset_union (hmul _) hite)))
    fun u ↦ divisor_mul_log_le hr hrR hf u

/-- **Jensen's bound at a zero of the centre.** Let `f` be analytic on `closedBall c R`, bounded
by `M ≥ 1` on `sphere c R`, and of finite order `m` at `c` with trailing coefficient `a`. Then for
`0 < r < R` the number of zeros of `f` in `closedBall c r`, counted with multiplicity, is at most
`m + (log (M / ‖a‖) - m log R) / log (R / r)`.

This follows from Jensen's formula `MeromorphicOn.circleAverage_log_norm`, in which the centre
contributes `m log R + log ‖a‖` and every other zero of the smaller disc at least
`log (R / r)`. -/
theorem AnalyticOnNhd.sum_divisor_le_analyticOrderNatAt_add {M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hfc : analyticOrderAt f c ≠ ⊤) (hbound : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) :
    ((∑ᶠ u, divisor f (closedBall c r) u : ℤ) : ℝ) ≤
      analyticOrderNatAt f c + (log (M / ‖meromorphicTrailingCoeffAt f c‖) -
        analyticOrderNatAt f c * log R) / log (R / r) := by
  have hR : 0 < R := hr.trans hrR
  have hcR : c ∈ closedBall c R := mem_closedBall_self hR.le
  have hsphere : sphere c |R| ⊆ closedBall c R := by
    rw [abs_of_pos hR]
    exact sphere_subset_closedBall
  have jensen := (abs_of_pos hR ▸ hf.meromorphicOn).circleAverage_log_norm hR.ne'
  rw [abs_of_pos hR, hf.meromorphicOn.divisor_eq_analyticOrderNatAt (hf c hcR) hcR,
    Int.cast_natCast] at jensen
  have havg : circleAverage (log ‖f ·‖) c R ≤ log M := by
    refine circleAverage_mono_on_of_le_circle
      (hf.mono hsphere).meromorphicOn.circleIntegrable_log_norm fun z hz ↦ ?_
    rcases eq_or_ne (f z) 0 with h | h
    · simpa [h] using log_nonneg hM
    · exact log_le_log (norm_pos_iff.2 h) (hbound z (abs_of_pos hR ▸ hz))
  have ha : 0 < ‖meromorphicTrailingCoeffAt f c‖ :=
    norm_pos_iff.2 <| (hf c hcR).meromorphicAt.meromorphicTrailingCoeffAt_ne_zero
      (by simpa [(hf c hcR).meromorphicOrderAt_eq] using hfc)
  have hsum := sum_divisor_mul_log_le hr hrR hf
  rw [log_div (by linarith) ha.ne', ← sub_le_iff_le_add', le_div_iff₀ (log_pos
    ((one_lt_div hr).2 hrR)), sub_mul]
  linarith

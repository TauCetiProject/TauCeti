/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform

/-!
# Holomorphy of the partial-sum integral of a Dirichlet series

Mathlib's `LSeries_eq_mul_integral` writes a Dirichlet series whose coefficient partial sums
`A(t) = ∑_{k ≤ t} f k` are `O(t ^ r)` as the integral `s * ∫_1^∞ A(t) t^{-(s+1)} dt` wherever the
series converges.  The integral itself makes sense on the larger half-plane `Re s > r`, and this
file proves that it is holomorphic there: it is the analytic continuation of the series supplied
by cancellation in its partial sums.

The integral is the Mellin transform of `A` cut off below `1`, evaluated at `-s`, so holomorphy is
Mathlib's `mellin_differentiableAt_of_isBigO_rpow`.  The statements take an arbitrary locally
integrable `A : ℝ → ℂ`, not only a partial-sum function, since nothing else is used.

## Main results

* `TauCeti.mellin_indicator_Ici_one_neg`: the integral as a Mellin transform.
* `TauCeti.differentiableAt_integral_Ioi_one_mul_cpow` and
  `TauCeti.differentiableOn_integral_Ioi_one_mul_cpow`: if `A = O(t ^ r)` at infinity, then
  `s ↦ ∫_1^∞ A(t) t^{-(s+1)} dt` is complex differentiable on `Re s > r`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 1 (partial summation for Dirichlet series).
-/

public section

open Asymptotics Filter MeasureTheory Set

namespace TauCeti

variable {A : ℝ → ℂ} {r : ℝ}

/-- The integral `∫_1^∞ A(t) t^{-(s+1)} dt` is the Mellin transform at `-s` of `A` cut off
below `1`. -/
theorem mellin_indicator_Ici_one_neg (A : ℝ → ℂ) (s : ℂ) :
    mellin ((Ici 1).indicator A) (-s) = ∫ t in Ioi (1 : ℝ), A t * (t : ℂ) ^ (-(s + 1)) := by
  rw [mellin, ← indicator_smul, setIntegral_indicator measurableSet_Ici,
    inter_eq_right.mpr (Ici_subset_Ioi.mpr zero_lt_one), integral_Ici_eq_integral_Ioi]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  rw [smul_eq_mul, mul_comm, neg_add', sub_eq_add_neg]

/-- **Holomorphy of the partial-sum integral.** If `A` is locally integrable on `[1, ∞)` and
`A(t) = O(t ^ r)` as `t → ∞`, then `s ↦ ∫_1^∞ A(t) t^{-(s+1)} dt` is complex differentiable at
every `s` with `r < Re s`. -/
theorem differentiableAt_integral_Ioi_one_mul_cpow (hA : LocallyIntegrableOn A (Ici 1))
    (hO : A =O[atTop] (· ^ r)) {s : ℂ} (hs : r < s.re) :
    DifferentiableAt ℂ (fun s : ℂ ↦ ∫ t in Ioi (1 : ℝ), A t * (t : ℂ) ^ (-(s + 1))) s := by
  simp_rw [← mellin_indicator_Ici_one_neg]
  have hneg : DifferentiableAt ℂ (fun s : ℂ ↦ -s) s := differentiableAt_id.neg
  refine DifferentiableAt.comp (g := mellin ((Ici 1).indicator A)) s ?_ hneg
  refine mellin_differentiableAt_of_isBigO_rpow (f := (Ici 1).indicator A) (a := -r)
    (b := -s.re - 1) ?_ ?_ ?_ ?_ ?_
  · refine (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).mpr fun K _ hK ↦ ?_
    refine (integrable_indicator_iff measurableSet_Ici).mpr ?_
    rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ici]
    exact hA.integrableOn_compact_subset inter_subset_left (hK.inter_left isClosed_Ici)
  · rw [neg_neg]
    refine (isBigO_congr ?_ EventuallyEq.rfl).mp hO
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [indicator_of_mem (mem_Ici.mpr ht)]
  · rwa [Complex.neg_re, neg_lt_neg_iff]
  · refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
    rw [indicator_of_notMem (notMem_Ici.mpr ht.2)]
  · rw [Complex.neg_re]
    linarith

/-- **Holomorphy of the partial-sum integral on a half-plane.** If `A` is locally integrable on
`[1, ∞)` and `A(t) = O(t ^ r)` as `t → ∞`, then `s ↦ ∫_1^∞ A(t) t^{-(s+1)} dt` is complex
differentiable on the open half-plane `Re s > r`. -/
theorem differentiableOn_integral_Ioi_one_mul_cpow (hA : LocallyIntegrableOn A (Ici 1))
    (hO : A =O[atTop] (· ^ r)) :
    DifferentiableOn ℂ (fun s : ℂ ↦ ∫ t in Ioi (1 : ℝ), A t * (t : ℂ) ^ (-(s + 1)))
      {s | r < s.re} :=
  fun _ hs ↦ (differentiableAt_integral_Ioi_one_mul_cpow hA hO hs).differentiableWithinAt

end TauCeti

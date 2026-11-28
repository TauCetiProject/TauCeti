/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Tail bounds from finite second moments

An almost-everywhere bound on the Euclidean norm of a finite family by an integrable
function controls the sum of the integrals of the individual norms. For an inverse-power
bound on a positive half-line, this gives an explicit bound on the sum of the tail
integrals with logarithmic weight `dt / t`. This estimate passes from a pointwise second
moment of twisted theta series to a first moment of their tail integrals.

## References

* The tail averaging step of `New.sum_thetaTailIntegral_le` in
  `grh/src/Lib/Analytic/QuadraticTwist.lean` of <https://github.com/lsernau/grh-lean>
  (revision `72fead102f663d5c7a407964a13dc0cf9d977207`).
-/

public section

open Set
open scoped BigOperators Real

namespace MeasureTheory

/-- The sum of the integrals of the individual norms is bounded by the square root of the
cardinality times the integral of any integrable majorant for the pointwise Euclidean norm
of the family. Non-integrable terms contribute zero. -/
theorem Integrable.sum_integral_norm_le_of_sqrt_sum_sq_le {α ι E : Type*} [MeasurableSpace α]
    [Norm E] {μ : Measure α} {s : Finset ι} {f : ι → α → E} {g : α → ℝ} (hg : Integrable g μ)
    (hbound : ∀ᵐ x ∂μ, √(∑ i ∈ s, ‖f i x‖ ^ 2) ≤ g x) :
    ∑ i ∈ s, (∫ x, ‖f i x‖ ∂μ) ≤ √(s.card : ℝ) * ∫ x, g x ∂μ := by
  classical
  -- First discard the terms whose integrals are zero by the Bochner integral convention.
  let a := s.filter fun i ↦ Integrable (fun x ↦ ‖f i x‖) μ
  have ha : a ⊆ s := Finset.filter_subset _ _
  have hi (i : ι) (hia : i ∈ a) : Integrable (fun x ↦ ‖f i x‖) μ :=
    (Finset.mem_filter.mp hia).2
  have hsum : (∑ i ∈ a, ∫ x, ‖f i x‖ ∂μ) = ∑ i ∈ s, ∫ x, ‖f i x‖ ∂μ := by
    refine Finset.sum_subset ha fun i his hia ↦ integral_undef ?_
    exact fun h ↦ hia (Finset.mem_filter.mpr ⟨his, h⟩)
  rw [← hsum, ← integral_finsetSum a hi, ← integral_const_mul]
  refine integral_mono_ae (integrable_finsetSum a hi) (hg.const_mul _) (hbound.mono fun x hx ↦ ?_)
  refine (Finset.sum_le_sum (fun i _ ↦ le_abs_self ‖f i x‖)).trans ?_
  refine (Finset.sum_le_sum_of_subset_of_nonneg ha (fun i _ _ ↦ abs_nonneg ‖f i x‖)).trans ?_
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt s (fun _ ↦ (1 : ℝ)) (fun i ↦ |‖f i x‖|)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, sq_abs] at hCS
  exact hCS.trans (mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg _))

/-- If the sum of the squared norms of a finite family is at most `C t⁻²ᵟ` above a positive
cutoff `r`, the sum of the norm tails with weight `dt / t` is at most
`√(#s) √C r⁻ᵟ / δ`, for `δ > 0`. -/
theorem sum_setIntegral_norm_div_le_of_sum_sq_le {ι E : Type*} [Norm E]
    {s : Finset ι} {f : ι → ℝ → E} {r δ C : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hbound : ∀ᵐ t ∂volume.restrict (Ioi r), ∑ i ∈ s, ‖f i t‖ ^ 2 ≤ C * t ^ (-2 * δ)) :
    ∑ i ∈ s, (∫ t in Ioi r, ‖f i t‖ / t) ≤ √(s.card : ℝ) * √C * r ^ (-δ) / δ := by
  have hp : -δ - 1 < -1 := by linarith
  have htail := integrableOn_Ioi_rpow_of_lt hp hr
  have hpos : ∀ᵐ t ∂volume.restrict (Ioi r), 0 < t :=
    (ae_restrict_mem measurableSet_Ioi).mono fun _ ht ↦ hr.trans ht
  have hquot : ∀ᵐ t ∂volume.restrict (Ioi r),
      √(∑ i ∈ s, ‖‖f i t‖ / t‖ ^ 2) ≤ √C * t ^ (-δ - 1) := by
    filter_upwards [hpos, hbound] with t ht hb
    have he : t ^ (-2 * δ) = (t ^ (-δ)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le, Nat.cast_ofNat]
      congr 1
      ring
    simp only [Real.norm_eq_abs, sq_abs, div_pow, ← Finset.sum_div]
    rw [Real.sqrt_div' _ (sq_nonneg t), Real.sqrt_sq ht.le,
      Real.rpow_sub_one ht.ne', ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ ht.le
    exact (Real.sqrt_le_sqrt hb).trans_eq (by
      rw [he, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (Real.rpow_nonneg ht.le _)])
  have hsum := (htail.const_mul (√C)).sum_integral_norm_le_of_sqrt_sum_sq_le hquot
  have he : -δ - 1 + 1 = -δ := by ring
  simp only [integral_const_mul, integral_Ioi_rpow_of_lt hp hr, he, neg_div_neg_eq] at hsum
  have habs : ∑ i ∈ s, (∫ t in Ioi r, ‖f i t‖ / t) ≤ ∑ i ∈ s, ∫ t in Ioi r, |‖f i t‖ / t| :=
    Finset.sum_le_sum fun i _ ↦
      le_of_abs_le (abs_integral_le_integral_abs (f := fun t ↦ ‖f i t‖ / t))
  exact habs.trans (by simpa only [Real.norm_eq_abs, mul_div_assoc, mul_assoc] using hsum)

end MeasureTheory

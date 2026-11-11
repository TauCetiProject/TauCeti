/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The radial profile `log log (4 / r)` on `(0, 2)`

On `(0, 2)` the inner logarithm of `r ↦ log log (4 / r)` exceeds `log 2 > 0`
(`TauCeti.log_two_lt_log_four_div`), so the profile is differentiable there with derivative
`-(r log (4 / r))⁻¹` (`TauCeti.hasDerivAt_log_log_four_div`). Both the profile and its derivative
are square integrable against the planar polar weight `r dr`:

* `TauCeti.integrableOn_mul_log_log_four_div_sq`: `r (log log (4 / r))²` is integrable on
  `(0, 2)`, being bounded by `36` there;
* `TauCeti.integrableOn_mul_inv_mul_log_four_div_sq`: `r (r log (4 / r))⁻²` is integrable on
  `(0, 2)`, being the derivative of `r ↦ (log (4 / r))⁻¹`, which is continuous on `[0, 2]`.

These are the radial integrals behind the `W^{1,2}` examples `log log (4 / ‖z - z₀‖)` on discs of
radius at most `2` about the singularity `z₀`.

## References

* L. C. Evans, *Partial Differential Equations*, §5.6.3 (the example `log log (1 / |x|)` of an
  unbounded `W^{1,n}` function).
-/

public section

namespace TauCeti

open Filter MeasureTheory Set
open scoped Topology

/-- For `0 < r < 2` the inner logarithm `log (4 / r)` exceeds `log 2`. -/
theorem log_two_lt_log_four_div {r : ℝ} (h0 : 0 < r) (h2 : r < 2) :
    Real.log 2 < Real.log (4 / r) :=
  Real.log_lt_log two_pos (by rw [lt_div_iff₀ h0]; linarith)

/-- For `0 < r < 2` the inner logarithm `log (4 / r)` is positive. -/
theorem log_four_div_pos {r : ℝ} (h0 : 0 < r) (h2 : r < 2) : 0 < Real.log (4 / r) :=
  (Real.log_pos one_lt_two).trans (log_two_lt_log_four_div h0 h2)

/-- `r ↦ 4 / r` has derivative `-(4 / r²)` at `r ≠ 0`. -/
private theorem hasDerivAt_four_div {r : ℝ} (h0 : r ≠ 0) :
    HasDerivAt (fun y : ℝ => 4 / y) (-(4 / r ^ 2)) r := by
  have h := (hasDerivAt_inv h0).const_mul (4 : ℝ)
  simp only [div_eq_mul_inv]
  convert h using 1
  ring

/-- The derivative of the radial profile: `d/dr log log (4 / r) = -(r log (4 / r))⁻¹` for
`0 < r < 2`. -/
theorem hasDerivAt_log_log_four_div {r : ℝ} (h0 : 0 < r) (h2 : r < 2) :
    HasDerivAt (fun s : ℝ => Real.log (Real.log (4 / s))) (-(r * Real.log (4 / r))⁻¹) r := by
  have hL := log_four_div_pos h0 h2
  have h := ((hasDerivAt_four_div h0.ne').log (by positivity)).log hL.ne'
  refine h.congr_deriv ?_
  field_simp

/-- The radial integrand `r (log log (4 / r))²` is integrable on `(0, 2)`: it is bounded by
`36` there. This is the radial form of square integrability of `log log (4 / r)` on a disc of
radius `2` about the singularity. -/
theorem integrableOn_mul_log_log_four_div_sq :
    IntegrableOn (fun r : ℝ => r * Real.log (Real.log (4 / r)) ^ 2) (Ioo 0 2) := by
  refine Measure.integrableOn_of_bounded (M := 36) (by simp) ?_ ?_
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · refine ae_restrict_of_forall_mem measurableSet_Ioo fun r ⟨h0, h2⟩ => ?_
    set L := Real.log (4 / r)
    have hL : Real.log 2 < L := log_two_lt_log_four_div h0 h2
    have hL2 : 1 / 2 < L := by
      have := Real.one_sub_inv_le_log_of_pos (two_pos : (0 : ℝ) < 2)
      norm_num at this
      linarith
    have hLpos : 0 < L := by linarith
    -- `|log L| ≤ L + 1` because `L > 1 / 2`.
    have hup : Real.log L ≤ L + 1 := by linarith [Real.log_le_sub_one_of_pos hLpos]
    have hlow : -(L + 1) ≤ Real.log L := by
      have := Real.one_sub_inv_le_log_of_pos hLpos
      have : L⁻¹ < 2 := by
        rw [inv_lt_comm₀ hLpos two_pos]
        linarith
      linarith
    -- `L < 2 √(4 / r)`, so `r L² < 16`.
    have hsq : L < 2 * √(4 / r) := by
      have h4r : 0 ≤ 4 / r := by positivity
      have hs : 0 < √(4 / r) := Real.sqrt_pos.2 (by positivity)
      have : Real.log √(4 / r) < √(4 / r) := by
        linarith [Real.log_le_sub_one_of_pos hs]
      rw [Real.log_sqrt h4r] at this
      linarith
    have hrL : r * L ^ 2 ≤ 16 := by
      have h1 : L ^ 2 ≤ (2 * √(4 / r)) ^ 2 := pow_le_pow_left₀ hLpos.le hsq.le 2
      rw [mul_pow, Real.sq_sqrt (by positivity)] at h1
      calc r * L ^ 2 ≤ r * (2 ^ 2 * (4 / r)) := by gcongr
        _ = 16 := by field_simp; norm_num
    have hprof : Real.log L ^ 2 ≤ (L + 1) ^ 2 := sq_le_sq' hlow hup
    rw [Real.norm_of_nonneg (by positivity)]
    calc r * Real.log L ^ 2 ≤ r * (L + 1) ^ 2 := by gcongr
      _ ≤ 2 * (r * L ^ 2) + 2 * r := by nlinarith [sq_nonneg (L - 1)]
      _ ≤ 36 := by linarith

/-- The radial integrand `r (r log (4 / r))⁻²` is integrable on `(0, 2)`: it is the derivative of
`r ↦ (log (4 / r))⁻¹`, which is continuous on `[0, 2]` and vanishes at `0`. This is the radial
form of square integrability of the gradient of `log log (4 / r)`. -/
theorem integrableOn_mul_inv_mul_log_four_div_sq :
    IntegrableOn (fun r : ℝ => r * ((r * Real.log (4 / r))⁻¹) ^ 2) (Ioo 0 2) := by
  set G : ℝ → ℝ := fun r => (Real.log (4 / r))⁻¹
  have hcont : ContinuousOn G (Icc 0 2) := by
    intro r hr
    rcases eq_or_lt_of_le hr.1 with rfl | h0
    · refine (continuousWithinAt_Ioi_iff_Ici.1 ?_).mono Icc_subset_Ici_self
      have h4 : Tendsto (fun y : ℝ => 4 / y) (𝓝[>] 0) atTop := by
        simpa only [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop four_pos
      have hG0 : G 0 = 0 := by simp [G]
      rw [ContinuousWithinAt, hG0]
      exact tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp h4)
    · have hL : 0 < Real.log (4 / r) := Real.log_pos (by rw [lt_div_iff₀ h0]; linarith [hr.2])
      have hdiv : (4 : ℝ) / r ≠ 0 := by positivity
      exact (((continuousAt_const (y := (4 : ℝ))).div continuousAt_id h0.ne').log
        hdiv).inv₀ hL.ne' |>.continuousWithinAt
  have hderiv : ∀ r ∈ Ioo (0 : ℝ) 2,
      HasDerivAt G (r * ((r * Real.log (4 / r))⁻¹) ^ 2) r := by
    rintro r ⟨h0, h2⟩
    have hL := log_four_div_pos h0 h2
    have h := ((hasDerivAt_four_div h0.ne').log (by positivity)).inv hL.ne'
    convert h using 1
    field_simp
  have hnonneg : ∀ r ∈ Ioo (0 : ℝ) 2, 0 ≤ r * ((r * Real.log (4 / r))⁻¹) ^ 2 :=
    fun r hr => mul_nonneg hr.1.le (sq_nonneg _)
  exact (intervalIntegral.integrableOn_deriv_of_nonneg hcont hderiv hnonneg).mono_set
    Ioo_subset_Ioc_self

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Linearity of Lebesgue integrals of `ENNReal.ofReal` finite sums

For almost everywhere measurable, almost everywhere nonnegative real functions `f i`, the map
`ENNReal.ofReal` commutes almost everywhere with finite sums and nonnegative scalar multiples, so
the Lebesgue integral `∫⁻ x, ENNReal.ofReal (∑ i ∈ s, c i * f i x) ∂μ` expands linearly. When the
summands have the form `(g i x).toReal` for almost everywhere finite `ℝ≥0∞`-valued functions
`g i`, this recovers `∑ i ∈ s, ENNReal.ofReal (c i) * ∫⁻ x, g i x ∂μ`.

## Main statements

* `TauCeti.lintegral_ofReal_finsetSum`: `∫⁻ x, ENNReal.ofReal (∑ i ∈ s, f i x) ∂μ` equals
  `∑ i ∈ s, ∫⁻ x, ENNReal.ofReal (f i x) ∂μ` for almost everywhere measurable, almost everywhere
  nonnegative `f i`.
* `TauCeti.lintegral_ofReal_finsetSum_mul`: linear expansion of
  `∫⁻ x, ENNReal.ofReal (∑ i ∈ s, c i * f i x) ∂μ` for nonnegative weights `c i`.
* `TauCeti.lintegral_ofReal_finsetSum_mul_toReal`: linear expansion of
  `∫⁻ x, ENNReal.ofReal (∑ i ∈ s, c i * (f i x).toReal) ∂μ` for almost everywhere finite
  `f i : α → ℝ≥0∞`.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {s : Finset ι}

/-- The Lebesgue integral of `ENNReal.ofReal` of a finite sum of almost everywhere measurable,
almost everywhere nonnegative real functions is the sum of their `ENNReal.ofReal` Lebesgue
integrals. -/
theorem lintegral_ofReal_finsetSum {f : ι → α → ℝ} (hf_meas : ∀ i ∈ s, AEMeasurable (f i) μ)
    (hf_nonneg : ∀ i ∈ s, 0 ≤ᵐ[μ] f i) :
    ∫⁻ x, ENNReal.ofReal (∑ i ∈ s, f i x) ∂μ = ∑ i ∈ s, ∫⁻ x, ENNReal.ofReal (f i x) ∂μ := by
  have hcongr : (fun x ↦ ENNReal.ofReal (∑ i ∈ s, f i x)) =ᵐ[μ]
      fun x ↦ ∑ i ∈ s, ENNReal.ofReal (f i x) := by
    filter_upwards [(ae_ball_iff s.countable_toSet).2 hf_nonneg] with x hx
    exact ENNReal.ofReal_sum_of_nonneg hx
  rw [lintegral_congr_ae hcongr,
    lintegral_finsetSum' s fun i hi ↦ (hf_meas i hi).ennreal_ofReal]

/-- The Lebesgue integral of `ENNReal.ofReal` of a finite nonnegative linear combination of almost
everywhere measurable, almost everywhere nonnegative real functions expands linearly. -/
theorem lintegral_ofReal_finsetSum_mul {c : ι → ℝ} {f : ι → α → ℝ} (hc : ∀ i ∈ s, 0 ≤ c i)
    (hf_meas : ∀ i ∈ s, AEMeasurable (f i) μ) (hf_nonneg : ∀ i ∈ s, 0 ≤ᵐ[μ] f i) :
    ∫⁻ x, ENNReal.ofReal (∑ i ∈ s, c i * f i x) ∂μ =
      ∑ i ∈ s, ENNReal.ofReal (c i) * ∫⁻ x, ENNReal.ofReal (f i x) ∂μ := by
  rw [lintegral_ofReal_finsetSum (fun i hi ↦ (hf_meas i hi).const_mul (c i))
    (fun i hi ↦ (hf_nonneg i hi).mono fun _ hx ↦ mul_nonneg (hc i hi) hx)]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  simp_rw [ENNReal.ofReal_mul (hc i hi)]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The Lebesgue integral of `ENNReal.ofReal (∑ i ∈ s, c i * (f i x).toReal)` for nonnegative
weights `c i` and almost everywhere measurable, almost everywhere finite `ℝ≥0∞`-valued functions
`f i` equals `∑ i ∈ s, ENNReal.ofReal (c i) * ∫⁻ x, f i x ∂μ`. -/
theorem lintegral_ofReal_finsetSum_mul_toReal {c : ι → ℝ} {f : ι → α → ℝ≥0∞}
    (hc : ∀ i ∈ s, 0 ≤ c i) (hf_meas : ∀ i ∈ s, AEMeasurable (f i) μ)
    (hf_fin : ∀ i ∈ s, ∀ᵐ x ∂μ, f i x ≠ ∞) :
    ∫⁻ x, ENNReal.ofReal (∑ i ∈ s, c i * (f i x).toReal) ∂μ =
      ∑ i ∈ s, ENNReal.ofReal (c i) * ∫⁻ x, f i x ∂μ := by
  rw [lintegral_ofReal_finsetSum_mul hc (fun i hi ↦ (hf_meas i hi).ennreal_toReal)
    (fun _ _ ↦ .of_forall fun _ ↦ ENNReal.toReal_nonneg)]
  refine Finset.sum_congr rfl fun i hi ↦ congrArg (ENNReal.ofReal (c i) * ·) ?_
  exact lintegral_congr_ae ((hf_fin i hi).mono fun _ hx ↦ ENNReal.ofReal_toReal hx)

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrating finite products of `ℝ≥0∞`-valued functions

Two facts about a finite product `∏ i, f i ω` of `ℝ≥0∞`-valued functions, relating its real form
to its `ℝ≥0∞` form.

## Main results

* `integrable_prod_toReal` — a finite product of measurable functions, each a.e. bounded by a
  finite constant, is integrable in its real form against a finite measure.
* `ofReal_integral_prod_toReal_eq_lintegral_prod` — the real integral of the product of the real
  forms is the Lebesgue integral of the product, provided the product is a.e. finite.

Both are stated for an arbitrary family `f : ι → Ω → ℝ≥0∞` indexed over a `Finset`, with
almost-everywhere hypotheses, since that is all integration sees. The motivating instance is a
product of measure evaluations `f i ω = κ ω (B i)` for a measurable family of probability
measures `κ`, where the bound `≤ 1` is `prob_le_one` and finiteness is `measure_ne_top`; nothing
in the proofs uses that the factors come from measures, so neither statement mentions one.
-/

public section

noncomputable section

open MeasureTheory Finset

open scoped ENNReal

namespace TauCeti

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **A finite product of bounded functions is integrable** against a finite measure: if every
factor is a.e. bounded by a finite constant `C`, the product of the real forms is a.e. bounded by
`C.toReal ^ #s`. -/
theorem integrable_prod_toReal {ι : Type*} {ν : Measure Ω} [IsFiniteMeasure ν] {s : Finset ι}
    {f : ι → Ω → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ∞) (hf_meas : ∀ i ∈ s, AEMeasurable (f i) ν)
    (hf_le : ∀ i ∈ s, ∀ᵐ ω ∂ν, f i ω ≤ C) :
    Integrable (fun ω => ∏ i ∈ s, (f i ω).toReal) ν := by
  refine ⟨(Finset.aemeasurable_fun_prod s fun i hi =>
    (hf_meas i hi).ennreal_toReal).aestronglyMeasurable, .of_bounded (C := C.toReal ^ #s) ?_⟩
  filter_upwards [(Filter.eventually_all_finset s).2 hf_le] with ω hω
  rw [← ENNReal.toReal_prod, Real.norm_of_nonneg ENNReal.toReal_nonneg, ← ENNReal.toReal_pow]
  exact ENNReal.toReal_mono (ENNReal.pow_ne_top hC) (Finset.prod_le_pow_card s _ C hω)

/-- **The real integral of a finite product is its `ℝ≥0∞` integral**, provided the product of the
real forms is integrable and the product itself is a.e. finite. Only the *product* need be a.e.
finite, not each factor: an infinite factor annihilated by a zero one is allowed. -/
theorem ofReal_integral_prod_toReal_eq_lintegral_prod {ι : Type*} {ν : Measure Ω} {s : Finset ι}
    {f : ι → Ω → ℝ≥0∞} (hf_ne_top : ∀ᵐ ω ∂ν, (∏ i ∈ s, f i ω) ≠ ∞)
    (h_int : Integrable (fun ω => ∏ i ∈ s, (f i ω).toReal) ν) :
    ENNReal.ofReal (∫ ω, ∏ i ∈ s, (f i ω).toReal ∂ν) = ∫⁻ ω, ∏ i ∈ s, f i ω ∂ν := by
  rw [ofReal_integral_eq_lintegral_ofReal h_int (ae_of_all _ fun _ => by positivity)]
  refine lintegral_congr_ae ?_
  filter_upwards [hf_ne_top] with ω hω
  rw [← ENNReal.toReal_prod, ENNReal.ofReal_toReal hω]

end MeasureTheory

end TauCeti

end

end

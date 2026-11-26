/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import TauCeti.MeasureTheory.Measure.Decomposition.Lebesgue

import TauCeti.Analysis.SpecialFunctions.Log.MulLog
import TauCeti.InformationTheory.KullbackLeibler.Variational

/-!
# Basic properties of Kullback–Leibler divergence

This file records general-purpose properties of log-likelihood ratios, the scalar integrand
`InformationTheory.klFun`, and Kullback–Leibler divergence.

## Main results

* `MeasureTheory.Measure.llr_eq_log_real_div_real_singleton`: on a singleton of
  nonzero finite reference mass, the log-likelihood ratio is the logarithm of the quotient of
  the two real singleton masses.
* `MeasureTheory.Measure.klDiv_map_measurableEquiv`: relative entropy between σ-finite measures
  is invariant under a measurable equivalence.
* `TauCeti.klFun_sub_klFun_sub_le_sq_div`: quadratic upper bound `(u - a) ^ 2 / a` on the Bregman
  remainder `klFun u - klFun a - (u - a) * log a` for `0 < a` and `0 ≤ u`.
* `TauCeti.integrable_klFun_of_ae_eq_or_le`: on a finite measure space, a nonnegative
  a.e.-measurable function that almost everywhere agrees with `f` or is bounded above by `M` has
  integrable `klFun` whenever `klFun ∘ f` is integrable.
* `TauCeti.klDiv_withDensity_ofReal_eq`: for a finite reference measure `ν` and a nonnegative
  a.e.-measurable `g` with `klFun ∘ g` integrable, `klDiv (ν.withDensity (ENNReal.ofReal ∘ g)) ν`
  equals `ENNReal.ofReal (∫ x, klFun (g x) ∂ν)`.
-/

public section

open MeasureTheory InformationTheory Set
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- On a singleton of nonzero finite reference mass, the log-likelihood ratio is the
logarithm of the quotient of the two real singleton masses. -/
theorem llr_eq_log_real_div_real_singleton (π R : Measure α) [π.HaveLebesgueDecomposition R]
    (x : α)
    (hR : R {x} ≠ 0) (hRtop : R {x} ≠ ∞) :
    llr π R x = Real.log (π.real {x} / R.real {x}) := by
  rw [llr, rnDeriv_eq_measure_singleton_div hR hRtop, ENNReal.toReal_div]
  rw [Measure.real, Measure.real]

/-- Relative entropy between σ-finite measures is invariant under a measurable equivalence:
the Radon–Nikodym derivative is transported along the equivalence. -/
theorem klDiv_map_measurableEquiv (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (e : α ≃ᵐ β) : klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  by_cases hac : μ ≪ ν
  swap
  · refine (klDiv_of_not_ac hac).symm ▸ klDiv_of_not_ac fun h ↦ hac ?_
    simpa [Measure.map_map e.symm.measurable e.measurable] using h.map e.symm.measurable
  have hllr : (fun x ↦ llr (μ.map e) (ν.map e) (e x)) =ᵐ[μ] llr μ ν :=
    hac.ae_le <| by
      filter_upwards [e.measurableEmbedding.rnDeriv_map μ ν] with x hx
      simp [llr, hx]
  have hint : Integrable (llr (μ.map e) (ν.map e)) (μ.map e) ↔ Integrable (llr μ ν) μ := by
    rw [integrable_map_equiv]
    exact integrable_congr hllr
  by_cases hi : Integrable (llr μ ν) μ
  · rw [klDiv_of_ac_of_integrable (hac.map e.measurable) (hint.2 hi),
      klDiv_of_ac_of_integrable hac hi, integral_map_equiv, integral_congr_ae hllr]
    simp [measureReal_def, e.map_apply]
  · rw [klDiv_of_not_integrable hi, klDiv_of_not_integrable (mt hint.1 hi)]

end MeasureTheory.Measure

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}

/-- The Bregman remainder of `InformationTheory.klFun` at `a > 0` is bounded above by the `χ²`
integrand `(u - a) ^ 2 / a` for every `u ≥ 0`. -/
theorem klFun_sub_klFun_sub_le_sq_div {a u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) :
    klFun u - klFun a - (u - a) * Real.log a ≤ (u - a) ^ 2 / a := by
  have hid : klFun u - klFun a - (u - a) * Real.log a =
      u * Real.log u - a * Real.log a - (u - a) * (Real.log a + 1) := by
    simp only [klFun]; ring
  exact hid.trans_le (mul_log_sub_mul_log_sub_le_sq_div ha hu)

/-- On a finite measure space, if a nonnegative almost everywhere measurable function `g` agrees
almost everywhere with `f` or is bounded above by `M`, and `klFun ∘ f` is integrable, then
`klFun ∘ g` is integrable. -/
theorem integrable_klFun_of_ae_eq_or_le [IsFiniteMeasure ν] {f g : α → ℝ} {M : ℝ}
    (hg : AEMeasurable g ν) (hg0 : 0 ≤ᵐ[ν] g) (hf : Integrable (fun x ↦ klFun (f x)) ν)
    (h : ∀ᵐ x ∂ν, g x = f x ∨ g x ≤ M) :
    Integrable (fun x ↦ klFun (g x)) ν := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) M) continuous_klFun.continuousOn
  refine (hf.norm.add (integrable_const (max K 0))).mono'
    (measurable_klFun.comp_aemeasurable hg).aestronglyMeasurable ?_
  filter_upwards [hg0, h] with x hx0 hx
  rcases hx with hgf | hle
  · simp only [Pi.add_apply, hgf]
    exact le_add_of_nonneg_right (le_max_right K 0)
  · simp only [Pi.add_apply]
    exact (hK (g x) ⟨hx0, hle⟩).trans ((le_max_left K 0).trans (le_add_of_nonneg_left
      (norm_nonneg _)))

/-- For a finite reference measure `ν` and a nonnegative almost everywhere measurable density `g`
with `klFun ∘ g` integrable, the relative entropy of `ν.withDensity (ENNReal.ofReal ∘ g)` against
`ν` is `ENNReal.ofReal (∫ x, klFun (g x) ∂ν)`. -/
theorem klDiv_withDensity_ofReal_eq [IsFiniteMeasure ν] {g : α → ℝ}
    (hg : AEMeasurable g ν) (hg0 : 0 ≤ᵐ[ν] g)
    (hkl : Integrable (fun x ↦ klFun (g x)) ν) :
    klDiv (ν.withDensity fun x ↦ ENNReal.ofReal (g x)) ν =
      ENNReal.ofReal (∫ x, klFun (g x) ∂ν) := by
  have hg_int : Integrable g ν := by
    refine (hkl.add (integrable_const (Real.exp 1 - 1))).mono' hg.aestronglyMeasurable ?_
    filter_upwards [hg0] with x hx0
    rw [Real.norm_eq_abs, abs_of_nonneg hx0, Pi.add_apply]
    linarith [mul_sub_exp_sub_one_le_klFun hx0 1]
  have := isFiniteMeasure_withDensity_ofReal hg_int.2
  rw [klDiv_eq_lintegral_klFun_of_ac (withDensity_absolutelyContinuous _ _),
    ofReal_integral_eq_lintegral_ofReal hkl (hg0.mono fun _ ↦ klFun_nonneg)]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_withDensity₀ ν hg.ennreal_ofReal, hg0] with x hx hx0
  rw [hx, ENNReal.toReal_ofReal hx0]

end TauCeti

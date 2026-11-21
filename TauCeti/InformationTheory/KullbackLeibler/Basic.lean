/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import TauCeti.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# Basic properties of Kullback–Leibler divergence

This file records general-purpose properties of log-likelihood ratios and Kullback–Leibler
divergence.

## Main results

* `MeasureTheory.Measure.llr_eq_log_real_div_real_singleton`: on a singleton of
  nonzero finite reference mass, the log-likelihood ratio is the logarithm of the quotient of
  the two real singleton masses.
* `MeasureTheory.Measure.klDiv_map_measurableEquiv`: relative entropy between σ-finite measures
  is invariant under a measurable equivalence.
-/

public section

open MeasureTheory InformationTheory
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

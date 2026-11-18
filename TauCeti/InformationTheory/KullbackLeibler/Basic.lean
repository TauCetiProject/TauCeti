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
* `MeasurableEmbedding.klDiv_map`: pushing two `σ`-finite measures forward along a measurable
  embedding preserves their Kullback–Leibler divergence.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α]

/-- On a singleton of nonzero finite reference mass, the log-likelihood ratio is the
logarithm of the quotient of the two real singleton masses. -/
theorem llr_eq_log_real_div_real_singleton (π R : Measure α) [π.HaveLebesgueDecomposition R]
    (x : α)
    (hR : R {x} ≠ 0) (hRtop : R {x} ≠ ∞) :
    llr π R x = Real.log (π.real {x} / R.real {x}) := by
  rw [llr, rnDeriv_eq_measure_singleton_div hR hRtop, ENNReal.toReal_div]
  rw [Measure.real, Measure.real]

/-- Pushing two `σ`-finite measures forward along a measurable embedding preserves their
Kullback–Leibler divergence. -/
theorem _root_.MeasurableEmbedding.klDiv_map {β : Type*} [MeasurableSpace β] {f : α → β}
    (hf : MeasurableEmbedding f) (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    InformationTheory.klDiv (μ.map f) (ν.map f) = InformationTheory.klDiv μ ν := by
  by_cases hμν : μ ≪ ν
  · have hllr : (fun x ↦ llr (μ.map f) (ν.map f) (f x)) =ᵐ[μ] llr μ ν :=
      (hμν.ae_eq (hf.rnDeriv_map μ ν)).mono fun x hx ↦ by
        dsimp only at hx
        simp only [llr_def]
        rw [hx]
    have hint : Integrable (llr (μ.map f) (ν.map f)) (μ.map f) ↔
        Integrable (llr μ ν) μ :=
      hf.integrable_map_iff.trans (integrable_congr hllr)
    by_cases hi : Integrable (llr μ ν) μ
    · rw [InformationTheory.klDiv_of_ac_of_integrable (hf.absolutelyContinuous_map hμν)
        (hint.2 hi), InformationTheory.klDiv_of_ac_of_integrable hμν hi, hf.integral_map,
        integral_congr_ae hllr, Measure.real, Measure.real, Measure.map_apply hf.measurable .univ,
        Measure.map_apply hf.measurable .univ, Set.preimage_univ, ← Measure.real, ← Measure.real]
    · rw [InformationTheory.klDiv_of_not_integrable (mt hint.1 hi),
        InformationTheory.klDiv_of_not_integrable hi]
  · have hnot : ¬μ.map f ≪ ν.map f := fun h ↦ hμν fun s hs ↦ by
      have hs' : (ν.map f) (f '' s) = 0 := by rwa [hf.map_apply, hf.injective.preimage_image]
      simpa only [hf.map_apply, hf.injective.preimage_image] using h hs'
    rw [InformationTheory.klDiv_of_not_ac hnot, InformationTheory.klDiv_of_not_ac hμν]

end MeasureTheory.Measure

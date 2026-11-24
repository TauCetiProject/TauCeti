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
* `MeasureTheory.Measure.llr_withDensity_ofReal_ae_eq`: the log-likelihood ratio of two measures
  with real densities `p`, `q` against a common reference measure is `log p - log q`.
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

/-- The log-likelihood ratio of two measures with real densities `p` and `q` against a common
reference measure `R` is `log p - log q`, almost everywhere for the first measure, when `q` is
almost everywhere positive. No σ-finiteness of `R` is needed, only of the second measure (for
instance when `q` is integrable). Adapted from `llr_ae_eq_log_sub_log` in the lean-CKSD project
(<https://github.com/bjbraams/lean-CKSD>, `CKSD/Bayes/Evidence/Bounds.lean`), which assumes a
σ-finite reference measure. -/
theorem llr_withDensity_ofReal_ae_eq {R : Measure α} {p q : α → ℝ}
    [SigmaFinite (R.withDensity fun x ↦ ENNReal.ofReal (q x))] (hp : AEMeasurable p R)
    (hq : AEMeasurable q R) (hq0 : ∀ᵐ x ∂R, 0 < q x) :
    llr (R.withDensity fun x ↦ ENNReal.ofReal (p x))
        (R.withDensity fun x ↦ ENNReal.ofReal (q x)) =ᵐ[R.withDensity fun x ↦ ENNReal.ofReal (p x)]
      fun x ↦ Real.log (p x) - Real.log (q x) := by
  set Q := R.withDensity fun x ↦ ENNReal.ofReal (q x)
  have hr : AEMeasurable (fun x ↦ ENNReal.ofReal (p x / q x)) R := (hp.div hq).ennreal_ofReal
  have hP : (R.withDensity fun x ↦ ENNReal.ofReal (p x)) =
      Q.withDensity fun x ↦ ENNReal.ofReal (p x / q x) := by
    rw [← withDensity_mul₀ hq.ennreal_ofReal hr]
    refine withDensity_congr_ae ?_
    filter_upwards [hq0] with x hx
    rw [Pi.mul_apply, ← ENNReal.ofReal_mul hx.le, mul_div_cancel₀ _ hx.ne']
  have hd := rnDeriv_withDensity₀ Q (hr.mono_ac (withDensity_absolutelyContinuous _ _))
  rw [hP]
  filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le hd,
    rnDeriv_pos (withDensity_absolutelyContinuous _ _),
    (withDensity_absolutelyContinuous _ _).ae_le ((withDensity_absolutelyContinuous _ _).ae_le hq0)]
    with x hx hx0 hqx
  rw [hx, ENNReal.ofReal_pos] at hx0
  rw [llr, hx, ENNReal.toReal_ofReal hx0.le,
    Real.log_div ((div_pos_iff_of_pos_right hqx).1 hx0).ne' hqx.ne']

end MeasureTheory.Measure

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Scaling and Haar-measure independence of weak derivatives

Scaling the reference measure `μ` by a finite constant `c : ℝ≥0∞` preserves weak directional and
Fréchet derivatives (`TauCeti.HasWeakLineDerivOn.smul_measure`,
`TauCeti.HasWeakFDerivOn.smul_measure`), since both local integrability and the integration-by-parts
identity scale by `c`. When `c ≠ 0` and `c ≠ ∞`, applying the scaling lemma to `c⁻¹` gives the
equivalence (`TauCeti.hasWeakLineDerivOn_smul_measure_iff`,
`TauCeti.hasWeakFDerivOn_smul_measure_iff`).

On a locally compact, second-countable real normed space with its Borel σ-algebra (in particular,
any finite-dimensional real normed space), any two additive Haar measures are positive finite scalar
multiples of one another (`MeasureTheory.Measure.isAddLeftInvariant_eq_smul`). Consequently, the
predicates `TauCeti.HasWeakLineDerivOn` and `TauCeti.HasWeakFDerivOn` are independent of the choice
of additive Haar measure (`TauCeti.hasWeakLineDerivOn_iff_of_isAddHaarMeasure`,
`TauCeti.hasWeakFDerivOn_iff_of_isAddHaarMeasure`).

## Main declarations

* `TauCeti.HasWeakLineDerivOn.smul_measure`, `TauCeti.hasWeakLineDerivOn_smul_measure_iff`:
  scaling the measure for weak directional derivatives.
* `TauCeti.HasWeakFDerivOn.smul_measure`, `TauCeti.hasWeakFDerivOn_smul_measure_iff`:
  scaling the measure for weak Fréchet derivatives.
* `TauCeti.hasWeakLineDerivOn_iff_of_isAddHaarMeasure`,
  `TauCeti.hasWeakFDerivOn_iff_of_isAddHaarMeasure`: independence of the choice of additive Haar
  measure.
-/

public section

open MeasureTheory TopologicalSpace
open scoped ENNReal

namespace TauCeti

section SmulMeasure

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} {Ω : Opens E} {u u' : E → F} {U : E → E →L[ℝ] F} {v : E}

/-- Multiplying the reference measure by a finite constant preserves weak directional
derivatives. -/
theorem HasWeakLineDerivOn.smul_measure (h : HasWeakLineDerivOn μ Ω u u' v) {c : ℝ≥0∞}
    (hc : c ≠ ∞) : HasWeakLineDerivOn (c • μ) Ω u u' v := by
  obtain ⟨hcs, hu, hu', hint⟩ := hasWeakLineDerivOn_iff_testFunction.1 h
  refine hasWeakLineDerivOn_iff_testFunction.2
    ⟨hcs, hu.smul_measure hc, hu'.smul_measure hc, fun φ => ?_⟩
  rw [integral_smul_measure, integral_smul_measure, hint φ, smul_neg]

/-- Multiplying the reference measure by a positive finite constant leaves weak directional
derivatives unchanged. -/
theorem hasWeakLineDerivOn_smul_measure_iff {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) :
    HasWeakLineDerivOn (c • μ) Ω u u' v ↔ HasWeakLineDerivOn μ Ω u u' v := by
  refine ⟨fun h => ?_, fun h => h.smul_measure hc⟩
  have := h.smul_measure (c := c⁻¹) (ENNReal.inv_ne_top.2 hc0)
  rwa [smul_smul, ENNReal.inv_mul_cancel hc0 hc, one_smul] at this

/-- Multiplying the reference measure by a finite constant preserves weak Fréchet derivatives. -/
theorem HasWeakFDerivOn.smul_measure (h : HasWeakFDerivOn μ Ω u U) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    HasWeakFDerivOn (c • μ) Ω u U :=
  hasWeakFDerivOn_iff.2 fun v => (hasWeakFDerivOn_iff.1 h v).smul_measure hc

/-- Multiplying the reference measure by a positive finite constant leaves weak Fréchet
derivatives unchanged. -/
theorem hasWeakFDerivOn_smul_measure_iff {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) :
    HasWeakFDerivOn (c • μ) Ω u U ↔ HasWeakFDerivOn μ Ω u U := by
  simp only [hasWeakFDerivOn_iff, hasWeakLineDerivOn_smul_measure_iff hc0 hc]

end SmulMeasure

section Haar

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {u u' : E → F} {U : E → E →L[ℝ] F} {v : E}

/-- On a locally compact, second-countable real normed space with its Borel σ-algebra, weak
directional derivatives are independent of the choice of additive Haar measure. -/
theorem hasWeakLineDerivOn_iff_of_isAddHaarMeasure (μ ν : Measure E) [μ.IsAddHaarMeasure]
    [ν.IsAddHaarMeasure] :
    HasWeakLineDerivOn μ Ω u u' v ↔ HasWeakLineDerivOn ν Ω u u' v := by
  have hμν : μ = (Measure.addHaarScalarFactor μ ν : ℝ≥0∞) • ν :=
    Measure.isAddLeftInvariant_eq_smul μ ν
  have hc0 : (Measure.addHaarScalarFactor μ ν : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν).ne'
  conv_lhs => rw [hμν]
  exact hasWeakLineDerivOn_smul_measure_iff hc0 ENNReal.coe_ne_top

/-- On a locally compact, second-countable real normed space with its Borel σ-algebra, weak
Fréchet derivatives are independent of the choice of additive Haar measure. -/
theorem hasWeakFDerivOn_iff_of_isAddHaarMeasure (μ ν : Measure E) [μ.IsAddHaarMeasure]
    [ν.IsAddHaarMeasure] :
    HasWeakFDerivOn μ Ω u U ↔ HasWeakFDerivOn ν Ω u U := by
  simp only [hasWeakFDerivOn_iff, hasWeakLineDerivOn_iff_of_isAddHaarMeasure μ ν]

end Haar

end TauCeti

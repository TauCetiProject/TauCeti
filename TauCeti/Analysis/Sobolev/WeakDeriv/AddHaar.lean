/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Weak derivatives and the choice of Haar measure

The defining identity `∫ ∂_v φ • u ∂μ = -∫ φ • u' ∂μ` of a weak derivative is linear in the
measure `μ`, and local integrability is unchanged when `μ` is multiplied by a finite constant.
Hence a weak derivative relative to `μ` is one relative to `c • μ` for every finite `c`
(`TauCeti.HasWeakLineDerivOn.smul_measure`, `TauCeti.HasWeakFDerivOn.smul_measure`). Two
additive Haar measures on a finite-dimensional real normed space differ by such a factor
(`MeasureTheory.Measure.isAddLeftInvariant_eq_smul`), so all of them define the same weak
derivatives (`TauCeti.HasWeakFDerivOn.of_isAddHaarMeasure`). This is what allows a Sobolev space
built on one Haar measure, typically `volume`, to be compared with the one built on another.

## Main declarations

* `TauCeti.HasWeakLineDerivOn.smul_measure` and `TauCeti.HasWeakFDerivOn.smul_measure`: weak
  derivatives are preserved by multiplying the measure by a finite constant.
* `TauCeti.HasWeakFDerivOn.of_isAddHaarMeasure`: weak Fréchet derivatives do not depend on the
  choice of additive Haar measure.
-/

public section

namespace TauCeti

open MeasureTheory TopologicalSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace E] {μ : Measure E}
  {Ω : Opens E} {u : E → F}

/-- A weak derivative stays one when the measure is multiplied by a finite constant: both sides of
the defining identity are multiplied by the same factor. -/
theorem HasWeakLineDerivOn.smul_measure {u' : E → F} {v : E} (h : HasWeakLineDerivOn μ Ω u u' v)
    {c : ENNReal} (hc : c ≠ ⊤) : HasWeakLineDerivOn (c • μ) Ω u u' v := by
  refine (hasWeakLineDerivOn_iff_testFunction).2 ⟨h.completeSpace,
    h.locallyIntegrableOn.smul_measure hc, h.locallyIntegrableOn_deriv.smul_measure hc,
    fun φ => ?_⟩
  rw [integral_smul_measure, integral_smul_measure,
    h.integral_lineDeriv_smul_eq_neg_integral_smul φ, smul_neg]

/-- A weak Fréchet derivative stays one when the measure is multiplied by a finite constant. -/
theorem HasWeakFDerivOn.smul_measure {U : E → E →L[ℝ] F} (h : HasWeakFDerivOn μ Ω u U)
    {c : ENNReal} (hc : c ≠ ⊤) : HasWeakFDerivOn (c • μ) Ω u U :=
  hasWeakFDerivOn_iff.2 fun v => (hasWeakFDerivOn_iff.1 h v).smul_measure hc

/-- **Weak derivatives do not depend on the choice of Haar measure.** On a finite-dimensional real
normed space with its Borel σ-algebra, a weak Fréchet derivative relative to one additive Haar
measure is one relative to every other. -/
theorem HasWeakFDerivOn.of_isAddHaarMeasure [FiniteDimensional ℝ E] [BorelSpace E]
    [μ.IsAddHaarMeasure] {U : E → E →L[ℝ] F} (ν : Measure E) [ν.IsAddHaarMeasure]
    (h : HasWeakFDerivOn μ Ω u U) : HasWeakFDerivOn ν Ω u U := by
  rw [Measure.isAddLeftInvariant_eq_smul ν μ]
  exact h.smul_measure ENNReal.coe_ne_top

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.Sobolev.WeakDeriv.MeasurePreserving
import TauCeti.Analysis.Sobolev.WeakDeriv.Translation

/-!
# Haar-measure independence and linear invariance of weak derivatives

On a finite-dimensional real normed space `E`, any two additive Haar measures differ by a positive
finite scalar factor (`MeasureTheory.Measure.isAddLeftInvariant_eq_smul`). Because scaling the
ambient measure by a positive finite constant preserves local integrability and scales both sides
of the weak-derivative integration-by-parts identity by the same factor, weak differentiability is
independent of the choice of additive Haar measure
(`TauCeti.hasWeakLineDerivOn_iff_of_isAddHaarMeasure`,
`TauCeti.hasWeakFDerivOn_iff_of_isAddHaarMeasure`).

Consequently, any continuous linear equivalence `e : E ≃L[ℝ] E₁` between finite-dimensional
real normed spaces carries an additive Haar measure on `E` to an additive Haar measure on `E₁`
(`ContinuousLinearEquiv.isAddHaarMeasure_map`), and hence yields the weak chain rule without any
measure-preserving hypothesis
(`TauCeti.HasWeakFDerivOn.comp_continuousLinearEquiv_of_isAddHaarMeasure`,
`ContinuousLinearEquiv.hasWeakFDerivOn_comp_iff_of_isAddHaarMeasure`). Combining this with
translation invariance gives the weak chain rule for general invertible affine maps `x ↦ e x + b`
between different spaces
(`TauCeti.HasWeakFDerivOn.comp_continuousLinearEquiv_add`).

## Main declarations

* `TauCeti.HasWeakLineDerivOn.smul_measure`, `TauCeti.hasWeakLineDerivOn_smul_measure_iff`:
  scaling the ambient measure by a finite (nonzero) scalar.
* `TauCeti.HasWeakFDerivOn.smul_measure`, `TauCeti.hasWeakFDerivOn_smul_measure_iff`: the same for
  weak Fréchet derivatives.
* `TauCeti.hasWeakLineDerivOn_iff_of_isAddHaarMeasure`,
  `TauCeti.hasWeakFDerivOn_iff_of_isAddHaarMeasure`: independence of weak derivatives from the
  choice of additive Haar measure.
* `TauCeti.HasWeakFDerivOn.comp_continuousLinearEquiv_of_isAddHaarMeasure`,
  `ContinuousLinearEquiv.hasWeakFDerivOn_comp_iff_of_isAddHaarMeasure`: linear chain rule between
  arbitrary finite-dimensional real normed spaces with arbitrary additive Haar measures.
* `TauCeti.HasWeakFDerivOn.comp_continuousLinearEquiv_add`: affine chain rule between arbitrary
  finite-dimensional real normed spaces.

## References

* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, §4.2.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace TauCeti

section SmulMeasure

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure E} {Ω : Opens E} {u u' : E → F}
  {D : E → E →L[ℝ] F} {v : E} {c : ℝ≥0∞}

/-- Scaling the ambient measure by a finite constant preserves weak directional derivatives. -/
theorem HasWeakLineDerivOn.smul_measure (h : HasWeakLineDerivOn μ Ω u u' v) (hc : c ≠ ∞) :
    HasWeakLineDerivOn (c • μ) Ω u u' v := by
  obtain ⟨hcs, hui, hu'i, hint⟩ := hasWeakLineDerivOn_iff_testFunction.1 h
  have hsmul :
      ∀ {f : E → F}, LocallyIntegrableOn f Ω μ → LocallyIntegrableOn f Ω (c • μ) :=
    fun hf x hx => by
      obtain ⟨t, ht, hti⟩ := hf x hx
      exact ⟨t, ht, by simpa [IntegrableOn] using hti.smul_measure hc⟩
  refine hasWeakLineDerivOn_iff_testFunction.2 ⟨hcs, hsmul hui, hsmul hu'i, fun φ => ?_⟩
  rw [integral_smul_measure, integral_smul_measure, hint φ, smul_neg]

/-- Scaling the ambient measure by a positive finite constant preserves and reflects weak
directional derivatives. -/
theorem hasWeakLineDerivOn_smul_measure_iff (hc0 : c ≠ 0) (hc : c ≠ ∞) :
    HasWeakLineDerivOn (c • μ) Ω u u' v ↔ HasWeakLineDerivOn μ Ω u u' v := by
  refine ⟨fun h => ?_, fun h => h.smul_measure hc⟩
  have hinv : HasWeakLineDerivOn (c⁻¹ • (c • μ)) Ω u u' v :=
    h.smul_measure (ENNReal.inv_ne_top.2 hc0)
  rwa [smul_smul, ENNReal.inv_mul_cancel hc0 hc, one_smul] at hinv

/-- Scaling the ambient measure by a finite constant preserves weak Fréchet derivatives. -/
theorem HasWeakFDerivOn.smul_measure (h : HasWeakFDerivOn μ Ω u D) (hc : c ≠ ∞) :
    HasWeakFDerivOn (c • μ) Ω u D :=
  hasWeakFDerivOn_iff.2 fun v => (h.hasWeakLineDerivOn v).smul_measure hc

/-- Scaling the ambient measure by a positive finite constant preserves and reflects weak Fréchet
derivatives. -/
theorem hasWeakFDerivOn_smul_measure_iff (hc0 : c ≠ 0) (hc : c ≠ ∞) :
    HasWeakFDerivOn (c • μ) Ω u D ↔ HasWeakFDerivOn μ Ω u D := by
  simp only [hasWeakFDerivOn_iff, hasWeakLineDerivOn_smul_measure_iff hc0 hc]

end SmulMeasure

section HaarIndependence

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {μ ν : Measure E} [μ.IsAddHaarMeasure]
  [ν.IsAddHaarMeasure] {Ω : Opens E} {u u' : E → F} {D : E → E →L[ℝ] F} {v : E}

/-- Weak directional differentiability is independent of the choice of additive Haar measure. -/
theorem hasWeakLineDerivOn_iff_of_isAddHaarMeasure :
    HasWeakLineDerivOn μ Ω u u' v ↔ HasWeakLineDerivOn ν Ω u u' v := by
  rw [Measure.isAddLeftInvariant_eq_smul μ ν, ← Measure.coe_nnreal_smul]
  exact hasWeakLineDerivOn_smul_measure_iff
    (ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν).ne')
    ENNReal.coe_ne_top

/-- Weak Fréchet differentiability is independent of the choice of additive Haar measure. -/
theorem hasWeakFDerivOn_iff_of_isAddHaarMeasure :
    HasWeakFDerivOn μ Ω u D ↔ HasWeakFDerivOn ν Ω u D := by
  simp only [hasWeakFDerivOn_iff, hasWeakLineDerivOn_iff_of_isAddHaarMeasure (μ := μ) (ν := ν)]

end HaarIndependence

section LinearEquiv

variable {E E₁ F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [FiniteDimensional ℝ E₁] [MeasurableSpace E₁] [BorelSpace E₁]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {ν : Measure E₁} [ν.IsAddHaarMeasure]
  {U : Opens E} {V : Opens E₁} {u : E₁ → F} {D : E₁ → E₁ →L[ℝ] F}

/-- **The weak chain rule for linear isomorphisms and arbitrary Haar measures.** Any continuous
linear equivalence `e : E ≃L[ℝ] E₁` carries an additive Haar measure on `E` to an additive Haar
measure on `E₁`, so precomposition with `e` obeys the weak chain rule without assuming that `e`
preserves the given measures. -/
theorem HasWeakFDerivOn.comp_continuousLinearEquiv_of_isAddHaarMeasure
    (h : HasWeakFDerivOn ν V u D) (e : E ≃L[ℝ] E₁) (hUV : MapsTo e U V) :
    HasWeakFDerivOn μ U (u ∘ e) fun x => (D (e x)).comp (e : E →L[ℝ] E₁) := by
  have : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have h' : HasWeakFDerivOn (μ.map e) V u D :=
    (hasWeakFDerivOn_iff_of_isAddHaarMeasure (μ := ν) (ν := μ.map e)).1 h
  exact h'.comp_continuousLinearEquiv e ⟨e.continuous.measurable, rfl⟩ hUV

/-- **Equivalence of weak differentiability under a linear isomorphism.** For any continuous
linear equivalence `e : E ≃L[ℝ] E₁` with `U = e ⁻¹' V` and any additive Haar measures `μ` on `E`
and `ν` on `E₁`, `u ∘ e` has weak derivative `x ↦ D (e x) ∘L e` on `U` if and only if `u` has
weak derivative `D` on `V`. -/
theorem _root_.ContinuousLinearEquiv.hasWeakFDerivOn_comp_iff_of_isAddHaarMeasure
    (e : E ≃L[ℝ] E₁) (hUV : (U : Set E) = e ⁻¹' V) :
    HasWeakFDerivOn μ U (u ∘ e) (fun x => (D (e x)).comp (e : E →L[ℝ] E₁)) ↔
      HasWeakFDerivOn ν V u D := by
  refine ⟨fun h => ?_,
    fun h => h.comp_continuousLinearEquiv_of_isAddHaarMeasure e (hUV ▸ mapsTo_preimage e V)⟩
  have hVU : MapsTo e.symm V U := fun y hy => by simpa [hUV] using hy
  simpa [Function.comp_def, ContinuousLinearMap.comp_assoc] using
    h.comp_continuousLinearEquiv_of_isAddHaarMeasure (ν := μ) (μ := ν) e.symm hVU

/-- **The weak chain rule for affine isomorphisms between arbitrary finite-dimensional spaces.**
For any continuous linear equivalence `e : E ≃L[ℝ] E₁`, translation `b : E₁`, and additive
Haar measures `μ` on `E` and `ν` on `E₁`, if `x ↦ e x + b` maps `U` into `V`, then
`x ↦ u (e x + b)` has weak derivative `x ↦ D (e x + b) ∘L e` on `U`. -/
theorem HasWeakFDerivOn.comp_continuousLinearEquiv_add
    (h : HasWeakFDerivOn ν V u D) (e : E ≃L[ℝ] E₁) (b : E₁)
    (hUV : MapsTo (fun x => e x + b) U V) :
    HasWeakFDerivOn μ U (fun x => u (e x + b))
      fun x => (D (e x + b)).comp (e : E →L[ℝ] E₁) := by
  let W : Opens E₁ :=
    ⟨(· + b) ⁻¹' V, V.isOpen.preimage (continuous_id.add continuous_const)⟩
  have htrans : HasWeakFDerivOn ν W (fun y => u (y + b)) (fun y => D (y + b)) :=
    h.comp_add_right (mapsTo_preimage (· + b) V)
  exact htrans.comp_continuousLinearEquiv_of_isAddHaarMeasure e hUV

end LinearEquiv

end TauCeti

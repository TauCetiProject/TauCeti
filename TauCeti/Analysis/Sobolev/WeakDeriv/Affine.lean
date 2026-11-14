/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.MeasurePreserving
public import TauCeti.Analysis.Sobolev.WeakDeriv.Translation
-- Private: uniqueness of additive Haar measure and scaling of local integrability are used only
-- inside the proofs.
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Measure scaling and affine change of variables for weak derivatives

Multiplying the ambient measure by a finite constant preserves the weak-derivative identity, since
both sides of the integration-by-parts pairing scale by the same factor; when the factor is
nonzero and finite, weak differentiability is invariant. Because any two additive Haar measures on
a locally compact second-countable group are positive scalar multiples of one another, weak
differentiability on an open set does not depend on the choice of additive Haar measure.

Consequently, if `e : E ≃L[ℝ] E'` is *any* continuous linear equivalence between
finite-dimensional real normed spaces carrying additive Haar measures `μ` and `ν`, then `μ.map e`
is itself an additive Haar measure on `E'`, so `e` is measure-preserving into `(E', μ.map e)`.
Combining Haar-measure independence with `TauCeti.HasWeakFDerivOn.comp_continuousLinearEquiv` and
translation (`TauCeti.HasWeakFDerivOn.comp_add_right`) yields the weak chain rule along any
invertible affine map `x ↦ e x + b`, with no measure-preservation or inner-product hypothesis.

## Main declarations

* `TauCeti.HasWeakLineDerivOn.smul_measure`, `TauCeti.HasWeakFDerivOn.smul_measure`: scaling the
  measure by a finite constant preserves weak derivatives.
* `TauCeti.HasWeakLineDerivOn.of_isAddHaarMeasure`, `TauCeti.HasWeakFDerivOn.of_isAddHaarMeasure`:
  weak derivatives are independent of the choice of additive Haar measure.
* `TauCeti.HasWeakFDerivOn.comp_continuousLinearEquiv_of_isAddHaarMeasure`: weak chain rule along
  an arbitrary continuous linear equivalence between finite-dimensional real normed spaces.
* `TauCeti.HasWeakFDerivOn.comp_continuousLinearEquiv_add_of_isAddHaarMeasure`,
  `TauCeti.HasWeakFDerivOn.comp_continuousLinearEquiv_add`,
  `ContinuousLinearEquiv.hasWeakFDerivOn_comp_add_of_isAddHaarMeasure_iff`: weak chain rule and
  characterization along an invertible affine map `x ↦ e x + b`.
-/

public section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

section MeasureScaling

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure E} {Ω : Opens E}
  {u u' : E → F} {D : E → E →L[ℝ] F} {v : E}

/-- Multiplying the measure by a finite constant preserves weak directional derivatives. -/
theorem HasWeakLineDerivOn.smul_measure (h : HasWeakLineDerivOn μ Ω u u' v) {a : ℝ≥0∞}
    (ha : a ≠ ∞) : HasWeakLineDerivOn (a • μ) Ω u u' v := by
  rw [hasWeakLineDerivOn_iff_testFunction]
  refine ⟨h.completeSpace, h.locallyIntegrableOn.smul_measure ha,
    h.locallyIntegrableOn_deriv.smul_measure ha, fun φ ↦ ?_⟩
  rw [integral_smul_measure, integral_smul_measure,
    h.integral_lineDeriv_smul_eq_neg_integral_smul φ, smul_neg]

/-- Multiplying the measure by a finite constant preserves weak Fréchet derivatives. -/
theorem HasWeakFDerivOn.smul_measure (h : HasWeakFDerivOn μ Ω u D) {a : ℝ≥0∞} (ha : a ≠ ∞) :
    HasWeakFDerivOn (a • μ) Ω u D := by
  rw [hasWeakFDerivOn_iff] at h ⊢
  exact fun v ↦ (h v).smul_measure ha

/-- Multiplying the measure by a nonzero finite constant preserves and reflects weak directional
derivatives. -/
theorem hasWeakLineDerivOn_smul_measure_iff {a : ℝ≥0∞} (ha₀ : a ≠ 0) (ha : a ≠ ∞) :
    HasWeakLineDerivOn (a • μ) Ω u u' v ↔ HasWeakLineDerivOn μ Ω u u' v := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.smul_measure ha⟩
  have h' := h.smul_measure (a := a⁻¹) (ENNReal.inv_ne_top.2 ha₀)
  rwa [smul_smul, ENNReal.inv_mul_cancel ha₀ ha, one_smul] at h'

/-- Multiplying the measure by a nonzero finite constant preserves and reflects weak Fréchet
derivatives. -/
theorem hasWeakFDerivOn_smul_measure_iff {a : ℝ≥0∞} (ha₀ : a ≠ 0) (ha : a ≠ ∞) :
    HasWeakFDerivOn (a • μ) Ω u D ↔ HasWeakFDerivOn μ Ω u D := by
  simp only [hasWeakFDerivOn_iff, hasWeakLineDerivOn_smul_measure_iff ha₀ ha]

/-- Weak directional differentiability on an open set does not depend on the choice of additive
Haar measure. -/
theorem HasWeakLineDerivOn.of_isAddHaarMeasure [LocallyCompactSpace E] [SecondCountableTopology E]
    [BorelSpace E] [μ.IsAddHaarMeasure] (ν : Measure E) [ν.IsAddHaarMeasure]
    (h : HasWeakLineDerivOn μ Ω u u' v) : HasWeakLineDerivOn ν Ω u u' v := by
  rw [Measure.isAddLeftInvariant_eq_smul ν μ]
  exact h.smul_measure ENNReal.coe_ne_top

/-- Weak Fréchet differentiability on an open set does not depend on the choice of additive Haar
measure. -/
theorem HasWeakFDerivOn.of_isAddHaarMeasure [LocallyCompactSpace E] [SecondCountableTopology E]
    [BorelSpace E] [μ.IsAddHaarMeasure] (ν : Measure E) [ν.IsAddHaarMeasure]
    (h : HasWeakFDerivOn μ Ω u D) : HasWeakFDerivOn ν Ω u D := by
  rw [Measure.isAddLeftInvariant_eq_smul ν μ]
  exact h.smul_measure ENNReal.coe_ne_top

/-- Two additive Haar measures on the same space yield the same weak Fréchet derivatives. -/
theorem hasWeakFDerivOn_iff_of_isAddHaarMeasure [LocallyCompactSpace E]
    [SecondCountableTopology E] [BorelSpace E] (μ ν : Measure E) [μ.IsAddHaarMeasure]
    [ν.IsAddHaarMeasure] :
    HasWeakFDerivOn μ Ω u D ↔ HasWeakFDerivOn ν Ω u D :=
  ⟨fun h ↦ h.of_isAddHaarMeasure ν, fun h ↦ h.of_isAddHaarMeasure μ⟩

end MeasureScaling

section Affine

variable {E E' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [MeasurableSpace E']
  [BorelSpace E'] {ν : Measure E'} [ν.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Opens E} {V : Opens E'} {u : E' → F} {D : E' → E' →L[ℝ] F}

/-- **Weak chain rule along an arbitrary continuous linear equivalence.** Unlike
`TauCeti.HasWeakFDerivOn.comp_continuousLinearEquiv`, no `MeasurePreserving` hypothesis is needed:
`μ.map e` is automatically an additive Haar measure on `E'`, hence a scalar multiple of `ν`. -/
theorem HasWeakFDerivOn.comp_continuousLinearEquiv_of_isAddHaarMeasure
    (h : HasWeakFDerivOn ν V u D) (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] E')
    (hUV : MapsTo e U V) :
    HasWeakFDerivOn μ U (u ∘ e) fun x ↦ (D (e x)).comp (e : E →L[ℝ] E') :=
  (h.of_isAddHaarMeasure (μ.map e)).comp_continuousLinearEquiv e ⟨e.continuous.measurable, rfl⟩ hUV

/-- **Weak derivatives through an arbitrary continuous linear equivalence.** When `U = e ⁻¹' V`,
`u ∘ e` has weak derivative `x ↦ D (e x) ∘L e` on `U` if and only if `u` has weak derivative `D`
on `V`. -/
theorem _root_.ContinuousLinearEquiv.hasWeakFDerivOn_comp_of_isAddHaarMeasure_iff
    (e : E ≃L[ℝ] E') (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure E') [ν.IsAddHaarMeasure]
    (hUV : (U : Set E) = e ⁻¹' V) :
    HasWeakFDerivOn μ U (u ∘ e) (fun x ↦ (D (e x)).comp (e : E →L[ℝ] E')) ↔
      HasWeakFDerivOn ν V u D :=
  (e.hasWeakFDerivOn_comp_iff ⟨e.continuous.measurable, rfl⟩ hUV).trans
    (hasWeakFDerivOn_iff_of_isAddHaarMeasure (μ.map e) ν)

/-- **Weak chain rule along an invertible affine map between normed spaces.** If `u` has weak
derivative `D` on `V` with respect to `ν`, `e : E ≃L[ℝ] E'` is a continuous linear equivalence,
`b : E'`, and `x ↦ e x + b` maps `U` into `V`, then `x ↦ u (e x + b)` has weak derivative
`x ↦ D (e x + b) ∘L e` on `U` with respect to any additive Haar measure `μ` on `E`. -/
theorem HasWeakFDerivOn.comp_continuousLinearEquiv_add_of_isAddHaarMeasure
    (h : HasWeakFDerivOn ν V u D) (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] E') (b : E')
    (hUV : MapsTo (fun x ↦ e x + b) U V) :
    HasWeakFDerivOn μ U (fun x ↦ u (e x + b)) fun x ↦ (D (e x + b)).comp (e : E →L[ℝ] E') := by
  let V' : Opens E' := ⟨(· + b) ⁻¹' V, V.isOpen.preimage (continuous_add_const b)⟩
  have htr : HasWeakFDerivOn ν V' (fun y ↦ u (y + b)) fun y ↦ D (y + b) :=
    h.comp_add_right (mapsTo_preimage (· + b) V)
  have hUV' : MapsTo e U V' := fun x hx ↦ hUV hx
  exact htr.comp_continuousLinearEquiv_of_isAddHaarMeasure μ e hUV'

/-- **Weak derivatives through an invertible affine map.** When `U = (fun x ↦ e x + b) ⁻¹' V`,
`x ↦ u (e x + b)` has weak derivative `x ↦ D (e x + b) ∘L e` on `U` if and only if `u` has weak
derivative `D` on `V`. -/
theorem _root_.ContinuousLinearEquiv.hasWeakFDerivOn_comp_add_of_isAddHaarMeasure_iff
    (e : E ≃L[ℝ] E') (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure E') [ν.IsAddHaarMeasure]
    (b : E') (hUV : (U : Set E) = (fun x ↦ e x + b) ⁻¹' V) :
    HasWeakFDerivOn μ U (fun x ↦ u (e x + b)) (fun x ↦ (D (e x + b)).comp (e : E →L[ℝ] E')) ↔
      HasWeakFDerivOn ν V u D := by
  refine ⟨fun h ↦ ?_,
    fun h ↦ h.comp_continuousLinearEquiv_add_of_isAddHaarMeasure μ e b
      (hUV ▸ mapsTo_preimage _ _)⟩
  have hinv : ∀ y, e (e.symm y + -e.symm b) + b = y := fun y ↦ by
    rw [map_add, map_neg, e.apply_symm_apply, e.apply_symm_apply, neg_add_cancel_right]
  have hVU : MapsTo (fun y ↦ e.symm y + -e.symm b) V U := fun y hy ↦ by
    rw [hUV, mem_preimage, hinv]
    exact hy
  simpa only [hinv, ContinuousLinearMap.comp_assoc, e.coe_comp_coe_symm,
    ContinuousLinearMap.comp_id] using
    h.comp_continuousLinearEquiv_add_of_isAddHaarMeasure ν e.symm (-e.symm b) hVU

/-- **Affine changes of variables on a single space.** Specialization of
`TauCeti.HasWeakFDerivOn.comp_continuousLinearEquiv_add_of_isAddHaarMeasure` to an affine map on
`(E, μ)`, inferring `μ` from `h`. -/
theorem HasWeakFDerivOn.comp_continuousLinearEquiv_add {μ : Measure E} [μ.IsAddHaarMeasure]
    {U V : Opens E} {u : E → F} {D : E → E →L[ℝ] F} (h : HasWeakFDerivOn μ V u D)
    (e : E ≃L[ℝ] E) (b : E) (hUV : MapsTo (fun x ↦ e x + b) U V) :
    HasWeakFDerivOn μ U (fun x ↦ u (e x + b)) fun x ↦ (D (e x + b)).comp (e : E →L[ℝ] E) :=
  h.comp_continuousLinearEquiv_add_of_isAddHaarMeasure μ e b hUV

end Affine

end TauCeti

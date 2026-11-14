/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.MeasurePreserving
public import TauCeti.Analysis.Sobolev.WeakDeriv.Translation

/-!
# Affine change of variables for weak derivatives

Combining the weak chain rule along a continuous linear equivalence
(`TauCeti.HasWeakFDerivOn.comp_continuousLinearEquiv`) with right translation
(`TauCeti.HasWeakFDerivOn.comp_add_right`) yields the weak chain rule along any invertible affine
map `x ↦ e x + b` between finite-dimensional real normed spaces carrying additive Haar measures,
with no measure-preservation or inner-product hypothesis.

## Main declarations

* `TauCeti.HasWeakFDerivOn.comp_continuousLinearEquiv_add`: weak chain rule along an invertible
  affine map `x ↦ e x + b`.
* `ContinuousLinearEquiv.hasWeakFDerivOn_comp_add_iff`: characterization of weak derivatives on the
  preimage of an open set under `x ↦ e x + b`.
-/

public section

namespace TauCeti

open MeasureTheory Set TopologicalSpace

section Affine

variable {E E' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [MeasurableSpace E']
  [BorelSpace E']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Opens E} {V : Opens E'} {u : E' → F} {D : E' → E' →L[ℝ] F}

/-- **Weak chain rule along an invertible affine map between normed spaces.** If `u` has weak
derivative `D` on `V` with respect to `ν`, `e : E ≃L[ℝ] E'` is a continuous linear equivalence,
`b : E'`, and `x ↦ e x + b` maps `U` into `V`, then `x ↦ u (e x + b)` has weak derivative
`x ↦ D (e x + b) ∘L e` on `U` with respect to any additive Haar measure `μ` on `E`. -/
theorem HasWeakFDerivOn.comp_continuousLinearEquiv_add {ν : Measure E'} [ν.IsAddHaarMeasure]
    (h : HasWeakFDerivOn ν V u D) (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] E') (b : E')
    (hUV : MapsTo (fun x ↦ e x + b) U V) :
    HasWeakFDerivOn μ U (fun x ↦ u (e x + b)) fun x ↦ (D (e x + b)).comp (e : E →L[ℝ] E') := by
  let V' : Opens E' := ⟨(· + b) ⁻¹' V, V.isOpen.preimage (continuous_add_const b)⟩
  have htr : HasWeakFDerivOn ν V' (fun y ↦ u (y + b)) fun y ↦ D (y + b) :=
    h.comp_add_right (mapsTo_preimage (· + b) V)
  have hUV' : MapsTo e U V' := fun x hx ↦ hUV hx
  exact htr.comp_continuousLinearEquiv μ e hUV'

/-- **Weak derivatives through an invertible affine map.** When `U = (fun x ↦ e x + b) ⁻¹' V`,
`x ↦ u (e x + b)` has weak derivative `x ↦ D (e x + b) ∘L e` on `U` with respect to an additive Haar
measure `μ` if and only if `u` has weak derivative `D` on `V` with respect to an additive Haar
measure `ν`. -/
theorem _root_.ContinuousLinearEquiv.hasWeakFDerivOn_comp_add_iff
    (e : E ≃L[ℝ] E') (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure E') [ν.IsAddHaarMeasure]
    (b : E') (hUV : (U : Set E) = (fun x ↦ e x + b) ⁻¹' V) :
    HasWeakFDerivOn μ U (fun x ↦ u (e x + b)) (fun x ↦ (D (e x + b)).comp (e : E →L[ℝ] E')) ↔
      HasWeakFDerivOn ν V u D := by
  refine ⟨fun h ↦ ?_,
    fun h ↦ h.comp_continuousLinearEquiv_add μ e b (hUV ▸ mapsTo_preimage _ _)⟩
  have hinv : ∀ y, e (e.symm y + -e.symm b) + b = y := fun y ↦ by
    rw [map_add, map_neg, e.apply_symm_apply, e.apply_symm_apply, neg_add_cancel_right]
  have hVU : MapsTo (fun y ↦ e.symm y + -e.symm b) V U := fun y hy ↦ by
    rw [hUV, mem_preimage, hinv]
    exact hy
  simpa only [hinv, ContinuousLinearMap.comp_assoc, e.coe_comp_coe_symm,
    ContinuousLinearMap.comp_id] using
    h.comp_continuousLinearEquiv_add ν e.symm (-e.symm b) hVU

end Affine

end TauCeti

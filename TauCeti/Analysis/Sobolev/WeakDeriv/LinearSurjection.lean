/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import TauCeti.MeasureTheory.Measure.Haar.Disintegration
import TauCeti.Analysis.Calculus.FDeriv.Integral
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Sobolev.WeakDeriv.MeasurePreserving
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.Topology.Algebra.Support

/-!
# Weak derivatives along surjective linear maps

Let `A : E → E'` be a surjective linear map between finite-dimensional real normed spaces with
additive Haar measures `μ` and `ν`, and let `V ⊆ E'` be open. A function `u` with weak derivative
`U` on `V` pulls back to `u ∘ A`, which is constant along the fibres of `A`, and the chain rule
holds weakly: `u ∘ A` has weak derivative `x ↦ U (A x) ∘L A` on `A⁻¹ V`
(`TauCeti.HasWeakFDerivOn.comp_surjective`). The matching transfers of local integrability are
in `TauCeti.MeasureTheory.Measure.Haar.Disintegration`.

These are the tools for lifting a function of fewer variables, such as a function on the plane,
to a function on a higher-dimensional space that is constant in the remaining variables, keeping
track of its Sobolev regularity in both directions.

## The argument

For the projection `Prod.fst : E₁ × E₂ → E₁` and a product of Haar measures this is Fubini's
theorem. Write the derivative of a test function `φ` in the direction `(w₁, w₂)` as the sum of its
partial derivatives. The partial derivative in `w₁` is handled on each slice `x₂ = const`, where
`x₁ ↦ φ (x₁, x₂)` is a test function on `V`, by the weak derivative identity of `u`; the partial
derivative in `w₂` integrates to zero over each slice `x₁ = const`
(`TauCeti.integral_apply_eq_zero_of_hasFDerivAt_off_countable`). A general surjection `A` is the
first coordinate of the linear equivalence `ContinuousLinearMap.linearCoord : E ≃ E' × ker A`, and
weak derivatives are transported along linear equivalences
(`TauCeti.HasWeakFDerivOn.comp_continuousLinearEquiv_of_isAddHaarMeasure`).

## Main results

* `TauCeti.HasWeakFDerivOn.comp_fst`: the weak chain rule for `u ∘ Prod.fst` on `V × E₂`.
* `TauCeti.HasWeakFDerivOn.comp_surjective`: the weak chain rule for `u ∘ A` on `A⁻¹ V`.
-/

public section

open MeasureTheory Set TopologicalSpace Filter
open scoped Topology

namespace TauCeti

/-! ### Weak derivatives along the first projection -/

section Prod

variable {E₁ E₂ F : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [MeasurableSpace E₁] [BorelSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [MeasurableSpace E₂] [BorelSpace E₂]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ₁ : Measure E₁} [SFinite μ₁] {μ₂ : Measure E₂} [μ₂.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E₁] [BorelSpace E₁] in
/-- The partial derivative of a compactly supported differentiable `φ` on `E₁ × E₂` in a direction
`(0, w₂)` of the second factor, times a function of the first variable, integrates to zero: it does
so on every slice `x₁ = const`. -/
private theorem integral_fderiv_inr_smul_eq_zero {φ : E₁ × E₂ → ℝ} (hφd : Differentiable ℝ φ)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) [CompleteSpace F] {u : E₁ → F} {w₂ : E₂}
    (hint : Integrable (fun x : E₁ × E₂ => fderiv ℝ φ x (0, w₂) • u x.1) (μ₁.prod μ₂)) :
    ∫ x, fderiv ℝ φ x (0, w₂) • u x.1 ∂(μ₁.prod μ₂) = 0 := by
  rw [integral_prod _ hint]
  refine integral_eq_zero_of_ae (ae_of_all _ fun x₁ => ?_)
  simp only [Pi.zero_apply]
  rw [integral_smul_const]
  have h0 := integral_apply_eq_zero_of_hasFDerivAt_off_countable (μ := μ₂) countable_empty
    (hφ.comp (Continuous.prodMk_right x₁)) (hφc.comp_prodMk_right x₁)
    (fun x₂ _ => (hφd (x₁, x₂)).hasFDerivAt_slice_snd) w₂
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.inr_apply] at h0
  simp [h0]

/-- **The weak chain rule along the first projection.** If `u` has weak derivative `U` on an open
set `V ⊆ E₁`, then `(x₁, x₂) ↦ u x₁` has weak derivative `(x₁, x₂) ↦ U x₁ ∘L fst` on `V × E₂`, for
the product of the measure on `E₁` with an additive Haar measure on `E₂`. -/
theorem HasWeakFDerivOn.comp_fst {V : Opens E₁} {u : E₁ → F} {U : E₁ → E₁ →L[ℝ] F}
    (h : HasWeakFDerivOn μ₁ V u U) :
    HasWeakFDerivOn (μ₁.prod μ₂) (Opens.comap (ContinuousMap.fst : C(E₁ × E₂, E₁)) V)
      (fun x => u x.1) fun x => (U x.1).comp (ContinuousLinearMap.fst ℝ E₁ E₂) := by
  have := h.completeSpace
  have hV : (Opens.comap (ContinuousMap.fst : C(E₁ × E₂, E₁)) V : Set (E₁ × E₂)) =
      Prod.fst ⁻¹' (V : Set E₁) := Opens.coe_comap _ _
  have hu := h.locallyIntegrableOn.comp_fst (ν := μ₂) V.isOpen
  refine hasWeakFDerivOn_iff.2 fun w => ?_
  have hUw := ((h.hasWeakLineDerivOn w.1).locallyIntegrableOn_deriv).comp_fst (ν := μ₂) V.isOpen
  rw [hasWeakLineDerivOn_iff (by rwa [hV]) (by simpa [hV] using hUw)]
  intro φ hφ hφc hφV
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφV' : tsupport φ ⊆ Prod.fst ⁻¹' (V : Set E₁) := hV ▸ hφV
  -- Split the derivative in the direction `w` into the two partial derivatives.
  have hsplit : ∀ x, lineDeriv ℝ φ x w =
      fderiv ℝ φ x (w.1, 0) + fderiv ℝ φ x (0, w.2) := fun x => by
    rw [(hφd x).lineDeriv_eq_fderiv, ← map_add, Prod.mk_add_mk, add_zero, zero_add]
  have hint : ∀ v, Integrable (fun x : E₁ × E₂ => fderiv ℝ φ x v • u x.1) (μ₁.prod μ₂) := fun v =>
    hu.integrable_smul_left_of_hasCompactSupport
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn
      (hφc.fderiv_apply (𝕜 := ℝ) _) ((tsupport_fderiv_apply_subset ℝ _).trans hφV')
  have hint₃ : Integrable (fun x : E₁ × E₂ => φ x • U x.1 w.1) (μ₁.prod μ₂) :=
    hUw.integrable_smul_left_of_hasCompactSupport hφ.continuous.continuousOn hφc hφV'
  simp_rw [hsplit, add_smul]
  rw [integral_add (hint _) (hint _)]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_fst']
  -- The second partial derivative integrates to zero on every slice `x₁ = const`.
  rw [integral_fderiv_inr_smul_eq_zero hφd hφ.continuous hφc (hint _), add_zero,
    integral_prod_symm _ (hint _), integral_prod_symm _ hint₃, ← integral_neg]
  -- The first partial derivative is the weak derivative identity of `u` on every slice.
  refine integral_congr_ae (ae_of_all _ fun x₂ => ?_)
  have hslice := ((hasWeakLineDerivOn_iff h.locallyIntegrableOn
    (h.hasWeakLineDerivOn w.1).locallyIntegrableOn_deriv).1 (h.hasWeakLineDerivOn w.1))
    (fun y => φ (y, x₂)) (hφ.comp (contDiff_prodMk_left x₂))
    (hφc.comp_prodMk_left x₂)
    fun _ hy => hφV' (tsupport_comp_subset_preimage φ (Continuous.prodMk_left x₂) hy)
  simp only
  rw [← hslice]
  refine integral_congr_ae (ae_of_all _ fun x₁ => ?_)
  simp only
  rw [(hφd (x₁, x₂)).hasFDerivAt_slice_fst.differentiableAt.lineDeriv_eq_fderiv,
    (hφd (x₁, x₂)).hasFDerivAt_slice_fst.fderiv]
  simp

end Prod

/-! ### Along a surjective linear map -/

section Surjective

variable {E E' F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E']
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  {μ : Measure E} [μ.IsAddHaarMeasure] {ν : Measure E'} [ν.IsAddHaarMeasure]
  {A : E →L[ℝ] E'}

/-- **The weak chain rule along a surjective linear map.** If `u` has weak derivative `U` on an
open set `V ⊆ E'` and `A : E → E'` is a surjective linear map, then `u ∘ A` has weak derivative
`x ↦ U (A x) ∘L A` on `A⁻¹ V`. -/
theorem HasWeakFDerivOn.comp_surjective {V : Opens E'} {u : E' → F} {U : E' → E' →L[ℝ] F}
    (h : HasWeakFDerivOn ν V u U) (hA : Function.Surjective A) :
    HasWeakFDerivOn μ (Opens.comap (A : C(E, E')) V) (u ∘ A) fun x => (U (A x)).comp A := by
  have hp := (h.comp_fst (μ₂ := (Measure.addHaar : Measure (A : E →ₗ[ℝ] E').ker))
    ).comp_continuousLinearEquiv_of_isAddHaarMeasure (μ := μ) (A.linearCoord hA)
    (U := Opens.comap (A : C(E, E')) V) fun x hx => by
      simpa using hx
  have hfst : (ContinuousLinearMap.fst ℝ E' (A : E →ₗ[ℝ] E').ker).comp
      (A.linearCoord hA : E →L[ℝ] E' × (A : E →ₗ[ℝ] E').ker) = A := by
    ext x
    simp
  convert hp using 1
  · ext x
    simp
  · ext x : 1
    rw [ContinuousLinearMap.comp_assoc, hfst]
    simp

end Surjective

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence.Basic
import Mathlib.MeasureTheory.Group.Integral
import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.Bochner.Affine

/-!
# Changes of variables for weak divergence

Weak divergence commutes with translations and with linear pullback of a vector field.
In the linear case the derivative of the transported test function cancels the inverse
linear map on the field, and both integrals acquire the same Jacobian factor.
-/

public section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped Distributions Gradient InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  {Ω V : Opens E} {u : E → E} {g : E → ℝ}

section Translation

variable [CompleteSpace E] [μ.IsAddRightInvariant]

/-- The divergence of a translated field is the translated divergence, on any open set whose
translate lies in the original domain. -/
theorem HasWeakDivergenceOn.comp_add_right (hu : HasWeakDivergenceOn μ Ω u g)
    {a : E} (hV : MapsTo (· + a) V Ω) :
    HasWeakDivergenceOn μ V (fun x ↦ u (x + a)) (fun x ↦ g (x + a)) := by
  refine hasWeakDivergenceOn_iff.mpr ⟨hu.locallyIntegrableOn.comp_add_right_of_mapsTo hV,
    hu.locallyIntegrableOn_divergence.comp_add_right_of_mapsTo hV, fun φ ↦ ?_⟩
  let ψ := translateTestFunction hV φ
  have hleft :
      ∫ x, ⟪u (x + a), ∇ (φ : E → ℝ) x⟫_ℝ ∂μ = ∫ y, ⟪u y, ∇ (ψ : E → ℝ) y⟫_ℝ ∂μ := by
    simpa only [ψ, inner_gradient_right, fderiv_translateTestFunction, add_sub_cancel_right] using
      integral_add_right_eq_self (fun y ↦ ⟪u y, ∇ (ψ : E → ℝ) y⟫_ℝ) a
  have hright : ∫ x, φ x * g (x + a) ∂μ = ∫ y, ψ y * g y ∂μ := by
    simpa only [ψ, translateTestFunction_apply, add_sub_cancel_right] using
      integral_add_right_eq_self (fun y ↦ ψ y * g y) a
  rw [hleft, hright, hu.integral_inner_gradient_eq_neg_integral_mul]

/-- Translating a solenoidal field preserves solenoidality. -/
theorem IsSolenoidalOn.comp_add_right (hu : IsSolenoidalOn μ Ω u)
    {a : E} (hV : MapsTo (· + a) V Ω) : IsSolenoidalOn μ V (fun x ↦ u (x + a)) := by
  rw [isSolenoidalOn_iff_hasWeakDivergenceOn] at hu ⊢
  simpa [Pi.zero_def] using hu.comp_add_right hV

end Translation

section Linear

variable [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure]

/-- The pullback of a field by a linear change of variables has divergence given by precomposing
the original divergence with the same change of variables. -/
theorem HasWeakDivergenceOn.comp_continuousLinearEquiv (hu : HasWeakDivergenceOn μ Ω u g)
    (e : E ≃L[ℝ] E) (hV : MapsTo e V Ω) :
    HasWeakDivergenceOn μ V (fun x ↦ e.symm (u (e x))) (fun x ↦ g (e x)) := by
  have hfield : LocallyIntegrableOn (fun x ↦ e.symm (u (e x))) V μ := by
    simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe] using
      (e.symm : E →L[ℝ] E).locallyIntegrableOn_comp
        (hu.locallyIntegrableOn.comp_continuousLinearEquiv_of_mapsTo e hV)
  have hdiv := hu.locallyIntegrableOn_divergence.comp_continuousLinearEquiv_of_mapsTo e hV
  refine hasWeakDivergenceOn_iff.mpr ⟨hfield, hdiv, fun φ ↦ ?_⟩
  let ψ := e.transportTestFunction hV φ
  let J := |LinearMap.det (e : E →ₗ[ℝ] E)|⁻¹
  have hleft :
      ∫ x, ⟪e.symm (u (e x)), ∇ (φ : E → ℝ) x⟫_ℝ ∂μ =
        J • ∫ y, ⟪u y, ∇ (ψ : E → ℝ) y⟫_ℝ ∂μ := by
    calc
      _ = ∫ x, ⟪u (e x), ∇ (ψ : E → ℝ) (e x)⟫_ℝ ∂μ := by
        congr with x
        simp [ψ, e.inner_gradient_transportTestFunction]
      _ = _ := by
        simpa [J] using
          μ.integral_comp_linearMap (fun y ↦ ⟪u y, ∇ (ψ : E → ℝ) y⟫_ℝ) (e : E →ₗ[ℝ] E)
  have hright : ∫ x, φ x * g (e x) ∂μ = J • ∫ y, ψ y * g y ∂μ := by
    simpa [J, ψ] using
      μ.integral_comp_linearMap (fun y ↦ ψ y * g y) (e : E →ₗ[ℝ] E)
  rw [hleft, hright, hu.integral_inner_gradient_eq_neg_integral_mul, smul_neg]

/-- Under precomposition by a nonzero dilation of factor `r`, the weak divergence is
precomposed by the dilation and multiplied by `r`. -/
theorem HasWeakDivergenceOn.comp_smul (hu : HasWeakDivergenceOn μ Ω u g)
    {r : ℝ} (hr : r ≠ 0) (hV : MapsTo (fun x : E ↦ r • x) V Ω) :
    HasWeakDivergenceOn μ V (fun x ↦ u (r • x)) (fun x ↦ r * g (r • x)) := by
  let e := (LinearEquiv.smulOfNeZero ℝ E r hr).toContinuousLinearEquiv
  have h := (hu.comp_continuousLinearEquiv e hV).const_smul r
  have hfield : (r • fun x ↦ e.symm (u (e x))) = fun x ↦ u (r • x) := by
    funext x
    simp [e, Pi.smul_apply, Units.smul_def, smul_inv_smul₀ hr]
  have hdiv : (r • fun x ↦ g (e x)) = fun x ↦ r * g (r • x) := by
    funext x
    simp [e, Pi.smul_apply, smul_eq_mul]
  simpa only [hfield, hdiv] using h

/-- Pulling a vector field back along a continuous linear equivalence preserves solenoidality. -/
theorem IsSolenoidalOn.comp_continuousLinearEquiv (hu : IsSolenoidalOn μ Ω u)
    (e : E ≃L[ℝ] E) (hV : MapsTo e V Ω) : IsSolenoidalOn μ V (fun x ↦ e.symm (u (e x))) := by
  rw [isSolenoidalOn_iff_hasWeakDivergenceOn] at hu ⊢
  simpa only [Pi.zero_def] using hu.comp_continuousLinearEquiv e hV

/-- Orthogonal changes of coordinates preserve solenoidality. For an orthogonal map `e`,
a field `u` in the original coordinates becomes `x ↦ e (u (e.symm x))`. -/
theorem IsSolenoidalOn.comp_linearIsometryEquiv (hu : IsSolenoidalOn μ Ω u)
    (e : E ≃ₗᵢ[ℝ] E) (hV : MapsTo e.symm V Ω) : IsSolenoidalOn μ V (fun x ↦ e (u (e.symm x))) :=
  hu.comp_continuousLinearEquiv e.symm.toContinuousLinearEquiv hV

/-- Precomposing a solenoidal field by a nonzero dilation preserves solenoidality. -/
theorem IsSolenoidalOn.comp_smul (hu : IsSolenoidalOn μ Ω u)
    {r : ℝ} (hr : r ≠ 0) (hV : MapsTo (fun x : E ↦ r • x) V Ω) :
    IsSolenoidalOn μ V (fun x ↦ u (r • x)) := by
  rw [isSolenoidalOn_iff_hasWeakDivergenceOn] at hu ⊢
  simpa only [Pi.zero_def, mul_zero] using hu.comp_smul hr hV

end Linear

end TauCeti

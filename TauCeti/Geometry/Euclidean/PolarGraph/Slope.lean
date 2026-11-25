/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import TauCeti.Analysis.Complex.Inner
public import TauCeti.MeasureTheory.Integral.PolarCoord

/-!
# Cartesian slope from radial and angular derivatives

The two columns of the polar differential are the radial unit vector and the angular
unit vector multiplied by the radius. Consequently the squared slope of a height on a
Cartesian patch is the squared radial derivative plus the squared angular derivative
divided by the squared radius. Germwise agreement suffices for a multi-valued graph.
-/

public noncomputable section

open Filter
open scoped Gradient RealInnerProductSpace Topology

namespace TauCeti.PolarGraph

/-- The polar slope identity with the radius factors cleared also holds at signed or zero
radius. The height may be defined on a single sheet through local agreement. -/
theorem sq_radius_mul_norm_gradient_sq {f : ℂ → ℝ} {h : ℝ × ℝ → ℝ} (z₀ : ℂ)
    (p : ℝ × ℝ) (hf : DifferentiableAt ℝ f (z₀ + Complex.polarCoord.symm p))
    (he : h =ᶠ[𝓝 p] fun q ↦ f (z₀ + Complex.polarCoord.symm q)) :
    p.1 ^ 2 * ‖∇ f (z₀ + Complex.polarCoord.symm p)‖ ^ 2 =
      p.1 ^ 2 * (fderiv ℝ h p (1, 0)) ^ 2 + (fderiv ℝ h p (0, 1)) ^ 2 := by
  set w := Complex.exp (p.2 * Complex.I)
  set v := ∇ f (z₀ + Complex.polarCoord.symm p)
  have hD := hf.hasFDerivAt.comp p (TauCeti.hasFDerivAt_add_polarCoord_symm p z₀)
  have hD' := hD.congr_of_eventuallyEq he
  have h₁ : fderiv ℝ h p (1, 0) = ⟪v, w⟫ := by
    rw [hD'.fderiv]
    simp [v, w, TauCeti.equivRealProd_symm_fderivPolarCoordSymm_apply_one_zero]
  have h₂ : fderiv ℝ h p (0, 1) = p.1 * ⟪v, w * Complex.I⟫ := by
    rw [hD'.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      TauCeti.equivRealProd_symm_fderivPolarCoordSymm_apply_zero_one, circleMap_zero]
    rw [mul_assoc, ← Complex.real_smul, map_smul]
    simp [v, w]
  rw [h₁, h₂, Complex.norm_sq_eq_real_inner_sq_add_real_inner_mul_I_sq v w
    (Complex.norm_exp_ofReal_mul_I p.2)]
  ring

/-- Away from the origin the Cartesian gradient norm uses the reciprocal radius on the
angular derivative. -/
theorem norm_gradient_sq_eq_polar_partials {f : ℂ → ℝ} {h : ℝ × ℝ → ℝ} (z₀ : ℂ)
    (p : ℝ × ℝ) (hr : p.1 ≠ 0) (hf : DifferentiableAt ℝ f (z₀ + Complex.polarCoord.symm p))
    (he : h =ᶠ[𝓝 p] fun q ↦ f (z₀ + Complex.polarCoord.symm q)) :
    ‖∇ f (z₀ + Complex.polarCoord.symm p)‖ ^ 2 =
      (fderiv ℝ h p (1, 0)) ^ 2 + (fderiv ℝ h p (0, 1) / p.1) ^ 2 := by
  have hD := sq_radius_mul_norm_gradient_sq z₀ p hf he
  field_simp
  linarith

end TauCeti.PolarGraph

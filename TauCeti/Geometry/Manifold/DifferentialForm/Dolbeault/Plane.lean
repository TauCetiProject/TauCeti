/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Conformal
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Basic

/-!
# Holomorphic one-forms on the plane

On the complex plane `ℂ`, regarded as a real manifold with its complex structure (multiplication
by `i`), a complex-valued one-form `η` of type `(1,0)` is complex-linear at every point, so it is
`η = c dz` for its coefficient `c(z) = η_z(1)` (`TauCeti.SmoothForm.IsOfType.apply_eq_smul`).
Its exterior derivative is `dη = dc ∧ dz`, and `∂bar η` is the type-`(1,1)` component of `dη`.
On the pair of tangent vectors `(1, i)` this component is `i ∂c/∂x - ∂c/∂y`, which vanishes
exactly when `c` satisfies the Cauchy–Riemann equation.

Hence a `(1,0)`-form on the plane is `∂bar`-closed at a point exactly when its coefficient is
complex differentiable there (`TauCeti.SmoothForm.IsOfType.delBar_apply_eq_zero_iff`), and
`∂bar η = 0` exactly when the coefficient is an entire function
(`TauCeti.SmoothForm.IsOfType.delBar_eq_zero_iff`). These are the holomorphic one-forms
`c(z) dz` of the plane, the one-form counterpart of the identification of `∂bar`-closed functions
with holomorphic functions in `TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.Holomorphic`.
Pulling a one-form on a Riemann surface back along holomorphic coordinates reduces questions about
its holomorphy to this case.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Sections 1.3 and 2.6.
-/

public section

open Set Complex
open scoped Manifold ContDiff

namespace TauCeti

open SmoothAlmostComplexStructure

namespace SmoothForm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {η : SmoothForm 𝓘(ℝ, ℂ) ℂ F 1}

/-- **A `(1,0)`-form on the plane is a multiple of `dz`.** At every point it is complex-linear,
so its value on a tangent vector `v` is `v` times its coefficient, its value on `1`. -/
theorem IsOfType.apply_eq_smul (hη : η.IsOfType (ofComplexManifold ℂ ℂ) 1 0) (z v : ℂ) :
    η.1 z ![v] = v • η.1 z ![(1 : ℂ)] := by
  have h : (η.1 z : ℂ [⋀^Fin 1]→L[ℝ] F).IsOfType (Complex.I • ContinuousLinearMap.id ℝ ℂ) 1 0 := by
    simpa only [toEndomorphism_ofComplexManifold] using hη.apply z
  have h' := h.map_smul_complex (U := ℂ) v (1 : ℂ)
  rw [smul_eq_mul, mul_one] at h'
  exact h'

/-- The exterior derivative of `c dz` is `dc ∧ dz`: on the tangent vectors `v` and `w` it is
`w • dc(v) - v • dc(w)`, where `c` is the coefficient of the `(1,0)`-form. -/
private theorem IsOfType.mextDerivₗ_apply_vecCons (hη : η.IsOfType (ofComplexManifold ℂ ℂ) 1 0)
    (z v w : ℂ) :
    (mextDerivₗ 𝓘(ℝ, ℂ) 1 η).1 z ![v, w] =
      w • fderiv ℝ (fun y ↦ η.1 y ![(1 : ℂ)]) z v -
        v • fderiv ℝ (fun y ↦ η.1 y ![(1 : ℂ)]) z w := by
  -- Read `η` as a map into the alternating forms on the model space `ℂ`.
  let Θ : ℂ → ℂ [⋀^Fin 1]→L[ℝ] F := fun y ↦ η.1 y
  have hd : ContDiff ℝ ∞ Θ := isSmoothForm_modelSpace_iff.1 η.isSmoothForm
  have hc : DifferentiableAt ℝ (fun y ↦ Θ y ![(1 : ℂ)]) z :=
    (ContinuousAlternatingMap.apply ℝ ℂ F ![(1 : ℂ)]).differentiableAt.comp z
      (hd.differentiable (by simp) z)
  have hcoeff (u : ℂ) : (fun y ↦ Θ y fun _ ↦ u) = fun y ↦ u • Θ y ![(1 : ℂ)] := by
    rw [show (fun _ : Fin 1 ↦ u) = ![u] by ext i; fin_cases i; rfl]
    exact funext fun y ↦ hη.apply_eq_smul y u
  -- The coefficient is stated through the tangent spaces of `ℂ`, which are `ℂ` itself; `change`
  -- restates it through `Θ` so that rewriting sees well-typed terms.
  change _ = w • fderiv ℝ (fun y ↦ Θ y ![(1 : ℂ)]) z v - v • fderiv ℝ (fun y ↦ Θ y ![(1 : ℂ)]) z w
  rw [TauCeti.mextDerivₗ_apply]
  refine (congrArg (fun A ↦ A ![v, w]) (mextDeriv_eq_extDeriv η.1 z)).trans
    ((extDeriv_apply_pair_of_differentiableAt
      (hd.differentiable (by simp) z : DifferentiableAt ℝ Θ z) v w).trans ?_)
  rw [hcoeff, hcoeff, fderiv_fun_const_smul hc, fderiv_fun_const_smul hc]
  rfl

/-- **Holomorphic one-forms on the plane, pointwise.** A `(1,0)`-form `c dz` on `ℂ` is
`∂bar`-closed at `z` exactly when its coefficient `c` is complex differentiable at `z`. -/
theorem IsOfType.delBar_apply_eq_zero_iff (hη : η.IsOfType (ofComplexManifold ℂ ℂ) 1 0)
    (z : ℂ) :
    ((ofComplexManifold ℂ ℂ).delBar η).1 z = 0 ↔
      DifferentiableAt ℂ (fun y ↦ η.1 y ![(1 : ℂ)]) z := by
  -- Read `η` and `dη` at `z` through the model space `ℂ`, with `J = L` multiplication by `i`.
  let Θ : ℂ → ℂ [⋀^Fin 1]→L[ℝ] F := fun y ↦ η.1 y
  let β : ℂ [⋀^Fin 2]→L[ℝ] F := (mextDerivₗ 𝓘(ℝ, ℂ) 1 η).1 z
  let L : ℂ →L[ℝ] ℂ := Complex.I • ContinuousLinearMap.id ℝ ℂ
  have hd : ContDiff ℝ ∞ Θ := isSmoothForm_modelSpace_iff.1 η.isSmoothForm
  have hc : DifferentiableAt ℝ (fun y ↦ Θ y ![(1 : ℂ)]) z :=
    (ContinuousAlternatingMap.apply ℝ ℂ F ![(1 : ℂ)]).differentiableAt.comp z
      (hd.differentiable (by simp) z)
  set D := fderiv ℝ (fun y ↦ Θ y ![(1 : ℂ)]) z
  have hβ (v w : ℂ) : β ![v, w] = w • D v - v • D w := hη.mextDerivₗ_apply_vecCons z v w
  have hL (v : ℂ) : L (L v) = -v := by simp [L, ← mul_assoc]
  -- `∂bar η` is the type-`(1,1)` component of `dη`; the structure of `ℂ` is `L` at every point.
  have hδ : ((ofComplexManifold ℂ ℂ).delBar η).1 z = L.typeProjection 1 1 β := by
    rw [hη.delBar_eq, coe_typeProjection]
    exact congrArg (fun A : ℂ →L[ℝ] ℂ ↦ A.typeProjection 1 1 β)
      (toEndomorphism_ofComplexManifold (E := ℂ) z)
  -- As in `hδ`, restate the coefficient through `Θ`.
  change _ ↔ DifferentiableAt ℂ (fun y ↦ Θ y ![(1 : ℂ)]) z
  rw [hδ, differentiableAt_complex_iff_differentiableAt_real, and_iff_right hc]
  constructor
  · -- On the pair `(1, i)`, the type-`(1,1)` component of `dη` is `i dc(1) - dc(i)`.
    intro h
    have h' : L.typeProjection 1 1 β ![(1 : ℂ), Complex.I] = 0 := by
      rw [show L.typeProjection 1 1 β = 0 from h]
      rfl
    rw [ContinuousLinearMap.typeProjection_one_one_apply hL, hβ, hβ] at h'
    simp [L] at h'
    linear_combination (norm := module) (-1 : ℂ) • h'
  · -- A complex-linear `dc` makes `dη = dc ∧ dz` vanish.
    intro h
    have hD (u : ℂ) : D u = u • D 1 := by
      simpa using real_linearMap_map_smul_complex (ℓ := D.toLinearMap) h u 1
    have hβ0 : β = 0 := by
      ext v
      have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
      rw [hv, hβ, hD (v 0), hD (v 1), smul_smul, smul_smul, mul_comm, sub_self]
      rfl
    rw [hβ0, map_zero]
    rfl

/-- **Holomorphic one-forms on the plane.** A `(1,0)`-form `c dz` on `ℂ` is `∂bar`-closed exactly
when its coefficient `c` is an entire function. -/
theorem IsOfType.delBar_eq_zero_iff (hη : η.IsOfType (ofComplexManifold ℂ ℂ) 1 0) :
    (ofComplexManifold ℂ ℂ).delBar η = 0 ↔ Differentiable ℂ (fun y ↦ η.1 y ![(1 : ℂ)]) := by
  refine ⟨fun h z ↦ (hη.delBar_apply_eq_zero_iff z).1 (by rw [h]; rfl), fun h ↦ ?_⟩
  exact Subtype.ext (funext fun z ↦ (hη.delBar_apply_eq_zero_iff z).2 (h z))

end SmoothForm

end TauCeti

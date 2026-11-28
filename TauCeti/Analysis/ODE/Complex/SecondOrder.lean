/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import TauCeti.Analysis.ODE.SecondOrder.Operator

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import TauCeti.Analysis.SpecialFunctions.Complex.Log.Deriv

/-!
# Second-order complex linear differential operators and logarithm products

Pointwise and domain-level logarithmic-product identities for the second-order complex linear
differential operator `L(w) = w'' + f w' + g w` on the translated slit plane
`z - z₀ ∈ Complex.slitPlane`:
* `TauCeti.deriv_deriv_add_mul_deriv_add_mul_mul_log_sub`: pointwise identity for
  `L(w * log(· - z₀)) - log(· - z₀) * L(w)`.
* `TauCeti.operator_mul_log`: domain-level holomorphy and forcing identity when `L(w₁) = 0`.
-/

public section

open Complex Filter
open scoped Topology

namespace TauCeti

/-- Pointwise logarithmic-product identity for the second-order linear operator
`L(w) = w'' + f w' + g w` on the logarithm branch `z - z₀ ∈ Complex.slitPlane`: if `w` is
differentiable near `z` and `deriv w` is differentiable at `z`, then
`L(w * log(· - z₀)) z - log(z - z₀) * L(w) z` equals
`((z - z₀) ^ 2)⁻¹ * (2 * (z - z₀) * deriv w z + ((z - z₀) * f z - 1) * w z)`. -/
theorem deriv_deriv_add_mul_deriv_add_mul_mul_log_sub
    {z₀ z : ℂ} (hzs : z - z₀ ∈ Complex.slitPlane) {f g w : ℂ → ℂ}
    (hw : ∀ᶠ u in 𝓝 z, DifferentiableAt ℂ w u) (hdw : DifferentiableAt ℂ (deriv w) z) :
    (deriv (deriv fun u ↦ w u * Complex.log (u - z₀)) z +
        f z * deriv (fun u ↦ w u * Complex.log (u - z₀)) z +
        g z * (w z * Complex.log (z - z₀))) -
        Complex.log (z - z₀) * (deriv (deriv w) z + f z * deriv w z + g z * w z) =
      ((z - z₀) ^ 2)⁻¹ * (2 * (z - z₀) * deriv w z + ((z - z₀) * f z - 1) * w z) := by
  set Φ : ℂ → ℂ := fun u ↦ w u * Complex.log (u - z₀)
  have hzu0 : z - z₀ ≠ 0 := Complex.slitPlane_ne_zero hzs
  have hsub : HasDerivAt (fun u : ℂ ↦ u - z₀) 1 z := (hasDerivAt_id z).sub_const z₀
  have hU_log : ∀ᶠ u in 𝓝 z, u - z₀ ∈ Complex.slitPlane :=
    (Complex.isOpen_slitPlane.preimage (continuous_id.sub continuous_const)).mem_nhds hzs
  have hderiv1 : ∀ᶠ u in 𝓝 z,
      HasDerivAt Φ (deriv w u * Complex.log (u - z₀) + (u - z₀)⁻¹ * w u) u := by
    filter_upwards [hw, hU_log] with u hu hsu
    exact hu.hasDerivAt.mul_log_sub hsu
  have hd1 : deriv Φ z = deriv w z * Complex.log (z - z₀) + (z - z₀)⁻¹ * w z :=
    hderiv1.self_of_nhds.deriv
  have hev : deriv Φ =ᶠ[𝓝 z]
      (deriv w * (fun u : ℂ ↦ Complex.log (u - z₀)) + (fun u : ℂ ↦ (u - z₀)⁻¹) * w) :=
    hderiv1.mono fun _ hu ↦ hu.deriv
  have hd2 : deriv (deriv Φ) z = deriv (deriv w) z * Complex.log (z - z₀) +
      2 * (z - z₀)⁻¹ * deriv w z - ((z - z₀) ^ 2)⁻¹ * w z := by
    rw [(((hdw.hasDerivAt.mul (hsub.clog hzs)).add
      ((hsub.inv hzu0).mul hw.self_of_nhds.hasDerivAt)).congr_of_eventuallyEq hev).deriv]
    simp only [Pi.inv_apply]; field_simp [hzu0]; ring
  change (deriv (deriv Φ) z + f z * deriv Φ z + g z * Φ z) -
      Complex.log (z - z₀) * (deriv (deriv w) z + f z * deriv w z + g z * w z) = _
  rw [hd1, hd2]
  dsimp only [Φ]
  field_simp [hzu0]
  ring

/-- Domain-level logarithmic-product forcing identity: on any open set `U` contained in the
translated slit plane `{z | z - z₀ ∈ Complex.slitPlane}`, if `w₁` is complex differentiable on `U`
and solves `w₁'' + f w₁' + g w₁ = 0` on `U`, then `Φ(z) = w₁(z) * Complex.log (z - z₀)` is complex
differentiable on `U` and satisfies
`L(Φ) z = ((z - z₀) ^ 2)⁻¹ * (2 (z - z₀) w₁'(z) + ((z - z₀) f(z) - 1) w₁(z))` on `U`. -/
theorem operator_mul_log {z₀ : ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hU_slit : ∀ z ∈ U, z - z₀ ∈ slitPlane) {f g w₁ : ℂ → ℂ}
    (hw₁ : DifferentiableOn ℂ w₁ U)
    (hsol₁ : ∀ z ∈ U, deriv (deriv w₁) z + f z * deriv w₁ z + g z * w₁ z = 0) :
    DifferentiableOn ℂ (fun z => w₁ z * Complex.log (z - z₀)) U ∧
      ∀ z ∈ U,
        deriv (deriv fun w => w₁ w * Complex.log (w - z₀)) z +
            f z * deriv (fun w => w₁ w * Complex.log (w - z₀)) z +
            g z * (w₁ z * Complex.log (z - z₀)) =
          ((z - z₀) ^ 2)⁻¹ * (2 * (z - z₀) * deriv w₁ z + ((z - z₀) * f z - 1) * w₁ z) := by
  have hw₁_at (z) (hz : z ∈ U) : DifferentiableAt ℂ w₁ z := hw₁.differentiableAt (hU.mem_nhds hz)
  refine ⟨fun z hz =>
      ((hw₁_at z hz).hasDerivAt.mul_log_sub (hU_slit z hz)).differentiableAt.differentiableWithinAt,
    fun z hz => ?_⟩
  have hw₁_ev : ∀ᶠ u in 𝓝 z, DifferentiableAt ℂ w₁ u :=
    Eventually.mono (hU.mem_nhds hz) hw₁_at
  have hdw₁ : DifferentiableAt ℂ (deriv w₁) z :=
    (hw₁.deriv hU).differentiableAt (hU.mem_nhds hz)
  have hpt := deriv_deriv_add_mul_deriv_add_mul_mul_log_sub (f := f) (g := g)
    (hU_slit z hz) hw₁_ev hdw₁
  linear_combination hpt + Complex.log (z - z₀) * hsol₁ z hz

end TauCeti

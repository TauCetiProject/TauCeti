/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import TauCeti.Analysis.ODE.SecondOrder.Operator

import Mathlib.Analysis.Calculus.Deriv.Shift
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
  set v : ℂ → ℂ := fun u ↦ w (u + z₀)
  have hv : ∀ᶠ y in 𝓝 (z - z₀), DifferentiableAt ℂ v y := by
    have hcont : ContinuousAt (fun y : ℂ ↦ y + z₀) (z - z₀) :=
      (continuous_id.add continuous_const).continuousAt
    have htend : Tendsto (fun y : ℂ ↦ y + z₀) (𝓝 (z - z₀)) (𝓝 z) := by
      simpa [sub_add_cancel] using hcont.tendsto
    exact (htend.eventually hw).mono fun y hy ↦ hy.comp y (differentiableAt_id.add_const z₀)
  have hdv_eq : deriv v = fun y ↦ deriv w (y + z₀) := funext fun y ↦ deriv_comp_add_const w z₀ y
  have hdv : DifferentiableAt ℂ (deriv v) (z - z₀) := by
    rw [hdv_eq]
    have hdw' : DifferentiableAt ℂ (deriv w) ((z - z₀) + z₀) := by
      simpa [sub_add_cancel] using hdw
    exact hdw'.comp (z - z₀) (differentiableAt_id.add_const z₀)
  have hd1_shift := Complex.deriv_mul_log hv.self_of_nhds hzs
  have hd2_shift := Complex.deriv_deriv_mul_log hv hdv hzs
  have hd1_fun : ∀ u, deriv (fun x ↦ w x * Complex.log (x - z₀)) u =
      deriv (fun y ↦ v y * Complex.log y) (u - z₀) := fun u ↦ by
    have hΦ_eq : (fun x ↦ w x * Complex.log (x - z₀)) =
        fun x ↦ (fun y ↦ v y * Complex.log y) (x - z₀) := by
      ext x; simp [v, sub_add_cancel]
    rw [hΦ_eq]
    exact deriv_comp_sub_const (fun y ↦ v y * Complex.log y) z₀ u
  have hd1 : deriv (fun u ↦ w u * Complex.log (u - z₀)) z =
      deriv w z * Complex.log (z - z₀) + w z * (z - z₀)⁻¹ := by
    rw [hd1_fun z, hd1_shift, deriv_comp_add_const]
    simp [v, sub_add_cancel]
  have hd2 : deriv (deriv fun u ↦ w u * Complex.log (u - z₀)) z =
      deriv (deriv w) z * Complex.log (z - z₀) + 2 * deriv w z * (z - z₀)⁻¹ -
        w z * ((z - z₀) ^ 2)⁻¹ := by
    rw [funext hd1_fun, deriv_comp_sub_const (deriv fun y ↦ v y * Complex.log y) z₀ z, hd2_shift,
      show deriv v (z - z₀) = deriv w z by rw [deriv_comp_add_const]; simp [sub_add_cancel],
      show deriv (deriv v) (z - z₀) = deriv (deriv w) z by
        rw [hdv_eq, deriv_comp_add_const]; simp [sub_add_cancel]]
    simp [v, sub_add_cancel]
  have hzu0 : z - z₀ ≠ 0 := Complex.slitPlane_ne_zero hzs
  rw [hd1, hd2]
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

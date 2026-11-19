/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic

/-!
# The Gaussian damping factor on a vertical strip

For `δ, θ ∈ ℝ` the entire function `exp (δ (z - θ)²)` equals one at `θ`, is bounded on the closed
strip `0 ≤ re z ≤ 1` for `δ ≥ 0`, and for `δ > 0` decays along every vertical line. Multiplying a
bounded function on the strip by it therefore produces boundary values that vanish at infinity
without changing the value at `θ`; this is the standard device for building admissible functions
in the complex interpolation method.

## Main declarations

* `TauCeti.Complex.HadamardThreeLines.stripGaussian δ θ`: the factor `z ↦ exp (δ (z - θ)²)`.
* `TauCeti.Complex.HadamardThreeLines.norm_stripGaussian_le`: for `δ ≥ 0`, its norm is at most
  `exp (δ (|θ| + 1)²)` on the closed strip.
* `TauCeti.Complex.HadamardThreeLines.tendsto_norm_stripGaussian`: for `δ > 0`, it tends to zero
  along every vertical line.
* `TauCeti.Complex.HadamardThreeLines.stripGaussianSMul`: the product of the factor on the line
  `re z = a` with a bounded continuous function, as a function vanishing at infinity.
-/

public noncomputable section

open Complex Filter Set Topology
open scoped BoundedContinuousFunction ZeroAtInfty

namespace TauCeti.Complex.HadamardThreeLines

/-- The Gaussian factor `exp (δ (z - θ)²)`, equal to one at `θ` and decaying along vertical
lines for `δ > 0`. Multiplying by it makes the boundary traces of an admissible function vanish
at infinity without changing its value at `θ`. -/
def stripGaussian (δ θ : ℝ) (z : ℂ) : ℂ :=
  exp (δ * (z - θ) ^ 2)

theorem stripGaussian_apply (δ θ : ℝ) (z : ℂ) : stripGaussian δ θ z = exp (δ * (z - θ) ^ 2) :=
  (rfl)

/-- The Gaussian factor is one at `θ`. -/
@[simp]
theorem stripGaussian_self (δ θ : ℝ) : stripGaussian δ θ θ = 1 := by
  simp [stripGaussian_apply]

/-- The Gaussian factor is entire. -/
theorem differentiable_stripGaussian (δ θ : ℝ) : Differentiable ℂ (stripGaussian δ θ) := by
  simp_rw [funext (stripGaussian_apply δ θ)]
  fun_prop

/-- The modulus of the Gaussian factor: `|exp (δ (z - θ)²)| = exp (δ ((re z - θ)² - (im z)²))`. -/
theorem norm_stripGaussian (δ θ : ℝ) (z : ℂ) :
    ‖stripGaussian δ θ z‖ = Real.exp (δ * ((z.re - θ) ^ 2 - z.im ^ 2)) := by
  rw [stripGaussian_apply, norm_exp]
  congr 1
  simp [sq]

/-- For `δ ≥ 0`, the Gaussian factor is bounded on the closed strip `0 ≤ re z ≤ 1`. -/
theorem norm_stripGaussian_le {δ : ℝ} (hδ : 0 ≤ δ) (θ : ℝ) {z : ℂ} (hz : z.re ∈ Icc 0 1) :
    ‖stripGaussian δ θ z‖ ≤ Real.exp (δ * (|θ| + 1) ^ 2) := by
  rw [norm_stripGaussian]
  refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hδ)
  have h : (z.re - θ) ^ 2 ≤ (|θ| + 1) ^ 2 :=
    sq_le_sq' (by linarith [hz.1, le_abs_self θ]) (by linarith [hz.2, neg_abs_le θ])
  nlinarith [sq_nonneg z.im]

/-- For `δ > 0`, the Gaussian factor tends to zero along every vertical line. -/
theorem tendsto_norm_stripGaussian {δ : ℝ} (hδ : 0 < δ) (θ a : ℝ) :
    Tendsto (fun t : ℝ => ‖stripGaussian δ θ (a + t * I)‖) (cocompact ℝ) (𝓝 0) := by
  have hsq : Tendsto (fun t : ℝ => t ^ 2) (cocompact ℝ) atTop :=
    ((tendsto_pow_atTop two_ne_zero).comp (tendsto_norm_cocompact_atTop (E := ℝ))).congr
      fun t => by simp
  have h : Tendsto (fun t : ℝ => δ * ((a - θ) ^ 2 - t ^ 2)) (cocompact ℝ) atBot :=
    ((tendsto_atBot_add_const_left _ ((a - θ) ^ 2)
      (tendsto_neg_atTop_atBot.comp hsq)).const_mul_atBot hδ).congr fun t => by
        simp [sub_eq_add_neg]
  have heq : (fun t : ℝ => ‖stripGaussian δ θ (a + t * I)‖) =
      Real.exp ∘ fun t => δ * ((a - θ) ^ 2 - t ^ 2) := by
    funext t
    simp [norm_stripGaussian]
  rw [heq]
  exact Real.tendsto_exp_atBot.comp h

section StripGaussianSMul

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- For `δ > 0`, the product `t ↦ exp (δ (a + i t - θ)²) • f t` of the Gaussian factor on the
vertical line `re z = a` with a bounded continuous function `f`, which vanishes at infinity. -/
def stripGaussianSMul {δ : ℝ} (hδ : 0 < δ) (θ a : ℝ) (f : ℝ →ᵇ X) : C₀(ℝ, X) :=
  ⟨⟨fun t => stripGaussian δ θ (a + t * I) • f t,
      ((differentiable_stripGaussian δ θ).continuous.comp (by fun_prop)).smul f.continuous⟩,
    squeeze_zero_norm (fun t => (norm_smul _ _).trans_le
        (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm t) (norm_nonneg _)))
      (by simpa using (tendsto_norm_stripGaussian hδ θ a).mul_const ‖f‖)⟩

@[simp]
theorem stripGaussianSMul_apply {δ : ℝ} (hδ : 0 < δ) (θ a : ℝ) (f : ℝ →ᵇ X) (t : ℝ) :
    stripGaussianSMul hδ θ a f t = stripGaussian δ θ (a + t * I) • f t :=
  (rfl)

/-- On a vertical line `re z = a` in the closed strip, the damped function has norm at most
`exp (δ (|θ| + 1)²) ‖f‖`. -/
theorem norm_stripGaussianSMul_le {δ : ℝ} (hδ : 0 < δ) (θ : ℝ) {a : ℝ} (ha : a ∈ Icc 0 1)
    (f : ℝ →ᵇ X) : ‖stripGaussianSMul hδ θ a f‖ ≤ Real.exp (δ * (|θ| + 1) ^ 2) * ‖f‖ :=
  (ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun t =>
    (norm_smul _ _).trans_le (mul_le_mul
      (norm_stripGaussian_le hδ.le θ (z := a + t * I) (by simpa using ha))
      (f.norm_coe_le_norm t) (norm_nonneg _) (Real.exp_pos _).le)

end StripGaussianSMul

end TauCeti.Complex.HadamardThreeLines

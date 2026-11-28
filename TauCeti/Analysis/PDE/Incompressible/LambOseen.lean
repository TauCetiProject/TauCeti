/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Incompressible.CircularFlow
public import TauCeti.Analysis.PDE.HeatKernel.Basic
public import Mathlib.Analysis.Calculus.DSlope
import TauCeti.Analysis.SpecialFunctions.Exp.DividedDifference
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic

/-!
# The Lamb–Oseen vortex

On an oriented Euclidean plane with quarter turn `J`, the **Lamb–Oseen vortex** of circulation
`Γ` is the velocity field

`u(x, t) = (Γ / (2π ‖x‖²)) (1 - exp (-‖x‖² / (4νt))) J x`,

the circular flow (`Orientation.circularFlow`) whose vorticity is the heat kernel
`ω(x, t) = Γ K_{νt}(x)`. It is the explicit classical solution of the Navier–Stokes equations on
`(0, ∞) × ℝ²` that describes the viscous spreading of a point vortex, and the vorticity of every
integrable planar solution approaches it at large times.

Write `τ = νt` for the heat time. The field `Orientation.lambOseenVelocity o Γ τ` is the circular
flow with the smooth angular velocity profile `TauCeti.lambOseenProfile Γ τ`, whose circulation
function is `s ρ(s) = (Γ / 2π) (1 - exp (-s / (4τ)))`; the removable singularity at the origin is
filled by `dslope exp 0`. This file proves:

* `Orientation.lambOseenVelocity_apply_of_ne`: the closed formula above away from the origin.
* `Orientation.isSolenoidalOn_lambOseenVelocity`: `u` is smooth and divergence free.
* `Orientation.fderiv_lambOseenVelocity_sub_adjoint`: its vorticity tensor is
  `∇u - (∇u)† = Γ K_τ(x) J`, so its scalar vorticity is `ω = Γ K_τ`.
* `Orientation.hasDerivAt_lambOseenVelocity`: `u` solves the vector heat equation
  `∂_τ u = Δu`, with `Δu = -(Γ K_τ(x) / (2τ)) J x` (`Orientation.laplacian_lambOseenVelocity`).
* `Orientation.hasDerivAt_lambOseenVelocity_mul`: with the pressure
  `TauCeti.lambOseenPressure`, `(x, t) ↦ u(x, νt)` solves the Navier–Stokes equations
  `∂ₜu + (u · ∇) u + ∇p = νΔu`, because the convective term is a gradient,
  `(u · ∇) u + ∇p = 0`.
* `Orientation.hasDerivAt_mul_heatKernel_mul`: the vorticity solves the vorticity equation
  `∂ₜω + u · ∇ω = νΔω`, in which `u · ∇ω = 0` because `ω` is radial and `u` is tangential
  (`Orientation.fderiv_heatKernel_apply_circularFlow`).
* `Orientation.tendsto_norm_mul_norm_lambOseenVelocity`,
  `Orientation.not_memLp_lambOseenVelocity`: the velocity decays exactly like
  `|Γ| / (2π ‖x‖)`, so for `Γ ≠ 0` it is not square integrable. Thus the Lamb–Oseen vortex is a
  classical solution outside the energy class of Leray–Hopf weak solutions.

## References

* C. W. Oseen, *Über Wirbelbewegung in einer reibenden Flüssigkeit*, Ark. Mat. Astro. Fys. 7
  (1912).
* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge University
  Press, 2002, §2.2.1 (radial vorticity and circular flows).
* T. Gallay and C. E. Wayne, *Global stability of vortex solutions of the two-dimensional
  Navier–Stokes equation*, Comm. Math. Phys. 255 (2005), 97–129.
-/

public section

noncomputable section

open InnerProductSpace Laplacian MeasureTheory Metric Real Set Filter Topology
open scoped Gradient RealInnerProductSpace

namespace TauCeti

/-- The angular velocity profile of the Lamb–Oseen vortex of circulation `Γ` at heat time `τ`:
`ρ(s) = (Γ / (2π s)) (1 - exp (-s / (4τ)))`, with its removable singularity at `s = 0` filled in
as `Γ / (8πτ)` through `dslope exp 0`. -/
def lambOseenProfile (Γ τ s : ℝ) : ℝ :=
  Γ / (8 * π * τ) * dslope exp 0 (-s / (4 * τ))

theorem lambOseenProfile_apply (Γ τ s : ℝ) :
    lambOseenProfile Γ τ s = Γ / (8 * π * τ) * dslope exp 0 (-s / (4 * τ)) :=
  (rfl)

/-- The circulation function of the Lamb–Oseen profile:
`s ρ(s) = (Γ / 2π) (1 - exp (-s / (4τ)))`. -/
theorem mul_lambOseenProfile (Γ : ℝ) {τ : ℝ} (hτ : τ ≠ 0) (s : ℝ) :
    s * lambOseenProfile Γ τ s = Γ / (2 * π) * (1 - exp (-s / (4 * τ))) := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  have hu : -s / (4 * τ) ≠ 0 := div_ne_zero (neg_ne_zero.mpr hs) (by positivity)
  rw [lambOseenProfile_apply, dslope_exp_zero_of_ne hu]
  field_simp
  ring

/-- Away from `s = 0`, the Lamb–Oseen profile is `(Γ / (2π s)) (1 - exp (-s / (4τ)))`. -/
theorem lambOseenProfile_of_ne (Γ : ℝ) {τ s : ℝ} (hτ : τ ≠ 0) (hs : s ≠ 0) :
    lambOseenProfile Γ τ s = Γ / (2 * π * s) * (1 - exp (-s / (4 * τ))) := by
  rw [← mul_div_cancel_left₀ (lambOseenProfile Γ τ s) hs, mul_lambOseenProfile Γ hτ s]
  field_simp

theorem contDiff_lambOseenProfile (Γ τ : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (lambOseenProfile Γ τ) := by
  have h : ContDiff ℝ n (dslope exp 0) :=
    ((analyticOnNhd_rexp (u := Set.univ)).dslope 0).contDiff
  exact contDiff_const.mul (h.comp (contDiff_id.neg.div_const _))

/-- The derivative of the Lamb–Oseen circulation function. -/
private theorem hasDerivAt_mul_lambOseenProfile (Γ : ℝ) {τ : ℝ} (hτ : τ ≠ 0) (s : ℝ) :
    HasDerivAt (fun r ↦ r * lambOseenProfile Γ τ r) (Γ / (8 * π * τ) * exp (-s / (4 * τ))) s := by
  rw [funext (mul_lambOseenProfile Γ hτ)]
  refine ((((hasDerivAt_id' s).fun_neg.div_const (4 * τ)).exp.const_sub 1).const_mul
    (Γ / (2 * π))).congr_deriv ?_
  field_simp
  ring

/-- The first derivative of the Lamb–Oseen circulation function `B(s) = s ρ(s)`:
`B'(s) = (Γ / (8πτ)) exp (-s / (4τ))`. Twice this is the vorticity `Γ K_τ`. -/
theorem deriv_mul_lambOseenProfile (Γ : ℝ) {τ : ℝ} (hτ : τ ≠ 0) (s : ℝ) :
    deriv (fun r ↦ r * lambOseenProfile Γ τ r) s = Γ / (8 * π * τ) * exp (-s / (4 * τ)) :=
  (hasDerivAt_mul_lambOseenProfile Γ hτ s).deriv

/-- The second derivative of the Lamb–Oseen circulation function:
`B''(s) = -(Γ / (32πτ²)) exp (-s / (4τ))`. -/
theorem deriv_deriv_mul_lambOseenProfile (Γ : ℝ) {τ : ℝ} (hτ : τ ≠ 0) (s : ℝ) :
    deriv (deriv fun r ↦ r * lambOseenProfile Γ τ r) s =
      -(Γ / (32 * π * τ ^ 2) * exp (-s / (4 * τ))) := by
  rw [funext (deriv_mul_lambOseenProfile Γ hτ)]
  refine ((((hasDerivAt_id' s).fun_neg.div_const (4 * τ)).exp.const_mul
    (Γ / (8 * π * τ))).congr_deriv ?_).deriv
  field_simp
  ring

/-- The pressure of the Lamb–Oseen vortex of circulation `Γ` at heat time `τ`: the circular
pressure `½ ∫₀^{‖x‖²} ρ²` of its angular velocity profile. -/
def lambOseenPressure {E : Type*} [NormedAddCommGroup E] (Γ τ : ℝ) : E → ℝ :=
  circularPressure (lambOseenProfile Γ τ)

theorem lambOseenPressure_eq_circularPressure {E : Type*} [NormedAddCommGroup E] (Γ τ : ℝ) :
    (lambOseenPressure Γ τ : E → ℝ) = circularPressure (lambOseenProfile Γ τ) :=
  (rfl)

/-- The gradient of the Lamb–Oseen pressure is `∇p(x) = ρ(‖x‖²)² x`. -/
theorem hasGradientAt_lambOseenPressure {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (Γ τ : ℝ) (x : E) :
    HasGradientAt (lambOseenPressure Γ τ) (lambOseenProfile Γ τ (‖x‖ ^ 2) ^ 2 • x) x :=
  hasGradientAt_circularPressure (contDiff_lambOseenProfile Γ τ (n := 0)).continuous x

end TauCeti

namespace Orientation

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)] (o : Orientation ℝ E (Fin 2)) {Γ τ : ℝ} {x : E}

local notation "J" => o.rightAngleRotation

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

/-- The **Lamb–Oseen vortex** of circulation `Γ` at heat time `τ = νt`: the circular flow
`u(x) = (Γ / (2π ‖x‖²)) (1 - exp (-‖x‖² / (4τ))) J x` whose vorticity is `Γ K_τ`. -/
def lambOseenVelocity (Γ τ : ℝ) : E → E :=
  o.circularFlow (lambOseenProfile Γ τ)

theorem lambOseenVelocity_eq_circularFlow (Γ τ : ℝ) :
    o.lambOseenVelocity Γ τ = o.circularFlow (lambOseenProfile Γ τ) :=
  (rfl)

/-- The closed formula for the Lamb–Oseen velocity away from the origin. -/
theorem lambOseenVelocity_apply_of_ne (Γ : ℝ) (hτ : τ ≠ 0) (hx : x ≠ 0) :
    o.lambOseenVelocity Γ τ x =
      (Γ / (2 * π * ‖x‖ ^ 2) * (1 - exp (-‖x‖ ^ 2 / (4 * τ)))) • J x := by
  rw [lambOseenVelocity_eq_circularFlow, circularFlow_apply,
    lambOseenProfile_of_ne Γ hτ (by positivity)]

@[simp]
theorem lambOseenVelocity_zero (Γ τ : ℝ) : o.lambOseenVelocity Γ τ (0 : E) = 0 :=
  o.circularFlow_zero _

theorem contDiff_lambOseenVelocity (Γ τ : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (o.lambOseenVelocity Γ τ) :=
  contDiff_circularFlow (contDiff_lambOseenProfile Γ τ)

/-- The Lamb–Oseen velocity is divergence free. -/
theorem trace_fderiv_lambOseenVelocity (Γ τ : ℝ) (x : E) :
    LinearMap.trace ℝ E (fderiv ℝ (o.lambOseenVelocity Γ τ) x) = 0 :=
  o.trace_fderiv_circularFlow ((contDiff_lambOseenProfile Γ τ (n := 1)).differentiable
    one_ne_zero _)

/-- The Lamb–Oseen velocity is solenoidal on the whole plane. -/
theorem isSolenoidalOn_lambOseenVelocity [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.IsAddHaarMeasure] (Γ τ : ℝ) : IsSolenoidalOn μ ⊤ (o.lambOseenVelocity Γ τ) :=
  o.isSolenoidalOn_circularFlow (contDiff_lambOseenProfile Γ τ)

/-- **The vorticity of the Lamb–Oseen vortex is the heat kernel.** The antisymmetric part of its
derivative is `Du(x) - Du(x)† = Γ K_τ(x) J`, so its scalar vorticity is `ω = Γ K_τ`. -/
theorem fderiv_lambOseenVelocity_sub_adjoint (Γ : ℝ) (hτ : τ ≠ 0) (x : E) :
    fderiv ℝ (o.lambOseenVelocity Γ τ) x -
        ContinuousLinearMap.adjoint (fderiv ℝ (o.lambOseenVelocity Γ τ) x) =
      (Γ * heatKernel τ x) • (o.rightAngleRotation.toContinuousLinearEquiv : E →L[ℝ] E) := by
  rw [lambOseenVelocity_eq_circularFlow, o.fderiv_circularFlow_sub_adjoint
    ((contDiff_lambOseenProfile Γ τ (n := 1)).differentiable one_ne_zero _),
    deriv_mul_lambOseenProfile Γ hτ, heatKernel_apply_of_finrank_eq_two Fact.out]
  congr 1
  field_simp
  ring

/-- The vector Laplacian of the Lamb–Oseen velocity: `Δu(x) = -(Γ K_τ(x) / (2τ)) J x`. -/
theorem laplacian_lambOseenVelocity (Γ : ℝ) (hτ : τ ≠ 0) (x : E) :
    Δ (o.lambOseenVelocity Γ τ) x = -(Γ * heatKernel τ x / (2 * τ)) • J x := by
  rw [lambOseenVelocity_eq_circularFlow,
    o.laplacian_circularFlow (contDiff_lambOseenProfile Γ τ).contDiffAt,
    deriv_deriv_mul_lambOseenProfile Γ hτ, heatKernel_apply_of_finrank_eq_two Fact.out]
  congr 1
  field_simp
  ring

/-- **The Lamb–Oseen velocity solves the vector heat equation** `∂_τ u = Δu` for `τ > 0`. -/
theorem hasDerivAt_lambOseenVelocity (Γ : ℝ) (hτ : 0 < τ) (x : E) :
    HasDerivAt (fun σ ↦ o.lambOseenVelocity Γ σ x) (Δ (o.lambOseenVelocity Γ τ) x) τ := by
  rw [o.laplacian_lambOseenVelocity Γ hτ.ne']
  rcases eq_or_ne x 0 with rfl | hx
  · simpa using hasDerivAt_const τ (0 : E)
  have hf : HasDerivAt (fun σ ↦ Γ / (2 * π * ‖x‖ ^ 2) * (1 - exp (-‖x‖ ^ 2 / 4 * σ⁻¹)))
      (Γ / (2 * π * ‖x‖ ^ 2) * -(exp (-‖x‖ ^ 2 / 4 * τ⁻¹) * (-‖x‖ ^ 2 / 4 * -(τ ^ 2)⁻¹))) τ :=
    ((((hasDerivAt_inv hτ.ne').const_mul (-‖x‖ ^ 2 / 4)).exp).const_sub 1).const_mul _
  refine (hf.smul_const (J x)).congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards [lt_mem_nhds hτ] with σ hσ
    rw [o.lambOseenVelocity_apply_of_ne Γ hσ.ne' hx]
    congr 4
    ring
  · rw [heatKernel_apply_of_finrank_eq_two Fact.out]
    congr 1
    field_simp

/-- The convective term of the Lamb–Oseen vortex is a gradient: `(u · ∇) u + ∇p = 0` for the
Lamb–Oseen pressure. -/
theorem fderiv_lambOseenVelocity_apply_self_add_gradient_lambOseenPressure (Γ τ : ℝ) (x : E) :
    fderiv ℝ (o.lambOseenVelocity Γ τ) x (o.lambOseenVelocity Γ τ x) +
        ∇ (lambOseenPressure Γ τ) x = 0 :=
  o.fderiv_circularFlow_apply_self_add_gradient_circularPressure
    (contDiff_lambOseenProfile Γ τ (n := 0)).continuous
    ((contDiff_lambOseenProfile Γ τ (n := 1)).differentiable one_ne_zero _)

/-- **The Lamb–Oseen vortex solves the Navier–Stokes equations.** For viscosity `ν > 0`, the
velocity `u(x, t) = lambOseenVelocity Γ (νt) x` and the pressure
`p(x, t) = lambOseenPressure Γ (νt) x` satisfy `∂ₜu = νΔu - (u · ∇) u - ∇p` at every `t > 0`
and every `x`, and `u` is divergence free (`Orientation.trace_fderiv_lambOseenVelocity`). -/
theorem hasDerivAt_lambOseenVelocity_mul (Γ : ℝ) {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (x : E) :
    HasDerivAt (fun s ↦ o.lambOseenVelocity Γ (ν * s) x)
      (ν • Δ (o.lambOseenVelocity Γ (ν * t)) x -
        fderiv ℝ (o.lambOseenVelocity Γ (ν * t)) x (o.lambOseenVelocity Γ (ν * t) x) -
          ∇ (lambOseenPressure Γ (ν * t)) x) t := by
  rw [sub_sub, o.fderiv_lambOseenVelocity_apply_self_add_gradient_lambOseenPressure, sub_zero]
  have h := (o.hasDerivAt_lambOseenVelocity Γ (mul_pos hν ht) x).scomp t
    ((hasDerivAt_id' t).const_mul ν)
  simpa only [Function.comp_def, mul_one] using h

/-- The heat kernel is radial and a circular flow is tangential, so the transport of the heat
kernel by a circular flow vanishes: `u · ∇K_τ = 0`. -/
theorem fderiv_heatKernel_apply_circularFlow (τ : ℝ) (ρ : ℝ → ℝ) (x : E) :
    fderiv ℝ (heatKernel τ) x (o.circularFlow ρ x) = 0 := by
  rw [(hasGradientAt_heatKernel τ x).hasFDerivAt.fderiv, toDual_apply_apply,
    real_inner_smul_left, real_inner_smul_left, real_inner_comm, inner_circularFlow_self,
    mul_zero, mul_zero]

/-- **The vorticity equation of the Lamb–Oseen vortex.** For viscosity `ν > 0`, the vorticity
`ω(x, t) = Γ K_{νt}(x)` of the Lamb–Oseen velocity `u(x, t) = lambOseenVelocity Γ (νt) x` solves
`∂ₜω + u · ∇ω = νΔω`, with `u · ∇ω = 0`. -/
theorem hasDerivAt_mul_heatKernel_mul (Γ : ℝ) {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (x : E) :
    HasDerivAt (fun s ↦ Γ * heatKernel (ν * s) x)
      (ν * Δ (fun y : E ↦ Γ * heatKernel (ν * t) y) x -
        fderiv ℝ (fun y ↦ Γ * heatKernel (ν * t) y) x (o.lambOseenVelocity Γ (ν * t) x)) t := by
  rw [fderiv_const_mul ((contDiff_heatKernel (ν * t) (k := 1)).differentiable one_ne_zero x),
    smul_apply, lambOseenVelocity_eq_circularFlow,
    o.fderiv_heatKernel_apply_circularFlow, smul_zero, sub_zero]
  have hΔ : Δ (fun y : E ↦ Γ * heatKernel (ν * t) y) x = Γ * Δ (heatKernel (ν * t) : E → ℝ) x :=
    laplacian_smul Γ (contDiff_heatKernel (ν * t)).contDiffAt
  have h := ((hasDerivAt_heatKernel (mul_pos hν ht) x).scomp t
    ((hasDerivAt_id' t).const_mul ν)).const_mul Γ
  rw [hΔ]
  simp only [Function.comp_def, smul_eq_mul] at h
  convert h using 1
  ring

/-- **The Lamb–Oseen velocity decays like a point vortex**: `‖x‖ ‖u(x)‖ → |Γ| / (2π)` as
`‖x‖ → ∞`. -/
theorem tendsto_norm_mul_norm_lambOseenVelocity (Γ : ℝ) (hτ : 0 < τ) :
    Tendsto (fun x : E ↦ ‖x‖ * ‖o.lambOseenVelocity Γ τ x‖) (cocompact E)
      (𝓝 (|Γ| / (2 * π))) := by
  have heq : (fun x : E ↦ ‖x‖ * ‖o.lambOseenVelocity Γ τ x‖) =
      fun x ↦ |Γ / (2 * π) * (1 - exp (-‖x‖ ^ 2 / (4 * τ)))| := by
    funext x
    rw [lambOseenVelocity_eq_circularFlow, norm_circularFlow, ← mul_lambOseenProfile Γ hτ.ne',
      abs_mul, abs_of_nonneg (sq_nonneg ‖x‖)]
    ring
  have hsq : Tendsto (fun x : E ↦ ‖x‖ ^ 2 / (4 * τ)) (cocompact E) atTop :=
    ((tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cocompact_atTop).atTop_div_const
      (by positivity)
  have hexp : Tendsto (fun x : E ↦ exp (-‖x‖ ^ 2 / (4 * τ))) (cocompact E) (𝓝 0) := by
    simpa only [neg_div, Function.comp_def] using tendsto_exp_neg_atTop_nhds_zero.comp hsq
  rw [heq]
  convert ((hexp.const_sub 1).const_mul (Γ / (2 * π))).abs using 2
  rw [sub_zero, mul_one, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]

/-- Far from the core, where `‖x‖² > 4τ`, the kinetic energy density of the Lamb–Oseen vortex
dominates the bracket `(1 + ‖x‖²)⁻¹`. -/
private theorem inv_one_add_norm_sq_le_mul_norm_lambOseenVelocity_sq (hΓ : Γ ≠ 0) (hτ : 0 < τ)
    (hx : 4 * τ < ‖x‖ ^ 2) :
    (1 + ‖x‖ ^ 2)⁻¹ ≤ 16 * π ^ 2 / Γ ^ 2 * ‖o.lambOseenVelocity Γ τ x‖ ^ 2 := by
  have hs0 : 0 < ‖x‖ ^ 2 := by linarith
  -- The circulation function is at least half its limit `Γ / (2π)` there.
  have hexp : exp (-‖x‖ ^ 2 / (4 * τ)) ≤ 1 / 2 := by
    have h1 : -‖x‖ ^ 2 / (4 * τ) ≤ -1 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    calc exp (-‖x‖ ^ 2 / (4 * τ)) ≤ exp (-1) := exp_le_exp.mpr h1
      _ ≤ 1 / 2 := by
        rw [exp_neg, inv_le_comm₀ (exp_pos 1) (by norm_num)]
        linarith [add_one_le_exp (1 : ℝ)]
  have hB : |Γ| / (4 * π) ≤ |‖x‖ ^ 2 * lambOseenProfile Γ τ (‖x‖ ^ 2)| := by
    rw [mul_lambOseenProfile Γ hτ.ne', abs_mul, abs_div, abs_of_pos (by positivity : 0 < 2 * π),
      abs_of_nonneg (by linarith : 0 ≤ 1 - exp (-‖x‖ ^ 2 / (4 * τ))),
      show |Γ| / (4 * π) = |Γ| / (2 * π) * (1 / 2) by field_simp; ring]
    gcongr
    linarith
  have hnorm : ‖o.lambOseenVelocity Γ τ x‖ ^ 2 =
      |‖x‖ ^ 2 * lambOseenProfile Γ τ (‖x‖ ^ 2)| ^ 2 / ‖x‖ ^ 2 := by
    rw [lambOseenVelocity_eq_circularFlow, norm_circularFlow, abs_mul,
      abs_of_nonneg (sq_nonneg ‖x‖)]
    field_simp
  rw [hnorm]
  calc (1 + ‖x‖ ^ 2)⁻¹ ≤ (‖x‖ ^ 2)⁻¹ := inv_anti₀ hs0 (by linarith)
    _ = 16 * π ^ 2 / Γ ^ 2 * ((|Γ| / (4 * π)) ^ 2 / ‖x‖ ^ 2) := by
      rw [div_pow, sq_abs]
      field_simp
      norm_num
    _ ≤ 16 * π ^ 2 / Γ ^ 2 * (|‖x‖ ^ 2 * lambOseenProfile Γ τ (‖x‖ ^ 2)| ^ 2 / ‖x‖ ^ 2) := by
      gcongr

/-- **The Lamb–Oseen vortex has infinite energy.** For `Γ ≠ 0` and `τ > 0` the velocity is not
square integrable, for any additive Haar measure: it decays only like `|Γ| / (2π ‖x‖)`. So the
Lamb–Oseen vortex is a classical solution of the Navier–Stokes equations which is not a weak
solution in the energy class. -/
theorem not_memLp_lambOseenVelocity [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.IsAddHaarMeasure] (hΓ : Γ ≠ 0) (hτ : 0 < τ) :
    ¬ MemLp (o.lambOseenVelocity Γ τ) 2 μ := by
  intro hu
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ (Fact.out : Module.finrank ℝ E = 2)
  have hint : Integrable (fun x ↦ ‖o.lambOseenVelocity Γ τ x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
  set R := 2 * √τ
  have hR : R ^ 2 = 4 * τ := by rw [mul_pow, sq_sqrt hτ.le]; norm_num
  have hcont : Continuous fun x : E ↦ (1 + ‖x‖ ^ 2) ^ (-(2 : ℝ) / 2) :=
    (continuous_const.add (continuous_norm.pow 2)).rpow_const fun y ↦
      Or.inl (by positivity : (1 : ℝ) + ‖y‖ ^ 2 ≠ 0)
  -- The bracket `(1 + ‖x‖²)⁻¹` is integrable on the closed ball of radius `2 √τ`, and outside it
  -- is dominated by the kinetic energy density, so it would be integrable.
  have hfar : ∀ x ∈ (closedBall (0 : E) R)ᶜ, ‖(1 + ‖x‖ ^ 2) ^ (-(2 : ℝ) / 2)‖ ≤
      16 * π ^ 2 / Γ ^ 2 * ‖o.lambOseenVelocity Γ τ x‖ ^ 2 := by
    intro x hx
    have hxR : R < ‖x‖ := by simpa using hx
    rw [Real.norm_of_nonneg (by positivity), show -(2 : ℝ) / 2 = -1 by norm_num, rpow_neg_one]
    exact o.inv_one_add_norm_sq_le_mul_norm_lambOseenVelocity_sq hΓ hτ
      (hR ▸ pow_lt_pow_left₀ hxR (by positivity) two_ne_zero)
  have hbracket : Integrable (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ (-(2 : ℝ) / 2)) μ := by
    rw [← integrableOn_univ, ← union_compl_self (closedBall (0 : E) R), integrableOn_union]
    refine ⟨hcont.continuousOn.integrableOn_compact (isCompact_closedBall _ _), ?_⟩
    exact (hint.const_mul _).integrableOn.mono' hcont.aestronglyMeasurable.restrict
      (ae_restrict_of_forall_mem measurableSet_closedBall.compl hfar)
  -- But the bracket at the critical exponent `2 = dim E` is not integrable.
  have h2 := (integrable_rpow_neg_one_add_norm_sq_iff μ).1 hbracket
  rw [(Fact.out : Module.finrank ℝ E = 2)] at h2
  norm_num at h2

end Orientation

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence.Basic
import Mathlib.Analysis.InnerProductSpace.Trace
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Calculus.ContDiff.Differentiable

/-!
# Circular flows in an oriented Euclidean plane

Let `J` be the quarter turn `o.rightAngleRotation` of an oriented Euclidean plane `E`. For a real
function `ρ`, the **circular flow** with angular velocity profile `ρ` is the velocity field

`u(x) = ρ(‖x‖²) J x`,

which rotates the circle of radius `r` about the origin rigidly at angular velocity `ρ(r²)`. Its
flow lines are these circles. Rigid rotation (`ρ = 1`) and the Lamb–Oseen vortex are circular
flows, and so is the point vortex (`ρ(s) = Γ / (2π s)`) away from the origin.

The differential calculus of such a field is governed by the function `B(s) = s ρ(s)`, which is
`1 / (2π)` times the circulation of `u` around the circle `‖x‖² = s`. This file proves:

* `Orientation.trace_fderiv_circularFlow`, `Orientation.isSolenoidalOn_circularFlow`: `u` is
  divergence free.
* `Orientation.fderiv_circularFlow_sub_adjoint`: its vorticity tensor is
  `∇u - (∇u)† = 2 B'(‖x‖²) J`, so its scalar vorticity is `ω(x) = 2 B'(‖x‖²)`.
* `Orientation.fderiv_circularFlow_apply_self`: its convective term is the centripetal
  acceleration `(u · ∇) u = -ρ(‖x‖²)² x`.
* `Orientation.fderiv_circularFlow_apply_self_add_gradient_circularPressure`: this acceleration is
  balanced by the radial pressure `p(x) = ½ ∫₀^{‖x‖²} ρ²` of `TauCeti.circularPressure`:
  `(u · ∇) u + ∇p = 0`. So every circular flow is a stationary solution of the Euler equations.
* `Orientation.laplacian_circularFlow`: its vector Laplacian is `Δu(x) = 4 B''(‖x‖²) J x`.

All identities are pointwise and use the regularity of `ρ` only at `‖x‖²`.

## References

* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge University
  Press, 2002, §2.2.1 (radial vorticity and circular flows).
-/

public section

noncomputable section

open InnerProductSpace Laplacian MeasureTheory Set
open scoped Gradient RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E]

/-- The radial pressure `p(x) = ½ ∫₀^{‖x‖²} ρ(r)² dr` balancing the centripetal acceleration of the
circular flow with angular velocity profile `ρ`. -/
def circularPressure (ρ : ℝ → ℝ) (x : E) : ℝ :=
  (∫ r in (0 : ℝ)..‖x‖ ^ 2, ρ r ^ 2) / 2

theorem circularPressure_apply (ρ : ℝ → ℝ) (x : E) :
    circularPressure ρ x = (∫ r in (0 : ℝ)..‖x‖ ^ 2, ρ r ^ 2) / 2 :=
  (rfl)

/-- The gradient of the circular pressure is `∇p(x) = ρ(‖x‖²)² x`. -/
theorem hasGradientAt_circularPressure [InnerProductSpace ℝ E] [CompleteSpace E] {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) (x : E) : HasGradientAt (circularPressure ρ) (ρ (‖x‖ ^ 2) ^ 2 • x) x := by
  have hF : HasDerivAt (fun s ↦ ∫ r in (0 : ℝ)..s, ρ r ^ 2) (ρ (‖x‖ ^ 2) ^ 2) (‖x‖ ^ 2) :=
    intervalIntegral.integral_hasDerivAt_right ((hρ.pow 2).intervalIntegrable _ _)
      (hρ.pow 2).aestronglyMeasurable.stronglyMeasurableAtFilter
      (hρ.pow 2).continuousAt
  have h := (hF.comp_hasFDerivAt x ((hasFDerivAt_id x).norm_sq)).mul_const (2⁻¹ : ℝ)
  simp only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] at h
  have hfun : circularPressure ρ = fun y : E ↦ (∫ r in (0 : ℝ)..‖y‖ ^ 2, ρ r ^ 2) * 2⁻¹ :=
    funext fun y ↦ div_eq_mul_inv _ _
  rw [hasGradientAt_iff_hasFDerivAt, hfun]
  refine h.congr_fderiv ?_
  ext h'
  simp only [smul_apply, innerSL_apply_apply, nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul,
    toDual_apply_apply, real_inner_smul_left]
  ring

end TauCeti

namespace Orientation

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)] (o : Orientation ℝ E (Fin 2))

local notation "J" => o.rightAngleRotation

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

/-- The **circular flow** with angular velocity profile `ρ`: the velocity field
`x ↦ ρ(‖x‖²) J x`, which turns the circle of radius `r` about the origin rigidly at angular
velocity `ρ(r²)`, counterclockwise for the orientation `o` where `ρ > 0`. -/
def circularFlow (ρ : ℝ → ℝ) (x : E) : E :=
  ρ (‖x‖ ^ 2) • J x

theorem circularFlow_apply (ρ : ℝ → ℝ) (x : E) : o.circularFlow ρ x = ρ (‖x‖ ^ 2) • J x :=
  (rfl)

@[simp]
theorem circularFlow_zero (ρ : ℝ → ℝ) : o.circularFlow ρ (0 : E) = 0 := by
  simp [circularFlow_apply]

@[simp]
theorem inner_circularFlow_self (ρ : ℝ → ℝ) (x : E) : ⟪o.circularFlow ρ x, x⟫ = 0 := by
  simp [circularFlow_apply, real_inner_smul_left]

@[simp]
theorem norm_circularFlow (ρ : ℝ → ℝ) (x : E) : ‖o.circularFlow ρ x‖ = |ρ (‖x‖ ^ 2)| * ‖x‖ := by
  simp [circularFlow_apply, norm_smul]

variable {o} in
theorem contDiff_circularFlow {n : WithTop ℕ∞} {ρ : ℝ → ℝ} (hρ : ContDiff ℝ n ρ) :
    ContDiff ℝ n (o.circularFlow ρ) :=
  (hρ.comp (contDiff_norm_sq ℝ)).smul
    (o.rightAngleRotation.toContinuousLinearEquiv.toContinuousLinearMap.contDiff)

variable {o} in
theorem contDiffAt_circularFlow {n : WithTop ℕ∞} {ρ : ℝ → ℝ} {x : E}
    (hρ : ContDiffAt ℝ n ρ (‖x‖ ^ 2)) : ContDiffAt ℝ n (o.circularFlow ρ) x :=
  (hρ.comp x (contDiff_norm_sq ℝ).contDiffAt).smul
    (o.rightAngleRotation.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt)

/-- The derivative of a circular flow: `Du(x) h = ρ(‖x‖²) J h + 2 ρ'(‖x‖²) ⟪x, h⟫ J x`. -/
theorem hasFDerivAt_circularFlow {ρ : ℝ → ℝ} {ρ' : ℝ} {x : E}
    (hρ : HasDerivAt ρ ρ' (‖x‖ ^ 2)) :
    HasFDerivAt (o.circularFlow ρ)
      (ρ (‖x‖ ^ 2) • (o.rightAngleRotation.toContinuousLinearEquiv : E →L[ℝ] E) +
        (innerSL ℝ ((2 * ρ') • x)).smulRight (J x)) x := by
  have hc := hρ.comp_hasFDerivAt x ((hasFDerivAt_id x).norm_sq)
  refine (hc.smul
    (o.rightAngleRotation.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt)).congr_fderiv
    ?_
  ext h
  simp [mul_comm, mul_left_comm]

/-- The derivative of a circular flow in the direction `h`. -/
theorem fderiv_circularFlow_apply {ρ : ℝ → ℝ} {x : E} (hρ : DifferentiableAt ℝ ρ (‖x‖ ^ 2))
    (h : E) :
    fderiv ℝ (o.circularFlow ρ) x h =
      ρ (‖x‖ ^ 2) • J h + (2 * deriv ρ (‖x‖ ^ 2) * ⟪x, h⟫) • J x := by
  rw [(o.hasFDerivAt_circularFlow hρ.hasDerivAt).fderiv]
  simp

/-- A circular flow is divergence free: `tr (Du(x)) = 0`. -/
theorem trace_fderiv_circularFlow {ρ : ℝ → ℝ} {x : E} (hρ : DifferentiableAt ℝ ρ (‖x‖ ^ 2)) :
    LinearMap.trace ℝ E (fderiv ℝ (o.circularFlow ρ) x) = 0 := by
  set b := stdOrthonormalBasis ℝ E
  have hterm (i : Fin (Module.finrank ℝ E)) :
      ⟪b i, (fderiv ℝ (o.circularFlow ρ) x : E →ₗ[ℝ] E) (b i)⟫ =
        2 * deriv ρ (‖x‖ ^ 2) * (⟪x, b i⟫ * ⟪b i, J x⟫) := by
    rw [ContinuousLinearMap.coe_coe, o.fderiv_circularFlow_apply hρ, inner_add_right,
      real_inner_smul_right, real_inner_smul_right, inner_rightAngleRotation_right,
      areaForm_apply_self]
    ring
  rw [LinearMap.trace_eq_sum_inner _ b]
  simp_rw [hterm, ← Finset.mul_sum, b.sum_inner_mul_inner, inner_rightAngleRotation_right,
    areaForm_apply_self, neg_zero, mul_zero]

/-- A circular flow with a `C¹` profile is solenoidal on the whole plane, for every additive Haar
measure. -/
theorem isSolenoidalOn_circularFlow [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.IsAddHaarMeasure] {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 1 ρ) :
    IsSolenoidalOn μ ⊤ (o.circularFlow ρ) :=
  (contDiff_circularFlow hρ).contDiffOn.isSolenoidalOn_iff.mpr fun _ _ ↦
    o.trace_fderiv_circularFlow (hρ.differentiable one_ne_zero _)

/-- The convective term of a circular flow is its centripetal acceleration:
`(u · ∇) u (x) = Du(x) (u(x)) = -ρ(‖x‖²)² x`. -/
theorem fderiv_circularFlow_apply_self {ρ : ℝ → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ (‖x‖ ^ 2)) :
    fderiv ℝ (o.circularFlow ρ) x (o.circularFlow ρ x) = -(ρ (‖x‖ ^ 2) ^ 2 • x) := by
  rw [o.fderiv_circularFlow_apply hρ, circularFlow_apply, real_inner_smul_right,
    inner_rightAngleRotation_right, areaForm_apply_self, map_smul,
    rightAngleRotation_rightAngleRotation, smul_smul]
  simp [sq]

/-- **Circular flows are stationary Euler flows.** The centripetal acceleration of a circular flow
is balanced by the gradient of the circular pressure: `(u · ∇) u + ∇p = 0`. -/
theorem fderiv_circularFlow_apply_self_add_gradient_circularPressure {ρ : ℝ → ℝ} {x : E}
    (hρ : Continuous ρ) (hρx : DifferentiableAt ℝ ρ (‖x‖ ^ 2)) :
    fderiv ℝ (o.circularFlow ρ) x (o.circularFlow ρ x) + ∇ (circularPressure ρ) x = 0 := by
  rw [o.fderiv_circularFlow_apply_self hρx, (hasGradientAt_circularPressure hρ x).gradient,
    neg_add_cancel]

/-- **The vorticity of a circular flow.** The antisymmetric part of the derivative of a circular
flow is `Du(x) - Du(x)† = 2 B'(‖x‖²) J` with `B(s) = s ρ(s)`: the scalar vorticity is
`ω(x) = 2 B'(‖x‖²) = 2 ρ(‖x‖²) + 2 ‖x‖² ρ'(‖x‖²)`. -/
theorem fderiv_circularFlow_sub_adjoint {ρ : ℝ → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ (‖x‖ ^ 2)) :
    fderiv ℝ (o.circularFlow ρ) x - ContinuousLinearMap.adjoint (fderiv ℝ (o.circularFlow ρ) x) =
      (2 * deriv (fun s ↦ s * ρ s) (‖x‖ ^ 2)) •
        (o.rightAngleRotation.toContinuousLinearEquiv : E →L[ℝ] E) := by
  have hB : deriv (fun s ↦ s * ρ s) (‖x‖ ^ 2) = ρ (‖x‖ ^ 2) + ‖x‖ ^ 2 * deriv ρ (‖x‖ ^ 2) := by
    rw [((hasDerivAt_id' (‖x‖ ^ 2)).fun_mul hρ.hasDerivAt).deriv, one_mul]
  refine ContinuousLinearMap.ext fun h ↦ ext_inner_right ℝ fun k ↦ ?_
  rw [sub_apply, inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
    o.fderiv_circularFlow_apply hρ, o.fderiv_circularFlow_apply hρ, hB]
  simp only [smul_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, inner_rightAngleRotation_left,
    inner_rightAngleRotation_right]
  have h2 := o.inner_mul_areaForm_sub x h k
  rw [o.areaForm_swap h x]
  linear_combination 2 * deriv ρ (‖x‖ ^ 2) * h2

/-- **The Laplacian of a circular flow.** With `B(s) = s ρ(s)`,
`Δu(x) = 4 B''(‖x‖²) J x = (8 ρ'(‖x‖²) + 4 ‖x‖² ρ''(‖x‖²)) J x`. -/
theorem laplacian_circularFlow {ρ : ℝ → ℝ} {x : E} (hρ : ContDiffAt ℝ 2 ρ (‖x‖ ^ 2)) :
    Δ (o.circularFlow ρ) x = (4 * deriv (deriv fun s ↦ s * ρ s) (‖x‖ ^ 2)) • J x := by
  -- The second derivative of the circulation function `B(s) = s ρ(s)` is `2 ρ' + s ρ''`.
  have hB : deriv (deriv fun r ↦ r * ρ r) (‖x‖ ^ 2) =
      2 * deriv ρ (‖x‖ ^ 2) + ‖x‖ ^ 2 * deriv (deriv ρ) (‖x‖ ^ 2) := by
    have heq : deriv (fun r ↦ r * ρ r) =ᶠ[nhds (‖x‖ ^ 2)] fun r ↦ ρ r + r * deriv ρ r :=
      (hρ.eventually_differentiableAt (by norm_num)).mono fun r hr ↦ by
        rw [((hasDerivAt_id' r).fun_mul hr.hasDerivAt).deriv, one_mul]
    rw [heq.deriv_eq, ((hρ.differentiableAt (by norm_num)).hasDerivAt.fun_add
      ((hasDerivAt_id' _).fun_mul hρ.differentiableAt_deriv_two.hasDerivAt)).deriv]
    ring
  set Jc : E →L[ℝ] E := (o.rightAngleRotation.toContinuousLinearEquiv : E →L[ℝ] E)
  have hf : ContDiffAt ℝ 2 (fun y : E ↦ ρ (‖y‖ ^ 2)) x :=
    hρ.comp x (contDiff_norm_sq ℝ).contDiffAt
  have hgradf : ∇ (fun y : E ↦ ρ (‖y‖ ^ 2)) x = (2 * deriv ρ (‖x‖ ^ 2)) • x := by
    refine HasGradientAt.gradient ?_
    rw [hasGradientAt_iff_hasFDerivAt]
    refine ((hρ.differentiableAt (by norm_num)).hasDerivAt.comp_hasFDerivAt x
      ((hasFDerivAt_id x).norm_sq)).congr_fderiv ?_
    ext h
    simp [mul_comm, mul_left_comm]
  refine ext_inner_left ℝ fun e ↦ ?_
  set g : E →L[ℝ] ℝ := (innerSL ℝ e).comp Jc
  have hcomp : Δ ((innerSL ℝ e) ∘ o.circularFlow ρ) x = ⟪e, Δ (o.circularFlow ρ) x⟫ := by
    rw [(contDiffAt_circularFlow hρ).laplacian_CLM_comp_left]
    rfl
  have hfun : ((innerSL ℝ e) ∘ o.circularFlow ρ) = fun y ↦ ρ (‖y‖ ^ 2) * g y := by
    funext y
    simp [g, Jc, circularFlow_apply, real_inner_smul_right]
  have hΔg : Δ (g : E → ℝ) x = 0 := congrFun g.laplacian x
  have hgrad : ⟪∇ (fun y : E ↦ ρ (‖y‖ ^ 2)) x, ∇ (g : E → ℝ) x⟫ =
      2 * deriv ρ (‖x‖ ^ 2) * ⟪e, J x⟫ := by
    rw [real_inner_comm, inner_gradient_left, g.fderiv, hgradf, map_smul]
    simp [g, Jc, smul_eq_mul]
  rw [← hcomp, hfun, hf.laplacian_fun_mul g.contDiff.contDiffAt, hΔg, hgrad,
    hρ.laplacian_comp_norm_sq, hB, real_inner_smul_right,
    (Fact.out : Module.finrank ℝ E = 2)]
  simp only [g, Jc, ContinuousLinearMap.coe_comp, Function.comp_apply, innerSL_apply_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  push_cast
  ring

end Orientation

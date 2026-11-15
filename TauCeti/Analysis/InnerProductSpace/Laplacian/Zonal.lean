/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The Laplacian of homogeneous zonal functions

Fix a unit vector `e` of a finite-dimensional real inner product space `E` of dimension `n`, and
write `t = ⟪e, x⟫ / ‖x‖` for the cosine of the angle between `x ≠ 0` and `e`. A function

`x ↦ ‖x‖ ^ μ * F (⟪e, x⟫ / ‖x‖)`

is positively homogeneous of degree `μ` and, on each sphere about the origin, depends only on the
angle with `e`. Away from the origin its Laplacian is

`Δ (‖x‖ ^ μ F(t)) = ‖x‖ ^ (μ - 2) (μ (μ + n - 2) F(t) + (1 - t²) F''(t) - (n - 1) t F'(t))`.

The first term is the Laplacian of the radial factor `‖x‖ ^ μ`; the other two are the
Laplace–Beltrami operator of the unit sphere applied to the zonal function `F(t)`. No mixed term
appears, because the gradient of the radial factor is parallel to `x` while the gradient of the
angular factor `t` is orthogonal to `x`. Only the regularity of `F` at the value `t` is used.

Since radial and angular variables separate, a choice of `F` making the bracket nonpositive for
`t` in an interval `[-1, c]` gives a function superharmonic on the cone
`{x | ⟪e, x⟫ < c ‖x‖}`. This is how barriers are built at boundary points satisfying an exterior
cone condition.

## Main declarations

* `TauCeti.hasGradientAt_inner_div_norm`: the gradient of `x ↦ ⟪e, x⟫ / ‖x‖` away from the
  origin, `‖x‖⁻¹ e - (⟪e, x⟫ / ‖x‖³) x`.
* `TauCeti.inner_gradient_inner_div_norm_self`, `TauCeti.norm_sq_gradient_inner_div_norm`: this
  gradient is orthogonal to `x`, and for a unit vector `e` its squared norm is `(1 - t²) / ‖x‖²`.
* `TauCeti.laplacian_inner_div_norm`: its Laplacian, `-(n - 1) ⟪e, x⟫ / ‖x‖³`.
* `TauCeti.laplacian_norm_rpow_mul_comp_inner_div_norm`: the Laplacian of `‖x‖ ^ μ F(t)`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 2.8 and the problems of Chapter 2 (barriers of the form `r ^ μ f(θ)` at a cone
  vertex).
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian Filter Topology
open scoped RealInnerProductSpace Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {e x : E}

/-- The quotient `⟪e, x⟫ / ‖x‖` is the dipole-type product `⟪e, x⟫ ‖x‖ ^ (-1)`. -/
private theorem inner_div_norm_eq_inner_mul_norm_rpow (e : E) :
    (fun y : E ↦ ⟪e, y⟫_ℝ / ‖y‖) = fun y ↦ ⟪e, y⟫_ℝ * ‖y‖ ^ (-1 : ℝ) := by
  funext y
  rw [Real.rpow_neg_one, div_eq_mul_inv]

omit [InnerProductSpace ℝ E] in
private theorem norm_rpow_neg_one_sub_two (x : E) : ‖x‖ ^ ((-1 : ℝ) - 2) = (‖x‖ ^ 3)⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_neg (norm_nonneg _)]
  norm_num

/-- Away from the origin, the gradient of `x ↦ ⟪e, x⟫ / ‖x‖` is
`‖x‖⁻¹ e - (⟪e, x⟫ / ‖x‖ ^ 3) x`. -/
theorem hasGradientAt_inner_div_norm [CompleteSpace E] (e : E) (hx : x ≠ 0) :
    HasGradientAt (fun y : E ↦ ⟪e, y⟫_ℝ / ‖y‖) (‖x‖⁻¹ • e - (⟪e, x⟫_ℝ / ‖x‖ ^ 3) • x) x := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have h1 : HasFDerivAt (fun y : E ↦ ⟪e, y⟫_ℝ) (innerSL ℝ e) x := (innerSL ℝ e).hasFDerivAt
  have h := h1.fun_mul (hasFDerivAt_norm_rpow_of_ne (-1) hx)
  rw [hasGradientAt_iff_hasFDerivAt, inner_div_norm_eq_inner_mul_norm_rpow]
  convert h using 1
  ext v
  simp only [toDual_apply_apply, inner_sub_left, inner_smul_left, conj_trivial,
    add_apply, smul_apply, innerSL_apply_apply,
    smul_eq_mul, norm_rpow_neg_one_sub_two, Real.rpow_neg_one]
  field_simp
  ring

/-- The gradient of `x ↦ ⟪e, x⟫ / ‖x‖` is orthogonal to `x`, since the function is constant on
rays from the origin. -/
theorem inner_gradient_inner_div_norm_self [CompleteSpace E] (e : E) (hx : x ≠ 0) :
    ⟪∇ (fun y : E ↦ ⟪e, y⟫_ℝ / ‖y‖) x, x⟫_ℝ = 0 := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  simp only [(hasGradientAt_inner_div_norm e hx).gradient, inner_sub_left, inner_smul_left,
    real_inner_self_eq_norm_sq, conj_trivial]
  field_simp
  ring

/-- For a unit vector `e`, the squared norm of the gradient of `x ↦ ⟪e, x⟫ / ‖x‖` is
`(1 - t²) / ‖x‖²` with `t = ⟪e, x⟫ / ‖x‖`. -/
theorem norm_sq_gradient_inner_div_norm [CompleteSpace E] (he : ‖e‖ = 1) (hx : x ≠ 0) :
    ‖∇ (fun y : E ↦ ⟪e, y⟫_ℝ / ‖y‖) x‖ ^ 2 = (1 - (⟪e, x⟫_ℝ / ‖x‖) ^ 2) / ‖x‖ ^ 2 := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  rw [(hasGradientAt_inner_div_norm e hx).gradient, ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, he, real_inner_comm e x, conj_trivial]
  field_simp
  ring

variable [FiniteDimensional ℝ E]

/-- Away from the origin, the Laplacian of `x ↦ ⟪e, x⟫ / ‖x‖` is
`-(dim E - 1) ⟪e, x⟫ / ‖x‖ ^ 3`. -/
theorem laplacian_inner_div_norm (e : E) (hx : x ≠ 0) :
    Δ (fun y : E ↦ ⟪e, y⟫_ℝ / ‖y‖) x = -(Module.finrank ℝ E - 1) * ⟪e, x⟫_ℝ / ‖x‖ ^ 3 := by
  rw [inner_div_norm_eq_inner_mul_norm_rpow, laplacian_inner_mul_norm_rpow_of_ne e (-1) hx,
    norm_rpow_neg_one_sub_two]
  ring

/-- **The Laplacian of a homogeneous zonal function.** Let `e` be a unit vector and `x ≠ 0`, and
put `t = ⟪e, x⟫ / ‖x‖`. If `F` is `C²` at `t`, then

`Δ (‖x‖ ^ μ F(t)) = ‖x‖ ^ (μ - 2) (μ (μ + n - 2) F(t) + (1 - t²) F''(t) - (n - 1) t F'(t))`,

where `n = dim E`. -/
theorem laplacian_norm_rpow_mul_comp_inner_div_norm {F : ℝ → ℝ} (he : ‖e‖ = 1) (hx : x ≠ 0)
    (μ : ℝ) (hF : ContDiffAt ℝ 2 F (⟪e, x⟫_ℝ / ‖x‖)) :
    Δ (fun y : E ↦ ‖y‖ ^ μ * F (⟪e, y⟫_ℝ / ‖y‖)) x =
      ‖x‖ ^ (μ - 2) * (μ * (μ + Module.finrank ℝ E - 2) * F (⟪e, x⟫_ℝ / ‖x‖) +
        (1 - (⟪e, x⟫_ℝ / ‖x‖) ^ 2) * deriv (deriv F) (⟪e, x⟫_ℝ / ‖x‖) -
        (Module.finrank ℝ E - 1) * (⟪e, x⟫_ℝ / ‖x‖) * deriv F (⟪e, x⟫_ℝ / ‖x‖)) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hnorm : ContDiffAt ℝ 2 (fun y : E ↦ ‖y‖) x := contDiffAt_norm ℝ hx
  have hq : ContDiffAt ℝ 2 (fun y : E ↦ ⟪e, y⟫_ℝ / ‖y‖) x :=
    (innerSL ℝ e).contDiff.contDiffAt.div hnorm hr.ne'
  have hp : ContDiffAt ℝ 2 (fun y : E ↦ ‖y‖ ^ μ) x := hnorm.rpow_const_of_ne hr.ne'
  have hFq : ContDiffAt ℝ 2 (F ∘ fun y : E ↦ ⟪e, y⟫_ℝ / ‖y‖) x := hF.comp x hq
  have hgq := hasGradientAt_inner_div_norm e hx
  -- The mixed term vanishes: `∇ ‖x‖ ^ μ` is parallel to `x`, and `∇ t` is orthogonal to `x`.
  have hgp : ∇ (fun y : E ↦ ‖y‖ ^ μ) x = (μ * ‖x‖ ^ (μ - 2)) • x := by
    refine (hasGradientAt_iff_hasFDerivAt.2 ?_).gradient
    convert hasFDerivAt_norm_rpow_of_ne μ hx using 1
    ext v
    simp
  have hfd : fderiv ℝ (F ∘ fun y : E ↦ ⟪e, y⟫_ℝ / ‖y‖) x =
      deriv F (⟪e, x⟫_ℝ / ‖x‖) • toDual ℝ E (‖x‖⁻¹ • e - (⟪e, x⟫_ℝ / ‖x‖ ^ 3) • x) :=
    ((hF.differentiableAt (by norm_num)).hasDerivAt.comp_hasFDerivAt x
      hgq.hasFDerivAt).fderiv
  have hmixed :
      ⟪∇ (fun y : E ↦ ‖y‖ ^ μ) x, ∇ (F ∘ fun y : E ↦ ⟪e, y⟫_ℝ / ‖y‖) x⟫_ℝ = 0 := by
    rw [inner_gradient_right, conj_trivial, hfd, hgp]
    simp only [smul_apply, toDual_apply_apply, inner_smul_right, smul_eq_mul]
    rw [← hgq.gradient, inner_gradient_inner_div_norm_self e hx, mul_zero, mul_zero]
  have hpow : ‖x‖ ^ μ = ‖x‖ ^ (μ - 2) * ‖x‖ ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hr]
    norm_num
  -- The Leibniz rule, then the chain rule for the angular factor.
  calc Δ (fun y : E ↦ ‖y‖ ^ μ * F (⟪e, y⟫_ℝ / ‖y‖)) x
      = Δ (fun y : E ↦ ‖y‖ ^ μ * (F ∘ fun y : E ↦ ⟪e, y⟫_ℝ / ‖y‖) y) x := rfl
    _ = _ := hp.laplacian_fun_mul hFq
    _ = _ := by
      rw [hmixed, ContDiffAt.laplacian_comp (q := fun y : E ↦ ⟪e, y⟫_ℝ / ‖y‖) hF hq,
        norm_sq_gradient_inner_div_norm he hx, laplacian_inner_div_norm e hx,
        laplacian_norm_rpow_of_ne μ hx, hpow]
      simp only [Function.comp_apply]
      field_simp
      ring

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The Laplacian of zonal functions

Fix a unit vector `v` of a finite-dimensional real inner product space `E` of dimension `n`, and
write `s(x) = ⟪v, x⟫ / ‖x‖` for the cosine of the angle between `x ≠ 0` and `v`. A function of
the form `x ↦ ‖x‖ ^ μ F(s(x))` is the product of a radial power and a *zonal* function on the
unit sphere, one depending only on the angle with the axis `v`. Its Laplacian separates:

`Δ (‖x‖ ^ μ F(s)) = ‖x‖ ^ (μ - 2) (μ (μ + n - 2) F(s) + (1 - s²) F''(s) - (n - 1) s F'(s))`,

where `(1 - s²) F'' - (n - 1) s F'` is the spherical Laplacian of the zonal function. The proof
combines the Leibniz rule for the Laplacian with the facts that `s` has squared gradient
`(1 - s²) / ‖x‖²` and Laplacian `-(n - 1) s / ‖x‖²`, and that its gradient is orthogonal to `x`
since `s` is homogeneous of degree zero. Functions of this form are the barriers of potential
theory at the vertex of a cone, and, for `F` a Gegenbauer polynomial, the solid zonal harmonics.

## Main declarations

* `TauCeti.hasGradientAt_inner_div_norm`, `TauCeti.norm_gradient_inner_div_norm_sq`,
  `TauCeti.laplacian_inner_div_norm`: the gradient and the Laplacian of `s`.
* `TauCeti.laplacian_norm_rpow_mul_comp_inner_div_norm`: the Laplacian of `‖x‖ ^ μ F(s)`.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian
open scoped RealInnerProductSpace Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Gradient

variable [CompleteSpace E]

/-- Away from the origin, the function `x ↦ ⟪v, x⟫ / ‖x‖` has gradient
`‖x‖⁻¹ v - ⟪v, x⟫ ‖x‖⁻³ x`. -/
theorem hasGradientAt_inner_div_norm (v : E) {x : E} (hx : x ≠ 0) :
    HasGradientAt (fun y : E ↦ ⟪v, y⟫_ℝ / ‖y‖)
      (‖x‖⁻¹ • v - (⟪v, x⟫_ℝ / ‖x‖ ^ 3) • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := (innerSL ℝ v).hasFDerivAt.mul (hasFDerivAt_norm_rpow_of_ne (-1) hx)
  have hfun : (fun y : E ↦ ⟪v, y⟫_ℝ / ‖y‖) = fun y ↦ innerSL ℝ v y * ‖y‖ ^ (-1 : ℝ) := by
    funext y
    rw [Real.rpow_neg_one, div_eq_mul_inv, innerSL_apply_apply]
  rw [hfun]
  convert h using 1
  ext w
  have hr : ‖x‖ ^ (-1 - 2 : ℝ) = (‖x‖ ^ 3)⁻¹ := by
    rw [show (-1 - 2 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg (norm_nonneg _),
      Real.rpow_natCast]
  simp only [toDual_apply_apply, inner_sub_left, inner_smul_left, conj_trivial,
    add_apply, smul_apply, innerSL_apply_apply,
    smul_eq_mul, hr, Real.rpow_neg_one]
  ring

/-- For a unit vector `v` and `x ≠ 0`, the squared gradient of `s = ⟪v, x⟫ / ‖x‖` is
`(1 - s²) / ‖x‖²`. -/
theorem norm_gradient_inner_div_norm_sq {v : E} (hv : ‖v‖ = 1) {x : E} (hx : x ≠ 0) :
    ‖∇ (fun y : E ↦ ⟪v, y⟫_ℝ / ‖y‖) x‖ ^ 2 = (1 - (⟪v, x⟫_ℝ / ‖x‖) ^ 2) / ‖x‖ ^ 2 := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  rw [(hasGradientAt_inner_div_norm v hx).gradient, norm_sub_sq_real, norm_smul, norm_smul,
    inner_smul_left, inner_smul_right, hv, real_inner_comm x v]
  simp only [norm_inv, Real.norm_eq_abs, abs_norm, mul_pow, sq_abs, div_pow, inv_pow,
    conj_trivial]
  field_simp
  ring

/-- The function `x ↦ ⟪v, x⟫ / ‖x‖` is homogeneous of degree zero, so its derivative at
`x ≠ 0` vanishes in the radial direction `x`. -/
theorem fderiv_inner_div_norm_apply_self (v : E) {x : E} (hx : x ≠ 0) :
    fderiv ℝ (fun y : E ↦ ⟪v, y⟫_ℝ / ‖y‖) x x = 0 := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  rw [← inner_gradient_left, (hasGradientAt_inner_div_norm v hx).gradient, inner_sub_left,
    inner_smul_left, inner_smul_left, real_inner_self_eq_norm_sq, real_inner_comm x v]
  simp only [conj_trivial]
  field_simp
  ring

end Gradient

variable [FiniteDimensional ℝ E]

/-- Away from the origin, `s = ⟪v, x⟫ / ‖x‖` has Laplacian `-(n - 1) s / ‖x‖²`, `n = dim E`. -/
theorem laplacian_inner_div_norm (v : E) {x : E} (hx : x ≠ 0) :
    Δ (fun y : E ↦ ⟪v, y⟫_ℝ / ‖y‖) x =
      -((Module.finrank ℝ E - 1) * (⟪v, x⟫_ℝ / ‖x‖) / ‖x‖ ^ 2) := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hfun : (fun y : E ↦ ⟪v, y⟫_ℝ / ‖y‖) = fun y ↦ ⟪v, y⟫_ℝ * ‖y‖ ^ (-1 : ℝ) := by
    funext y
    rw [Real.rpow_neg_one, div_eq_mul_inv]
  rw [hfun, laplacian_inner_mul_norm_rpow_of_ne v (-1) hx,
    show (-1 - 2 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg (norm_nonneg _),
    Real.rpow_natCast]
  field_simp
  ring

/-- **The Laplacian of a zonal function.** For a unit vector `v` and `x ≠ 0`, write
`s = ⟪v, x⟫ / ‖x‖` for the cosine of the angle between `x` and `v`, and `n = dim E`. For a real
function `F`, twice differentiable at `s`, the function `‖x‖ ^ μ F(s)` has Laplacian
`‖x‖ ^ (μ - 2) (μ (μ + n - 2) F(s) + (1 - s²) F''(s) - (n - 1) s F'(s))` at `x`. The last two
terms are the spherical Laplacian of the zonal function `F(s)`. -/
theorem laplacian_norm_rpow_mul_comp_inner_div_norm {v : E} (hv : ‖v‖ = 1) (μ : ℝ)
    {F : ℝ → ℝ} {x : E} (hx : x ≠ 0) (hF : ContDiffAt ℝ 2 F (⟪v, x⟫_ℝ / ‖x‖)) :
    Δ (fun y : E ↦ ‖y‖ ^ μ * F (⟪v, y⟫_ℝ / ‖y‖)) x =
      ‖x‖ ^ (μ - 2) * (μ * (μ + Module.finrank ℝ E - 2) * F (⟪v, x⟫_ℝ / ‖x‖) +
        (1 - (⟪v, x⟫_ℝ / ‖x‖) ^ 2) * deriv (deriv F) (⟪v, x⟫_ℝ / ‖x‖) -
        (Module.finrank ℝ E - 1) * (⟪v, x⟫_ℝ / ‖x‖) * deriv F (⟪v, x⟫_ℝ / ‖x‖)) := by
  set s : E → ℝ := fun y ↦ ⟪v, y⟫_ℝ / ‖y‖
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hs : ContDiffAt ℝ 2 s x :=
    (innerSL ℝ v).contDiff.contDiffAt.div (contDiffAt_norm ℝ hx) hr.ne'
  have hf : ContDiffAt ℝ 2 (fun y : E ↦ ‖y‖ ^ μ) x :=
    (contDiffAt_norm ℝ hx).rpow_const_of_ne hr.ne'
  replace hF : ContDiffAt ℝ 2 F (s x) := hF
  have hg : ContDiffAt ℝ 2 (F ∘ s) x := hF.comp x hs
  have hmul := hf.laplacian_fun_mul hg
  -- The radial and angular factors have orthogonal gradients, by homogeneity of `s`.
  have hcross : ⟪∇ (fun y : E ↦ ‖y‖ ^ μ) x, ∇ (F ∘ s) x⟫_ℝ = 0 := by
    have hgd : HasFDerivAt (F ∘ s) (deriv F (s x) • fderiv ℝ s x) x :=
      (hF.differentiableAt (by norm_num)).hasDerivAt.comp_hasFDerivAt x
        (hs.differentiableAt (by norm_num)).hasFDerivAt
    rw [inner_gradient_left, fderiv_norm_rpow_of_ne μ hx, smul_apply,
      innerSL_apply_apply, real_inner_comm, inner_gradient_left]
    rw [hgd.fderiv, smul_apply, fderiv_inner_div_norm_apply_self v hx]
    simp
  rw [show (fun y : E ↦ ‖y‖ ^ μ * F (s y)) = fun y ↦ ‖y‖ ^ μ * (F ∘ s) y from rfl, hmul, hcross,
    laplacian_norm_rpow_of_ne μ hx, hF.laplacian_comp hs,
    norm_gradient_inner_div_norm_sq hv hx, laplacian_inner_div_norm v hx]
  rw [Real.rpow_sub hr, Real.rpow_two, Function.comp_apply]
  simp only [s]
  field_simp
  ring

end TauCeti

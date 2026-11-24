/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Bessel.J
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import TauCeti.Analysis.Bochner.Gaussian.Basic
import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The Airy double integral against a Gaussian as a `J₀` integral

By the Fourier integral `Ai(x) = (2π)⁻¹ ∫ e^{i(u³/3 + x u)} du`, the square `Ai(x)²` is formally
the double integral `(2π)⁻² ∫∫ e^{i((u³ + v³)/3 + x(u + v))} du dv`. Neither this double integral
nor the `J₀` integral of DLMF 9.11.3,

`Ai(x)² = (4π√3)⁻¹ ∫₀^∞ J₀(t³/12 + x t) t dt`,

converges absolutely. They can be compared after inserting the Gaussian factor
`e^{-ε(a² + b²)}` in the coordinates `a = u + v`, `b = √3 (u - v)`, and letting `ε → 0+`.

This file proves the identity for each `ε > 0`. In the coordinates `(a, b)` the phase is
`(u³ + v³)/3 + x(u + v) = a((a² + b²)/12 + x)`, the Gaussian factor is `e^{-4ε(u² - uv + v²)}`
and the Jacobian is `2√3`. The phase is then a plane wave in the direction `a` whose frequency
depends only on the radius `t = √(a² + b²)`, so polar coordinates and Bessel's integral for `J₀`
(`Complex.integral_exp_re_mul_mul_I_mul_eq_integral_besselJ`) give

`∫∫ e^{i((u³ + v³)/3 + x(u + v))} e^{-4ε(u² - uv + v²)} du dv
  = (π/√3) ∫₀^∞ J₀(t³/12 + x t) e^{-εt²} t dt`.

Multiplied by `(2π)⁻²`, the right side is the right side of DLMF 9.11.3 with the factor `e^{-εt²}`.

## Main results

* `TauCeti.integrable_exp_cube_add_cube_mul_exp_neg`: the regularized integrand is integrable on
  the plane.
* `TauCeti.integral_exp_cube_add_cube_mul_exp_neg_eq_integral_besselJ`: the identity above.

## References

* NIST Digital Library of Mathematical Functions, §9.11(ii), <https://dlmf.nist.gov/9.11>.
-/

public section

noncomputable section

open MeasureTheory Set Complex
open scoped Real

namespace TauCeti

/-- The linear substitution `(u, v) ↦ (u + v, √3 (u - v))`, which turns the Airy phase
`(u³ + v³)/3 + x(u + v)` into `a((a² + b²)/12 + x)`. -/
private def airyProductSubst : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (√3 • (ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ))

private theorem airyProductSubst_apply (p : ℝ × ℝ) :
    airyProductSubst p = (p.1 + p.2, √3 * (p.1 - p.2)) := by
  simp [airyProductSubst]

private theorem det_airyProductSubst : airyProductSubst.det = -(2 * √3) := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ),
    Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, airyProductSubst_apply]
  ring

private theorem isUnit_airyProductSubst : IsUnit airyProductSubst := by
  have hdet := det_airyProductSubst
  rw [ContinuousLinearMap.det] at hdet
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_isUnit_det, hdet]
  exact isUnit_iff_ne_zero.2 (neg_ne_zero.2 (by positivity))

/-- The integrand in polar form: the radial plane wave `e^{i Re z (|z|²/12 + x)}` against the
Gaussian `e^{-ε|z|²}` is integrable on `ℂ`. -/
private theorem integrable_exp_re_mul_mul_I_mul_exp_neg {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    Integrable fun z : ℂ => exp (z.re * ((‖z‖ ^ 2 / 12 + x : ℝ) : ℂ) * I) *
      (Real.exp (-(ε * ‖z‖ ^ 2)) : ℂ) := by
  refine (integrable_cexp_neg_mul_sq_norm (V := ℂ) hε).mono (by fun_prop)
    (ae_of_all _ fun z => le_of_eq ?_)
  rw [norm_mul, ← ofReal_mul, norm_exp_ofReal_mul_I, one_mul, ofReal_exp, ofReal_neg]

/-- The Airy double integrand `e^{i((u³ + v³)/3 + x(u + v))}`, regularized by the Gaussian
`e^{-4ε(u² - uv + v²)}`, is integrable on the plane for every `ε > 0`. -/
theorem integrable_exp_cube_add_cube_mul_exp_neg (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Integrable fun p : ℝ × ℝ =>
      exp ((((p.1 ^ 3 + p.2 ^ 3) / 3 + x * (p.1 + p.2) : ℝ) : ℂ) * I) *
        (Real.exp (-(4 * ε * (p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2))) : ℂ) := by
  have hg : Integrable fun u : ℝ => Real.exp (-(2 * ε) * u ^ 2) :=
    integrable_exp_neg_mul_sq (by positivity)
  refine (hg.mul_prod hg).ofReal (𝕜 := ℂ) |>.mono (by fun_prop) (ae_of_all _ fun p => ?_)
  simp only [norm_mul, norm_exp_ofReal_mul_I, one_mul, norm_real, RCLike.norm_ofReal,
    Real.norm_eq_abs, Real.abs_exp, ← Real.exp_add, Real.exp_le_exp]
  -- `u² - uv + v² ≥ (u² + v²)/2`, since the difference is `(u - v)²/2`.
  nlinarith [sq_nonneg (p.1 - p.2), hε]

/-- The identity in the coordinates `(a, b)`: the plane wave `e^{i a((a² + b²)/12 + x)}` against
the Gaussian `e^{-ε(a² + b²)}` integrates to `2π ∫₀^∞ J₀(t³/12 + x t) e^{-εt²} t dt`. -/
private theorem integral_exp_fst_mul_exp_neg_eq_integral_besselJ (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ q : ℝ × ℝ, exp (((q.1 * ((q.1 ^ 2 + q.2 ^ 2) / 12 + x) : ℝ) : ℂ) * I) *
        (Real.exp (-(ε * (q.1 ^ 2 + q.2 ^ 2))) : ℂ) =
      2 * π * ∫ t in Ioi (0 : ℝ),
        t • (besselJ 0 ((t ^ 3 / 12 + x * t : ℝ) : ℂ) * (Real.exp (-(ε * t ^ 2)) : ℂ)) := by
  calc _ = ∫ z : ℂ, exp (z.re * ((‖z‖ ^ 2 / 12 + x : ℝ) : ℂ) * I) *
        (Real.exp (-(ε * ‖z‖ ^ 2)) : ℂ) := by
        -- The plane `ℝ × ℝ` as `ℂ`, where `a² + b² = |z|²`.
        rw [← volume_preserving_equiv_real_prod.integral_comp
          measurableEquivRealProd.measurableEmbedding]
        congr 1 with z
        have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
          rw [Complex.sq_norm, normSq_apply]
          ring
        simp only [measurableEquivRealProd_apply, hn]
        push_cast
        ring_nf
    _ = 2 * π * ∫ r in Ioi (0 : ℝ),
        r • (besselJ 0 (r * ((r ^ 2 / 12 + x : ℝ) : ℂ)) * (Real.exp (-(ε * r ^ 2)) : ℂ)) :=
      integral_exp_re_mul_mul_I_mul_eq_integral_besselJ (k := fun r => ((r ^ 2 / 12 + x : ℝ) : ℂ))
        (h := fun r => (Real.exp (-(ε * r ^ 2)) : ℂ)) (integrable_exp_re_mul_mul_I_mul_exp_neg hε x)
    _ = _ := by
      congr 1
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      simp only
      congr 3
      push_cast
      ring

/-- **The Airy double integral against a Gaussian.** For real `x` and `ε > 0`,
`∫∫ e^{i((u³ + v³)/3 + x(u + v))} e^{-4ε(u² - uv + v²)} du dv
  = (π/√3) ∫₀^∞ J₀(t³/12 + x t) e^{-εt²} t dt`.
Multiplied by `(2π)⁻²`, this is DLMF 9.11.3 regularized by the Gaussian
`e^{-ε(a² + b²)}` in the coordinates `a = u + v`, `b = √3 (u - v)`. -/
theorem integral_exp_cube_add_cube_mul_exp_neg_eq_integral_besselJ (x : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∫ p : ℝ × ℝ, exp ((((p.1 ^ 3 + p.2 ^ 3) / 3 + x * (p.1 + p.2) : ℝ) : ℂ) * I) *
        (Real.exp (-(4 * ε * (p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2))) : ℂ) =
      π / √3 * ∫ t in Ioi (0 : ℝ),
        t • (besselJ 0 ((t ^ 3 / 12 + x * t : ℝ) : ℂ) * (Real.exp (-(ε * t ^ 2)) : ℂ)) := by
  -- The integrand in the coordinates `(a, b) = (u + v, √3 (u - v))`.
  set G : ℝ × ℝ → ℂ := fun q => exp (((q.1 * ((q.1 ^ 2 + q.2 ^ 2) / 12 + x) : ℝ) : ℂ) * I) *
    (Real.exp (-(ε * (q.1 ^ 2 + q.2 ^ 2))) : ℂ) with hG
  have hsubst (p : ℝ × ℝ) :
      exp ((((p.1 ^ 3 + p.2 ^ 3) / 3 + x * (p.1 + p.2) : ℝ) : ℂ) * I) *
        (Real.exp (-(4 * ε * (p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2))) : ℂ) = G (airyProductSubst p) := by
    have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    simp only [hG, airyProductSubst_apply]
    congr 4
    · linear_combination (-(p.1 + p.2) * (p.1 - p.2) ^ 2 / 12) * h3
    · linear_combination (-(ε * (p.1 - p.2) ^ 2)) * h3
  -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  -- The Jacobian of the substitution is `|det| = 2√3`.
  have hdet := Measure.integral_eq_abs_det_smul_integral_comp volume isUnit_airyProductSubst G
  rw [det_airyProductSubst, abs_neg, abs_of_pos (by positivity)] at hdet
  simp_rw [hsubst]
  rw [eq_inv_smul_iff₀ (by positivity) |>.mpr hdet.symm, hG,
    integral_exp_fst_mul_exp_neg_eq_integral_besselJ x hε, real_smul, ← mul_assoc]
  congr 1
  push_cast
  field_simp

end TauCeti

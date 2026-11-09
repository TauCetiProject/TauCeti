/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Carlson.RG
public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Carlson.RJ
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.Analysis.SpecialFunctions.Pow.ParametricIntegral

/-!
# Slit-plane holomorphy and partial derivatives of Carlson's symmetric integrals

This file establishes separate complex differentiability, slit-plane holomorphy, and partial
derivative formulas (DLMF §19.18) for Carlson's symmetric elliptic integrals:

* `Complex.carlsonRC` in both arguments (`_left` and `_right`), including the closed-form
  difference-quotient derivatives obtained from the degenerate `R_D` identities
  `Complex.sub_mul_carlsonRD_self_left` and `Complex.two_mul_sub_mul_carlsonRD_self_right`
  (DLMF 19.20.21, 19.20.20);
* `Complex.carlsonRJ` in its first three symmetric arguments (`_first`, `_second`, `_third`),
  both in integral form and in the closed form `(R_D - R_J) / (2 (z - p))` away from `p`;
* `Complex.carlsonRD` in all three arguments (`_left`, `_middle`, `_right`), including the
  closed-form symmetric derivatives `(R_D(x, z, y) - R_D(x, y, z)) / (2 (y - z))` away from `z`;
* `Complex.carlsonRG` in all three arguments (`_left`, `_middle`, `_right`), proving
  differentiability and holomorphy even when both fixed arguments vanish, together with the
  closed-form partial derivative `R_F(x, y, z) / 4 - z R_D(x, y, z) / 12` when at most one fixed
  argument vanishes.

Together with the identity theorem on the simply connected domain `Complex.slitPlane`, separate
holomorphy upgrades real-argument identities for Carlson's integrals to the complex slit plane.

## Main results

* `Complex.hasDerivAt_carlsonRC_left`, `Complex.hasDerivAt_carlsonRC_left_of_ne`,
  `Complex.differentiableOn_carlsonRC_left`, `Complex.analyticOnNhd_carlsonRC_left` — first
  partial derivative and slit-plane holomorphy of `R_C`.
* `Complex.hasDerivAt_carlsonRC_right`, `Complex.hasDerivAt_carlsonRC_right_of_ne`,
  `Complex.differentiableOn_carlsonRC_right`, `Complex.analyticOnNhd_carlsonRC_right` — second
  partial derivative and slit-plane holomorphy of `R_C`.
* `Complex.hasDerivAt_carlsonRJ_first`, `Complex.hasDerivAt_carlsonRJ_second`,
  `Complex.hasDerivAt_carlsonRJ_third`, their `_of_ne` closed forms, and
  `Complex.differentiableOn_carlsonRJ_*`, `Complex.analyticOnNhd_carlsonRJ_*` — partial
  derivatives and slit-plane holomorphy of `R_J` in its three symmetric arguments.
* `Complex.hasDerivAt_carlsonRD_left`, `Complex.hasDerivAt_carlsonRD_middle`,
  `Complex.hasDerivAt_carlsonRD_right`, the symmetric closed forms
  `Complex.hasDerivAt_carlsonRD_left_of_ne` and `Complex.hasDerivAt_carlsonRD_middle_of_ne`, and
  `Complex.differentiableOn_carlsonRD_*`, `Complex.analyticOnNhd_carlsonRD_*` — partial
  derivatives and slit-plane holomorphy of `R_D` in all three arguments.
* `Complex.hasDerivAt_carlsonRG_left`, `Complex.hasDerivAt_carlsonRG_middle`,
  `Complex.hasDerivAt_carlsonRG_right`, their `_integral` forms allowing two zero fixed
  arguments, and `Complex.differentiableOn_carlsonRG_*`, `Complex.analyticOnNhd_carlsonRG_*` —
  partial derivatives and slit-plane holomorphy of `R_G` in all three arguments.

## References

* NIST *Digital Library of Mathematical Functions*, §19.18(i) and §19.20(iv),
  <https://dlmf.nist.gov/19.18> and <https://dlmf.nist.gov/19.20> (19.18.4–19.18.5 give the
  partial-derivative relations for the general `R`-function alongside 19.18.1 for `∂R_F/∂z` and
  19.18.2 for `(d/dx) R_G(x + a, x + b, x + c)`; 19.20.20–19.20.21 evaluate `R_D(x, y, y)` and
  `R_D(x, x, z)` in terms of `R_C`).
* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, Chapter 9.
* B. C. Carlson, Numerical computation of real or complex elliptic integrals, *Numer. Algorithms*
  10 (1995), 13–26.

B. Braams' `lean-codes` (<https://github.com/bjbraams/lean-codes>) formalizes Carlson's book on
top of Carlson's general Dirichlet-average `R`-function over a simplex. This file instead works
directly from the improper integral definitions via parametric differentiation on `slitPlane` and
is not ported from it.
-/

public section

open MeasureTheory Set Filter Topology

namespace Complex

/-! ### Partial derivatives and holomorphy of `R_C` -/

/-- **First partial derivative of `R_C`.** For `x, y ∈ slitPlane`,
`∂R_C(x, y)/∂x = -R_D(y, y, x) / 6`. -/
theorem hasDerivAt_carlsonRC_left {x y : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    HasDerivAt (fun w => carlsonRC w y) (-carlsonRD y y x / 6) x := by
  have hint : IntegrableOn
      (fun t : ℝ => ((t : ℂ) + y)⁻¹ * ((t : ℂ) + x) ^ (-(1 / 2) : ℂ)) (Ioi 0) :=
    (integrableOn_carlsonRC_integrand (Or.inl hx) hy).congr_fun
      (fun t _ => mul_comm _ _) measurableSet_Ioi
  have hd := (TauCeti.hasDerivAt_integral_mul_ofReal_add_cpow hx hint).const_mul (1 / 2 : ℂ)
  have heq : (fun w : ℂ => (1 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ),
      ((t : ℂ) + y)⁻¹ * ((t : ℂ) + w) ^ (-(1 / 2) : ℂ)) = fun w => carlsonRC w y := by
    funext w
    rw [carlsonRC_eq_integral]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => mul_comm _ _
  rw [heq] at hd
  refine hd.congr_deriv ?_
  rw [carlsonRD_eq_integral]
  have hint_eq : (∫ t in Ioi (0 : ℝ), ((t : ℂ) + y)⁻¹ * ((t : ℂ) + x) ^ (-(1 / 2 : ℂ) - 1)) =
      ∫ t in Ioi (0 : ℝ), ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + x) ^ (-(3 / 2) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [cpow_neg_half_mul_self]
    norm_num
  rw [hint_eq]
  ring

/-- **First partial derivative of `R_C`, closed form.** For `x, y ∈ slitPlane` with `x ≠ y`,
`∂R_C(x, y)/∂x = (R_C(x, y) - x^(-1/2)) / (2 (y - x))`. -/
theorem hasDerivAt_carlsonRC_left_of_ne {x y : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hxy : x ≠ y) :
    HasDerivAt (fun w => carlsonRC w y)
      ((carlsonRC x y - x ^ (-(1 / 2) : ℂ)) / (2 * (y - x))) x := by
  refine (hasDerivAt_carlsonRC_left hx hy).congr_deriv ?_
  rw [eq_div_iff (mul_ne_zero two_ne_zero (sub_ne_zero.mpr hxy.symm))]
  linear_combination -(1 / 3 : ℂ) * sub_mul_carlsonRD_self_left hx hy

/-- `R_C` is complex differentiable in its first argument on `slitPlane`. -/
theorem differentiableOn_carlsonRC_left {y : ℂ} (hy : y ∈ slitPlane) :
    DifferentiableOn ℂ (fun w => carlsonRC w y) slitPlane :=
  fun _ hx => (hasDerivAt_carlsonRC_left hx hy).differentiableAt.differentiableWithinAt

/-- `R_C` is holomorphic in its first argument on `slitPlane`. -/
theorem analyticOnNhd_carlsonRC_left {y : ℂ} (hy : y ∈ slitPlane) :
    AnalyticOnNhd ℂ (fun w => carlsonRC w y) slitPlane :=
  (differentiableOn_carlsonRC_left hy).analyticOnNhd isOpen_slitPlane

/-- **Second partial derivative of `R_C`.** For `x ∈ slitPlane ∪ {0}` and `y ∈ slitPlane`,
`∂R_C(x, y)/∂y = -R_D(x, y, y) / 3`. -/
theorem hasDerivAt_carlsonRC_right {x y : ℂ} (hx : x ∈ slitPlane ∪ {0}) (hy : y ∈ slitPlane) :
    HasDerivAt (carlsonRC x) (-carlsonRD x y y / 3) y := by
  have hint : IntegrableOn
      (fun t : ℝ => ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-1 : ℂ)) (Ioi 0) := by
    simpa only [cpow_neg_one] using integrableOn_carlsonRC_integrand hx hy
  have hd := (TauCeti.hasDerivAt_integral_mul_ofReal_add_cpow hy hint).const_mul (1 / 2 : ℂ)
  have heq : (fun w : ℂ => (1 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ),
      ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + w) ^ (-1 : ℂ)) = carlsonRC x := by
    funext w; simp only [carlsonRC_eq_integral, cpow_neg_one]
  rw [heq] at hd
  refine hd.congr_deriv ?_
  rw [carlsonRD_def, carlsonRJ_def]
  have hint_eq : (∫ t in Ioi (0 : ℝ),
      ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ ((-1 : ℂ) - 1)) =
      ∫ t in Ioi (0 : ℝ), ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y)⁻¹ := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have hy_ne : (t : ℂ) + y ≠ 0 :=
      slitPlane_ne_zero (TauCeti.ofReal_add_mem_slitPlane hy (le_of_lt ht))
    rw [mul_assoc (((t : ℂ) + x) ^ (-(1 / 2) : ℂ)), cpow_neg_half_mul_self,
      mul_assoc (((t : ℂ) + x) ^ (-(1 / 2) : ℂ)), ← cpow_neg_one, ← cpow_add _ _ hy_ne]
    norm_num
  rw [hint_eq]; ring

/-- **Second partial derivative of `R_C`, closed form.** For `x ∈ slitPlane ∪ {0}` and
`y ∈ slitPlane` with `x ≠ y`,
`∂R_C(x, y)/∂y = (x^(1/2) y⁻¹ - R_C(x, y)) / (2 (y - x))`. -/
theorem hasDerivAt_carlsonRC_right_of_ne {x y : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane) (hxy : x ≠ y) :
    HasDerivAt (carlsonRC x) ((x ^ (1 / 2 : ℂ) * y⁻¹ - carlsonRC x y) / (2 * (y - x))) y := by
  refine (hasDerivAt_carlsonRC_right hx hy).congr_deriv ?_
  rw [eq_div_iff (mul_ne_zero two_ne_zero (sub_ne_zero.mpr hxy.symm))]
  linear_combination -(1 / 3 : ℂ) * two_mul_sub_mul_carlsonRD_self_right hx hy

/-- `R_C` is complex differentiable in its second argument on `slitPlane`. -/
theorem differentiableOn_carlsonRC_right {x : ℂ} (hx : x ∈ slitPlane ∪ {0}) :
    DifferentiableOn ℂ (carlsonRC x) slitPlane :=
  fun _ hy => (hasDerivAt_carlsonRC_right hx hy).differentiableAt.differentiableWithinAt

/-- `R_C` is holomorphic in its second argument on `slitPlane`. -/
theorem analyticOnNhd_carlsonRC_right {x : ℂ} (hx : x ∈ slitPlane ∪ {0}) :
    AnalyticOnNhd ℂ (carlsonRC x) slitPlane :=
  (differentiableOn_carlsonRC_right hx).analyticOnNhd isOpen_slitPlane

/-! ### Partial derivatives and holomorphy of `R_J` in its symmetric arguments -/

/-- **Third partial derivative of `R_J`.** For `x ∈ slitPlane ∪ {0}` and `y, z, p ∈ slitPlane`,
`∂R_J(x, y, z, p)/∂z = -(3/4) ∫₀^∞ (t + x)^(-1/2) (t + y)^(-1/2) (t + z)^(-3/2) (t + p)⁻¹ dt`. -/
theorem hasDerivAt_carlsonRJ_third {x y z p : ℂ} (hx : x ∈ slitPlane ∪ {0}) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) (hp : p ∈ slitPlane) :
    HasDerivAt (fun w => carlsonRJ x y w p)
      (-(3 / 4 : ℂ) * ∫ t in Ioi (0 : ℝ), ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + z) ^ (-(3 / 2) : ℂ) * ((t : ℂ) + p)⁻¹) z := by
  have hint : IntegrableOn (fun t : ℝ =>
      (((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + p)⁻¹) *
        ((t : ℂ) + z) ^ (-(1 / 2) : ℂ)) (Ioi 0) :=
    (integrableOn_carlsonRJ_integrand hx hy hz hp).congr_fun
      (fun t _ => by dsimp only; ring) measurableSet_Ioi
  have hd := (TauCeti.hasDerivAt_integral_mul_ofReal_add_cpow hz hint).const_mul (3 / 2 : ℂ)
  have heq : (fun w : ℂ => (3 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ),
      (((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + p)⁻¹) *
        ((t : ℂ) + w) ^ (-(1 / 2) : ℂ)) = fun w => carlsonRJ x y w p := by
    funext w; rw [carlsonRJ_def]; congr 1
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
  rw [heq] at hd
  refine hd.congr_deriv ?_
  have hint_eq : (∫ t in Ioi (0 : ℝ),
      (((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + p)⁻¹) *
        ((t : ℂ) + z) ^ (-(1 / 2 : ℂ) - 1)) =
      ∫ t in Ioi (0 : ℝ), ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + z) ^ (-(3 / 2) : ℂ) * ((t : ℂ) + p)⁻¹ :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by norm_num; ring
  rw [hint_eq]; ring

/-- **Third partial derivative of `R_J`, closed form.** For `x ∈ slitPlane ∪ {0}` and
`y, z, p ∈ slitPlane` with `z ≠ p`,
`∂R_J(x, y, z, p)/∂z = (R_D(x, y, z) - R_J(x, y, z, p)) / (2 (z - p))`. -/
theorem hasDerivAt_carlsonRJ_third_of_ne {x y z p : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) (hp : p ∈ slitPlane) (hzp : z ≠ p) :
    HasDerivAt (fun w => carlsonRJ x y w p)
      ((carlsonRD x y z - carlsonRJ x y z p) / (2 * (z - p))) z := by
  refine (hasDerivAt_carlsonRJ_third hx hy hz hp).congr_deriv ?_
  have hint_rd := integrableOn_carlsonRD_integrand hx hy hz
  have hint_rj := integrableOn_carlsonRJ_integrand hx hy hz hp
  -- Split `(p - z) (t + z)^(-3/2) (t + p)⁻¹ = (t + z)^(-3/2) - (t + z)^(-1/2) (t + p)⁻¹`.
  have hpoint : EqOn
      (fun t : ℝ => (p - z) * (((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + z) ^ (-(3 / 2) : ℂ) * ((t : ℂ) + p)⁻¹))
      (fun t : ℝ => ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
          ((t : ℂ) + z) ^ (-(3 / 2) : ℂ) -
        ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
          ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + p)⁻¹) (Ioi 0) := by
    intro t ht
    dsimp only
    have hz_ne : (t : ℂ) + z ≠ 0 :=
      slitPlane_ne_zero (TauCeti.ofReal_add_mem_slitPlane hz (le_of_lt ht))
    have hp_ne : (t : ℂ) + p ≠ 0 :=
      slitPlane_ne_zero (TauCeti.ofReal_add_mem_slitPlane hp (le_of_lt ht))
    have hz_mul : ((t : ℂ) + z) * ((t : ℂ) + z) ^ (-(3 / 2) : ℂ) =
        ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) := by
      conv_lhs => enter [1]; rw [← cpow_one ((t : ℂ) + z)]
      rw [← cpow_add _ _ hz_ne]; norm_num
    have hpz : p - z = ((t : ℂ) + p) - ((t : ℂ) + z) := by ring
    have hp_inv : ((t : ℂ) + p) * ((t : ℂ) + p)⁻¹ = 1 := mul_inv_cancel₀ hp_ne
    rw [hpz]
    set A : ℂ := ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ)
    linear_combination (A * ((t : ℂ) + z) ^ (-(3 / 2) : ℂ)) * hp_inv -
      (A * ((t : ℂ) + p)⁻¹) * hz_mul
  have hrel : (p - z) * ∫ t in Ioi (0 : ℝ), ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) *
      ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + z) ^ (-(3 / 2) : ℂ) * ((t : ℂ) + p)⁻¹ =
      (2 / 3 : ℂ) * (carlsonRD x y z - carlsonRJ x y z p) := by
    rw [← integral_const_mul, setIntegral_congr_fun measurableSet_Ioi hpoint,
      integral_sub hint_rd hint_rj, carlsonRD_eq_integral, carlsonRJ_def]
    ring
  rw [eq_div_iff (mul_ne_zero two_ne_zero (sub_ne_zero.mpr hzp))]
  linear_combination (3 / 2 : ℂ) * hrel

/-- `R_J` is complex differentiable in its third argument on `slitPlane`. -/
theorem differentiableOn_carlsonRJ_third {x y p : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane) (hp : p ∈ slitPlane) :
    DifferentiableOn ℂ (fun w => carlsonRJ x y w p) slitPlane :=
  fun _ hz => (hasDerivAt_carlsonRJ_third hx hy hz hp).differentiableAt.differentiableWithinAt

/-- `R_J` is holomorphic in its third argument on `slitPlane`. -/
theorem analyticOnNhd_carlsonRJ_third {x y p : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane) (hp : p ∈ slitPlane) :
    AnalyticOnNhd ℂ (fun w => carlsonRJ x y w p) slitPlane :=
  (differentiableOn_carlsonRJ_third hx hy hp).analyticOnNhd isOpen_slitPlane

/-- **Second partial derivative of `R_J`.** For `x ∈ slitPlane ∪ {0}` and `y, z, p ∈ slitPlane`,
`∂R_J(x, y, z, p)/∂y = -(3/4) ∫₀^∞ (t + x)^(-1/2) (t + y)^(-3/2) (t + z)^(-1/2) (t + p)⁻¹ dt`. -/
theorem hasDerivAt_carlsonRJ_second {x y z p : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) (hp : p ∈ slitPlane) :
    HasDerivAt (fun w => carlsonRJ x w z p)
      (-(3 / 4 : ℂ) * ∫ t in Ioi (0 : ℝ), ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + y) ^ (-(3 / 2) : ℂ) * ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + p)⁻¹) y := by
  simp_rw [carlsonRJ_comm_right x _ z p]
  refine (hasDerivAt_carlsonRJ_third hx hz hy hp).congr_deriv ?_
  congr 1; exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring

/-- **Second partial derivative of `R_J`, closed form.** For `x ∈ slitPlane ∪ {0}` and
`y, z, p ∈ slitPlane` with `y ≠ p`,
`∂R_J(x, y, z, p)/∂y = (R_D(x, z, y) - R_J(x, y, z, p)) / (2 (y - p))`. -/
theorem hasDerivAt_carlsonRJ_second_of_ne {x y z p : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) (hp : p ∈ slitPlane) (hyp : y ≠ p) :
    HasDerivAt (fun w => carlsonRJ x w z p)
      ((carlsonRD x z y - carlsonRJ x y z p) / (2 * (y - p))) y := by
  simp_rw [carlsonRJ_comm_right x _ z p]; exact hasDerivAt_carlsonRJ_third_of_ne hx hz hy hp hyp

/-- `R_J` is complex differentiable in its second argument on `slitPlane`. -/
theorem differentiableOn_carlsonRJ_second {x z p : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hz : z ∈ slitPlane) (hp : p ∈ slitPlane) :
    DifferentiableOn ℂ (fun w => carlsonRJ x w z p) slitPlane :=
  fun _ hy => (hasDerivAt_carlsonRJ_second hx hy hz hp).differentiableAt.differentiableWithinAt

/-- `R_J` is holomorphic in its second argument on `slitPlane`. -/
theorem analyticOnNhd_carlsonRJ_second {x z p : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hz : z ∈ slitPlane) (hp : p ∈ slitPlane) :
    AnalyticOnNhd ℂ (fun w => carlsonRJ x w z p) slitPlane :=
  (differentiableOn_carlsonRJ_second hx hz hp).analyticOnNhd isOpen_slitPlane

/-- **First partial derivative of `R_J`.** For `x, z, p ∈ slitPlane` and `y ∈ slitPlane ∪ {0}`,
`∂R_J(x, y, z, p)/∂x = -(3/4) ∫₀^∞ (t + x)^(-3/2) (t + y)^(-1/2) (t + z)^(-1/2) (t + p)⁻¹ dt`. -/
theorem hasDerivAt_carlsonRJ_first {x y z p : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane ∪ {0}) (hz : z ∈ slitPlane) (hp : p ∈ slitPlane) :
    HasDerivAt (fun w => carlsonRJ w y z p)
      (-(3 / 4 : ℂ) * ∫ t in Ioi (0 : ℝ), ((t : ℂ) + x) ^ (-(3 / 2) : ℂ) *
        ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + p)⁻¹) x := by
  simp_rw [carlsonRJ_comm_left _ y z p]
  refine (hasDerivAt_carlsonRJ_second hy hx hz hp).congr_deriv ?_
  congr 1; exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring

/-- **First partial derivative of `R_J`, closed form.** For `x, z, p ∈ slitPlane` and
`y ∈ slitPlane ∪ {0}` with `x ≠ p`,
`∂R_J(x, y, z, p)/∂x = (R_D(y, z, x) - R_J(x, y, z, p)) / (2 (x - p))`. -/
theorem hasDerivAt_carlsonRJ_first_of_ne {x y z p : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane ∪ {0}) (hz : z ∈ slitPlane) (hp : p ∈ slitPlane) (hxp : x ≠ p) :
    HasDerivAt (fun w => carlsonRJ w y z p)
      ((carlsonRD y z x - carlsonRJ x y z p) / (2 * (x - p))) x := by
  simp_rw [carlsonRJ_comm_left _ y z p]; exact hasDerivAt_carlsonRJ_second_of_ne hy hx hz hp hxp

/-- `R_J` is complex differentiable in its first argument on `slitPlane`. -/
theorem differentiableOn_carlsonRJ_first {y z p : ℂ} (hy : y ∈ slitPlane ∪ {0})
    (hz : z ∈ slitPlane) (hp : p ∈ slitPlane) :
    DifferentiableOn ℂ (fun w => carlsonRJ w y z p) slitPlane :=
  fun _ hx => (hasDerivAt_carlsonRJ_first hx hy hz hp).differentiableAt.differentiableWithinAt

/-- `R_J` is holomorphic in its first argument on `slitPlane`. -/
theorem analyticOnNhd_carlsonRJ_first {y z p : ℂ} (hy : y ∈ slitPlane ∪ {0})
    (hz : z ∈ slitPlane) (hp : p ∈ slitPlane) :
    AnalyticOnNhd ℂ (fun w => carlsonRJ w y z p) slitPlane :=
  (differentiableOn_carlsonRJ_first hy hz hp).analyticOnNhd isOpen_slitPlane

/-! ### Partial derivatives and holomorphy of `R_D` -/

/-- **Second partial derivative of `R_D`.** For `x ∈ slitPlane ∪ {0}` and `y, z ∈ slitPlane`,
`∂R_D(x, y, z)/∂y = -(3/4) ∫₀^∞ (t + x)^(-1/2) (t + y)^(-3/2) (t + z)^(-3/2) dt`. -/
theorem hasDerivAt_carlsonRD_middle {x y z : ℂ} (hx : x ∈ slitPlane ∪ {0}) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    HasDerivAt (fun w => carlsonRD x w z)
      (-(3 / 4 : ℂ) * ∫ t in Ioi (0 : ℝ), ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + y) ^ (-(3 / 2) : ℂ) * ((t : ℂ) + z) ^ (-(3 / 2) : ℂ)) y := by
  simp_rw [carlsonRD_def]
  refine (hasDerivAt_carlsonRJ_second hx hy hz hz).congr_deriv ?_
  congr 1; refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [mul_assoc _ (((t : ℂ) + z) ^ (-(1 / 2) : ℂ)), TauCeti.cpow_mul_inv (by norm_num)]; norm_num

/-- **Second partial derivative of `R_D`, closed form.** For `x ∈ slitPlane ∪ {0}` and
`y, z ∈ slitPlane` with `y ≠ z`,
`∂R_D(x, y, z)/∂y = (R_D(x, z, y) - R_D(x, y, z)) / (2 (y - z))`. -/
theorem hasDerivAt_carlsonRD_middle_of_ne {x y z : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) (hyz : y ≠ z) :
    HasDerivAt (fun w => carlsonRD x w z)
      ((carlsonRD x z y - carlsonRD x y z) / (2 * (y - z))) y := by
  simp_rw [carlsonRD_def x _ z]; exact hasDerivAt_carlsonRJ_second_of_ne hx hy hz hz hyz

/-- `R_D` is complex differentiable in its second argument on `slitPlane`. -/
theorem differentiableOn_carlsonRD_middle {x z : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hz : z ∈ slitPlane) : DifferentiableOn ℂ (fun w => carlsonRD x w z) slitPlane :=
  fun _ hy => (hasDerivAt_carlsonRD_middle hx hy hz).differentiableAt.differentiableWithinAt

/-- `R_D` is holomorphic in its second argument on `slitPlane`. -/
theorem analyticOnNhd_carlsonRD_middle {x z : ℂ} (hx : x ∈ slitPlane ∪ {0}) (hz : z ∈ slitPlane) :
    AnalyticOnNhd ℂ (fun w => carlsonRD x w z) slitPlane :=
  (differentiableOn_carlsonRD_middle hx hz).analyticOnNhd isOpen_slitPlane

/-- **First partial derivative of `R_D`.** For `x, z ∈ slitPlane` and `y ∈ slitPlane ∪ {0}`,
`∂R_D(x, y, z)/∂x = -(3/4) ∫₀^∞ (t + x)^(-3/2) (t + y)^(-1/2) (t + z)^(-3/2) dt`. -/
theorem hasDerivAt_carlsonRD_left {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane ∪ {0})
    (hz : z ∈ slitPlane) :
    HasDerivAt (fun w => carlsonRD w y z)
      (-(3 / 4 : ℂ) * ∫ t in Ioi (0 : ℝ), ((t : ℂ) + x) ^ (-(3 / 2) : ℂ) *
        ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + z) ^ (-(3 / 2) : ℂ)) x := by
  simp_rw [carlsonRD_def]
  refine (hasDerivAt_carlsonRJ_first hx hy hz hz).congr_deriv ?_
  congr 1; refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [mul_assoc _ (((t : ℂ) + z) ^ (-(1 / 2) : ℂ)), TauCeti.cpow_mul_inv (by norm_num)]; norm_num

/-- **First partial derivative of `R_D`, closed form.** For `x, z ∈ slitPlane` and
`y ∈ slitPlane ∪ {0}` with `x ≠ z`,
`∂R_D(x, y, z)/∂x = (R_D(y, z, x) - R_D(x, y, z)) / (2 (x - z))`. -/
theorem hasDerivAt_carlsonRD_left_of_ne {x y z : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane ∪ {0}) (hz : z ∈ slitPlane) (hxz : x ≠ z) :
    HasDerivAt (fun w => carlsonRD w y z)
      ((carlsonRD y z x - carlsonRD x y z) / (2 * (x - z))) x := by
  simp_rw [carlsonRD_def _ y z]; exact hasDerivAt_carlsonRJ_first_of_ne hx hy hz hz hxz

/-- `R_D` is complex differentiable in its first argument on `slitPlane`. -/
theorem differentiableOn_carlsonRD_left {y z : ℂ} (hy : y ∈ slitPlane ∪ {0}) (hz : z ∈ slitPlane) :
    DifferentiableOn ℂ (fun w => carlsonRD w y z) slitPlane :=
  fun _ hx => (hasDerivAt_carlsonRD_left hx hy hz).differentiableAt.differentiableWithinAt

/-- `R_D` is holomorphic in its first argument on `slitPlane`. -/
theorem analyticOnNhd_carlsonRD_left {y z : ℂ} (hy : y ∈ slitPlane ∪ {0}) (hz : z ∈ slitPlane) :
    AnalyticOnNhd ℂ (fun w => carlsonRD w y z) slitPlane :=
  (differentiableOn_carlsonRD_left hy hz).analyticOnNhd isOpen_slitPlane

/-- **Third partial derivative of `R_D`.** For `x ∈ slitPlane ∪ {0}` and `y, z ∈ slitPlane`,
`∂R_D(x, y, z)/∂z = -(9/4) ∫₀^∞ (t + x)^(-1/2) (t + y)^(-1/2) (t + z)^(-5/2) dt`. -/
theorem hasDerivAt_carlsonRD_right {x y z : ℂ} (hx : x ∈ slitPlane ∪ {0}) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    HasDerivAt (carlsonRD x y)
      (-(9 / 4 : ℂ) * ∫ t in Ioi (0 : ℝ), ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + z) ^ (-(5 / 2) : ℂ)) z := by
  have hint := integrableOn_carlsonRD_integrand hx hy hz
  have hd := (TauCeti.hasDerivAt_integral_mul_ofReal_add_cpow hz hint).const_mul (3 / 2 : ℂ)
  have heq : (fun w : ℂ => (3 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ),
      (((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ)) *
        ((t : ℂ) + w) ^ (-(3 / 2) : ℂ)) = carlsonRD x y :=
    funext fun w => (carlsonRD_eq_integral x y w).symm
  rw [heq] at hd
  refine hd.congr_deriv ?_
  have hint_eq : (∫ t in Ioi (0 : ℝ),
      (((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ)) *
        ((t : ℂ) + z) ^ (-(3 / 2 : ℂ) - 1)) =
      ∫ t in Ioi (0 : ℝ), ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + z) ^ (-(5 / 2) : ℂ) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by norm_num
  rw [hint_eq]; ring

/-- `R_D` is complex differentiable in its third argument on `slitPlane`. -/
theorem differentiableOn_carlsonRD_right {x y : ℂ} (hx : x ∈ slitPlane ∪ {0}) (hy : y ∈ slitPlane) :
    DifferentiableOn ℂ (carlsonRD x y) slitPlane :=
  fun _ hz => (hasDerivAt_carlsonRD_right hx hy hz).differentiableAt.differentiableWithinAt

/-- `R_D` is holomorphic in its third argument on `slitPlane`. -/
theorem analyticOnNhd_carlsonRD_right {x y : ℂ} (hx : x ∈ slitPlane ∪ {0}) (hy : y ∈ slitPlane) :
    AnalyticOnNhd ℂ (carlsonRD x y) slitPlane :=
  (differentiableOn_carlsonRD_right hx hy).analyticOnNhd isOpen_slitPlane

/-! ### Partial derivatives and holomorphy of `R_G` -/

/-- First weight in the decomposition of `carlsonRGIntegrand x y w t` with respect to `w`. -/
private noncomputable def carlsonRGWeight₁ (x y : ℂ) (t : ℝ) : ℂ :=
  ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
    (x / ((t : ℂ) + x) + y / ((t : ℂ) + y)) * t

/-- Second weight in the decomposition of `carlsonRGIntegrand x y w t` with respect to `w`. -/
private noncomputable def carlsonRGWeight₂ (x y : ℂ) (t : ℝ) : ℂ :=
  ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * t

/-- Decomposition of `carlsonRGIntegrand x y w t` isolating its dependence on `w` into pure
principal powers `(t + w)^(-1/2)` and `(t + w)^(-3/2)`. Holds for all `x, y, w : ℂ` and `t : ℝ`. -/
private theorem carlsonRGIntegrand_eq_add (x y w : ℂ) (t : ℝ) :
    carlsonRGIntegrand x y w t =
      carlsonRGWeight₁ x y t * ((t : ℂ) + w) ^ (-(1 / 2) : ℂ) +
        w * (carlsonRGWeight₂ x y t * ((t : ℂ) + w) ^ (-(3 / 2) : ℂ)) := by
  have hpow : ((t : ℂ) + w) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + w)⁻¹ =
      ((t : ℂ) + w) ^ (-(3 / 2) : ℂ) := by
    rw [TauCeti.cpow_mul_inv (by norm_num)]; norm_num
  rw [carlsonRGIntegrand_def, div_eq_mul_inv w ((t : ℂ) + w)]
  simp only [carlsonRGWeight₁, carlsonRGWeight₂]
  linear_combination
    (((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * w * t) * hpow

/-- Integrability of `t ↦ carlsonRGWeight₂ x y t * (t + z)^(-3/2)` on `(0, ∞)` for all
`x, y ∈ slitPlane ∪ {0}` and `z ∈ slitPlane`, including when both `x` and `y` vanish. -/
private theorem integrableOn_carlsonRGWeight₂_mul_cpow {x y z : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane ∪ {0}) (hz : z ∈ slitPlane) :
    IntegrableOn (fun t : ℝ => carlsonRGWeight₂ x y t * ((t : ℂ) + z) ^ (-(3 / 2) : ℂ))
      (Ioi 0) := by
  have hz_int : IntegrableOn (fun t : ℝ => ((t : ℂ) + z) ^ (-(3 / 2) : ℂ)) (Ioi 0) := by
    refine (integrableOn_carlsonRF_integrand (Or.inl hz) hz hz).congr_fun
      (fun t ht => ?_) measurableSet_Ioi
    have hne := slitPlane_ne_zero (TauCeti.ofReal_add_mem_slitPlane hz (le_of_lt ht))
    dsimp only
    rw [← cpow_add _ _ hne, ← cpow_add _ _ hne]
    norm_num
  have hcont : ContinuousOn
      (fun t : ℝ => carlsonRGWeight₂ x y t * ((t : ℂ) + z) ^ (-(3 / 2) : ℂ)) (Ioi 0) :=
    (((TauCeti.continuousOn_ofReal_add_cpow hx (-(1 / 2))).mul
      (TauCeti.continuousOn_ofReal_add_cpow hy (-(1 / 2)))).mul
      continuous_ofReal.continuousOn).mul
      (TauCeti.continuousOn_ofReal_add_cpow (Or.inl hz) (-(3 / 2)))
  have hr : (-(1 / 2) : ℝ) ≤ 0 := by norm_num
  obtain ⟨Cx, hCx⟩ := TauCeti.exists_norm_ofReal_add_cpow_le_mul_rpow hx hr
  obtain ⟨Cy, hCy⟩ := TauCeti.exists_norm_ofReal_add_cpow_le_mul_rpow hy hr
  have hCx0 : 0 ≤ Cx := by simpa using (norm_nonneg _).trans (hCx 1 one_pos)
  have hCy0 : 0 ≤ Cy := by simpa using (norm_nonneg _).trans (hCy 1 one_pos)
  push_cast at hCx hCy
  refine (hz_int.norm.const_mul (Cx * Cy)).mono'
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) < t := ht
  have ht_cancel : t ^ (-(1 / 2) : ℝ) * t ^ (-(1 / 2) : ℝ) * t = 1 := by
    rw [← Real.rpow_add ht0]; norm_num [Real.rpow_neg_one, inv_mul_cancel₀ ht0.ne']
  simp only [carlsonRGWeight₂, norm_mul, norm_real, Real.norm_of_nonneg ht0.le]
  calc ‖((t : ℂ) + x) ^ (-(1 / 2) : ℂ)‖ * ‖((t : ℂ) + y) ^ (-(1 / 2) : ℂ)‖ * t *
        ‖((t : ℂ) + z) ^ (-(3 / 2) : ℂ)‖
      ≤ (Cx * t ^ (-(1 / 2) : ℝ)) * (Cy * t ^ (-(1 / 2) : ℝ)) * t *
          ‖((t : ℂ) + z) ^ (-(3 / 2) : ℂ)‖ := by gcongr; exacts [hCx t ht0, hCy t ht0]
    _ = Cx * Cy * (t ^ (-(1 / 2) : ℝ) * t ^ (-(1 / 2) : ℝ) * t) *
        ‖((t : ℂ) + z) ^ (-(3 / 2) : ℂ)‖ := by ring
    _ = Cx * Cy * ‖((t : ℂ) + z) ^ (-(3 / 2) : ℂ)‖ := by rw [ht_cancel, mul_one]

/-- Integrability of `t ↦ carlsonRGWeight₁ x y t * (t + z)^(-1/2)` on `(0, ∞)` for all
`x, y ∈ slitPlane ∪ {0}` and `z ∈ slitPlane`, including when both `x` and `y` vanish. -/
private theorem integrableOn_carlsonRGWeight₁_mul_cpow {x y z : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane ∪ {0}) (hz : z ∈ slitPlane) :
    IntegrableOn (fun t : ℝ => carlsonRGWeight₁ x y t * ((t : ℂ) + z) ^ (-(1 / 2) : ℂ))
      (Ioi 0) :=
  ((integrableOn_carlsonRGIntegrand hx hy (Or.inl hz)).sub
    ((integrableOn_carlsonRGWeight₂_mul_cpow hx hy hz).const_mul z)).congr_fun
    (fun t _ => by rw [Pi.sub_apply, carlsonRGIntegrand_eq_add]; ring) measurableSet_Ioi

/-- Splitting formula for `carlsonRG x y w` on `slitPlane`. -/
private theorem carlsonRG_eq_add_of_mem_slitPlane {x y w : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane ∪ {0}) (hw : w ∈ slitPlane) :
    carlsonRG x y w = (1 / 4 : ℂ) *
      ((∫ t in Ioi (0 : ℝ), carlsonRGWeight₁ x y t * ((t : ℂ) + w) ^ (-(1 / 2) : ℂ)) +
        w * ∫ t in Ioi (0 : ℝ), carlsonRGWeight₂ x y t * ((t : ℂ) + w) ^ (-(3 / 2) : ℂ)) := by
  rw [carlsonRG_def, setIntegral_congr_fun measurableSet_Ioi
    (fun t _ => carlsonRGIntegrand_eq_add x y w t),
    integral_add (integrableOn_carlsonRGWeight₁_mul_cpow hx hy hw)
      ((integrableOn_carlsonRGWeight₂_mul_cpow hx hy hw).const_mul w), integral_const_mul]

/-- Pointwise derivative on `(0, ∞)` of `K(t) = -t² (t + x)^(-1/2) (t + y)^(-1/2) (t + z)^(-3/2)`,
the function whose derivative integrates to the correction term in `∂R_G/∂z`. -/
private lemma hasDerivAt_carlsonRG_antiderivative_aux {x y z : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane ∪ {0}) (hz : z ∈ slitPlane) {t : ℝ}
    (ht : t ∈ Ioi (0 : ℝ)) :
    HasDerivAt (fun t : ℝ => -(t : ℂ) ^ 2 * ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) *
      ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + z) ^ (-(3 / 2) : ℂ))
      ((1 / 2 : ℂ) * (carlsonRGWeight₂ x y t * ((t : ℂ) + z) ^ (-(3 / 2) : ℂ)) -
        (1 / 2 : ℂ) * (carlsonRGWeight₁ x y t * ((t : ℂ) + z) ^ (-(3 / 2) : ℂ)) -
        (3 / 2 : ℂ) * z * (carlsonRGWeight₂ x y t * ((t : ℂ) + z) ^ (-(5 / 2) : ℂ))) t := by
  set K : ℝ → ℂ := fun t => -(t : ℂ) ^ 2 * ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) *
    ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + z) ^ (-(3 / 2) : ℂ) with hKdef
  have htx : (t : ℂ) + x ∈ slitPlane := TauCeti.ofReal_add_mem_slitPlane_of_mem_union hx ht
  have hty : (t : ℂ) + y ∈ slitPlane := TauCeti.ofReal_add_mem_slitPlane_of_mem_union hy ht
  have htz : (t : ℂ) + z ∈ slitPlane := TauCeti.ofReal_add_mem_slitPlane hz (le_of_lt ht)
  have htx_ne : (t : ℂ) + x ≠ 0 := slitPlane_ne_zero htx
  have hty_ne : (t : ℂ) + y ≠ 0 := slitPlane_ne_zero hty
  have htz_ne : (t : ℂ) + z ≠ 0 := slitPlane_ne_zero htz
  have hd_t : HasDerivAt (fun s : ℝ => -(s : ℂ) ^ 2) (-2 * (t : ℂ)) t := by
    simpa using (((hasDerivAt_pow 2 (t : ℂ)).neg).comp_ofReal)
  have hd_x : HasDerivAt (fun s : ℝ => ((s : ℂ) + x) ^ (-(1 / 2) : ℂ))
      (-(1 / 2 : ℂ) * ((t : ℂ) + x) ^ (-(1 / 2 : ℂ) - 1) * 1) t := by
    simpa using (((hasDerivAt_id (t : ℂ)).add_const x).cpow_const (c := -(1 / 2 : ℂ))
      htx).comp_ofReal
  have hd_y : HasDerivAt (fun s : ℝ => ((s : ℂ) + y) ^ (-(1 / 2) : ℂ))
      (-(1 / 2 : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2 : ℂ) - 1) * 1) t := by
    simpa using (((hasDerivAt_id (t : ℂ)).add_const y).cpow_const (c := -(1 / 2 : ℂ))
      hty).comp_ofReal
  have hd_z : HasDerivAt (fun s : ℝ => ((s : ℂ) + z) ^ (-(3 / 2) : ℂ))
      (-(3 / 2 : ℂ) * ((t : ℂ) + z) ^ (-(3 / 2 : ℂ) - 1) * 1) t := by
    simpa using (((hasDerivAt_id (t : ℂ)).add_const z).cpow_const (c := -(3 / 2 : ℂ))
      htz).comp_ofReal
  refine (((hd_t.fun_mul hd_x).fun_mul hd_y).fun_mul hd_z).congr_deriv ?_
  simp only [mul_one, carlsonRGWeight₁, carlsonRGWeight₂]
  -- Express `(t + w)^(c - 1)` as `(t + w)^c * (t + w)⁻¹` and use `(t + w) * (t + w)⁻¹ = 1`.
  have hx_sub : ((t : ℂ) + x) ^ (-(1 / 2 : ℂ) - 1) =
      ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + x)⁻¹ := by
    rw [cpow_sub _ _ htx_ne, cpow_one, div_eq_mul_inv]
  have hy_sub : ((t : ℂ) + y) ^ (-(1 / 2 : ℂ) - 1) =
      ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y)⁻¹ := by
    rw [cpow_sub _ _ hty_ne, cpow_one, div_eq_mul_inv]
  have hz_sub : ((t : ℂ) + z) ^ (-(3 / 2 : ℂ) - 1) = ((t : ℂ) + z) ^ (-(5 / 2) : ℂ) := by
    norm_num
  have hz_inv : ((t : ℂ) + z) ^ (-(3 / 2) : ℂ) * ((t : ℂ) + z)⁻¹ =
      ((t : ℂ) + z) ^ (-(5 / 2) : ℂ) := by
    rw [TauCeti.cpow_mul_inv (by norm_num)]; norm_num
  have hx_inv : ((t : ℂ) + x) * ((t : ℂ) + x)⁻¹ = 1 := mul_inv_cancel₀ htx_ne
  have hy_inv : ((t : ℂ) + y) * ((t : ℂ) + y)⁻¹ = 1 := mul_inv_cancel₀ hty_ne
  have htz_inv : ((t : ℂ) + z) * ((t : ℂ) + z)⁻¹ = 1 := mul_inv_cancel₀ htz_ne
  rw [hx_sub, hy_sub, hz_sub, ← hz_inv, div_eq_mul_inv x ((t : ℂ) + x),
    div_eq_mul_inv y ((t : ℂ) + y)]
  set ux : ℂ := ((t : ℂ) + x) ^ (-(1 / 2) : ℂ)
  set uy : ℂ := ((t : ℂ) + y) ^ (-(1 / 2) : ℂ)
  set uz : ℂ := ((t : ℂ) + z) ^ (-(3 / 2) : ℂ)
  linear_combination
    ((1 / 2 : ℂ) * (t : ℂ) * ux * uy * uz) * hx_inv +
      ((1 / 2 : ℂ) * (t : ℂ) * ux * uy * uz) * hy_inv +
      ((3 / 2 : ℂ) * (t : ℂ) * ux * uy * uz) * htz_inv

/-- `K(t) = -t² (t + x)^(-1/2) (t + y)^(-1/2) (t + z)^(-3/2)` is continuous at `0` from the right,
since `‖K(t)‖ = O(t)` as `t → 0⁺`. -/
private lemma continuousWithinAt_carlsonRG_antiderivative_aux {x y z : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane ∪ {0}) (hz : z ∈ slitPlane) :
    ContinuousWithinAt (fun t : ℝ => -(t : ℂ) ^ 2 * ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) *
      ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + z) ^ (-(3 / 2) : ℂ)) (Ici 0) 0 := by
  set K : ℝ → ℂ := fun t => -(t : ℂ) ^ 2 * ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) *
    ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + z) ^ (-(3 / 2) : ℂ) with hKdef
  have hK_zero : K 0 = 0 := by simp [K]
  have hr : (-(1 / 2) : ℝ) ≤ 0 := by norm_num
  obtain ⟨Cx, hCx⟩ := TauCeti.exists_norm_ofReal_add_cpow_le_mul_rpow hx hr
  obtain ⟨Cy, hCy⟩ := TauCeti.exists_norm_ofReal_add_cpow_le_mul_rpow hy hr
  obtain ⟨Cz, hCz⟩ := TauCeti.exists_norm_ofReal_add_cpow_le hz (r := -(3 / 2)) (by norm_num)
  have hCx0 : 0 ≤ Cx := by simpa using (norm_nonneg _).trans (hCx 1 one_pos)
  have hCy0 : 0 ≤ Cy := by simpa using (norm_nonneg _).trans (hCy 1 one_pos)
  push_cast at hCx hCy hCz
  rw [ContinuousWithinAt, hK_zero]
  have h0 : Tendsto (fun t : ℝ => Cx * Cy * Cz * t) (𝓝[Ici 0] 0) (𝓝 0) := by
    simpa using ((continuous_id.continuousWithinAt (s := Ici (0 : ℝ)) (x := 0)).const_mul
      (Cx * Cy * Cz)).tendsto
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [self_mem_nhdsWithin] with t ht
  rcases (ht : 0 ≤ t).eq_or_lt with rfl | ht0
  · simp [K]
  · have ht_sq : t ^ 2 * t ^ (-(1 / 2) : ℝ) * t ^ (-(1 / 2) : ℝ) = t := by
      have h1 : t ^ (-(1 / 2) : ℝ) * t ^ (-(1 / 2) : ℝ) = t⁻¹ := by
        rw [← Real.rpow_add ht0]; norm_num [Real.rpow_neg_one]
      rw [mul_assoc, h1, sq, mul_assoc, mul_inv_cancel₀ ht0.ne', mul_one]
    have hcz0 : 0 ≤ Cz := (norm_nonneg _).trans (hCz t ht0.le)
    simp only [K, norm_mul, norm_neg, norm_pow, norm_real, Real.norm_of_nonneg ht0.le]
    calc t ^ 2 * ‖((t : ℂ) + x) ^ (-(1 / 2) : ℂ)‖ * ‖((t : ℂ) + y) ^ (-(1 / 2) : ℂ)‖ *
          ‖((t : ℂ) + z) ^ (-(3 / 2) : ℂ)‖
        ≤ t ^ 2 * (Cx * t ^ (-(1 / 2) : ℝ)) * (Cy * t ^ (-(1 / 2) : ℝ)) * Cz := by
          gcongr; exacts [hCx t ht0, hCy t ht0, hCz t ht0.le]
      _ = Cx * Cy * Cz * (t ^ 2 * t ^ (-(1 / 2) : ℝ) * t ^ (-(1 / 2) : ℝ)) := by ring
      _ = Cx * Cy * Cz * t := by rw [ht_sq]

/-- `K(t) = -t² (t + x)^(-1/2) (t + y)^(-1/2) (t + z)^(-3/2)` tends to `0` at `+∞`, since
`‖K(t)‖ = O(t^(-1/2))`. -/
private lemma tendsto_carlsonRG_antiderivative_aux {x y z : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane ∪ {0}) (hz : z ∈ slitPlane) :
    Tendsto (fun t : ℝ => -(t : ℂ) ^ 2 * ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) *
      ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + z) ^ (-(3 / 2) : ℂ)) atTop (𝓝 0) := by
  set K : ℝ → ℂ := fun t => -(t : ℂ) ^ 2 * ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) *
    ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + z) ^ (-(3 / 2) : ℂ) with hKdef
  have hr : (-(1 / 2) : ℝ) ≤ 0 := by norm_num
  obtain ⟨Cx, hCx⟩ := TauCeti.exists_norm_ofReal_add_cpow_le_mul_rpow hx hr
  obtain ⟨Cy, hCy⟩ := TauCeti.exists_norm_ofReal_add_cpow_le_mul_rpow hy hr
  obtain ⟨Cz', hCz'⟩ := TauCeti.exists_norm_ofReal_add_cpow_le_mul_rpow (Or.inl hz)
    (r := -(3 / 2)) (by norm_num)
  have hCx0 : 0 ≤ Cx := by simpa using (norm_nonneg _).trans (hCx 1 one_pos)
  have hCy0 : 0 ≤ Cy := by simpa using (norm_nonneg _).trans (hCy 1 one_pos)
  push_cast at hCx hCy hCz'
  have h0 : Tendsto (fun t : ℝ => Cx * Cy * Cz' * t ^ (-(1 / 2) : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
      (Cx * Cy * Cz')
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht0
  have hcz'0 : 0 ≤ Cz' := by simpa using (norm_nonneg _).trans (hCz' 1 one_pos)
  have ht_pow : t ^ 2 * t ^ (-(1 / 2) : ℝ) * t ^ (-(1 / 2) : ℝ) * t ^ (-(3 / 2) : ℝ) =
      t ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_add ht0, ← Real.rpow_add ht0, ← Real.rpow_add ht0]
    norm_num
  simp only [K, norm_mul, norm_neg, norm_pow, norm_real, Real.norm_of_nonneg ht0.le]
  calc t ^ 2 * ‖((t : ℂ) + x) ^ (-(1 / 2) : ℂ)‖ * ‖((t : ℂ) + y) ^ (-(1 / 2) : ℂ)‖ *
        ‖((t : ℂ) + z) ^ (-(3 / 2) : ℂ)‖
      ≤ t ^ 2 * (Cx * t ^ (-(1 / 2) : ℝ)) * (Cy * t ^ (-(1 / 2) : ℝ)) *
          (Cz' * t ^ (-(3 / 2) : ℝ)) := by gcongr; exacts [hCx t ht0, hCy t ht0, hCz' t ht0]
    _ = Cx * Cy * Cz' *
        (t ^ 2 * t ^ (-(1 / 2) : ℝ) * t ^ (-(1 / 2) : ℝ) * t ^ (-(3 / 2) : ℝ)) := by ring
    _ = Cx * Cy * Cz' * t ^ (-(1 / 2) : ℝ) := by rw [ht_pow]

/-- **Third partial derivative of `R_G`, integral form.** Valid for all `x, y ∈ slitPlane ∪ {0}`
and `z ∈ slitPlane` (even when both `x` and `y` vanish):
`∂R_G(x, y, z)/∂z = (1/8) ∫₀^∞ (t + x)^(-1/2) (t + y)^(-1/2) (t + z)^(-3/2) t dt`. -/
theorem hasDerivAt_carlsonRG_right_integral {x y z : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane ∪ {0}) (hz : z ∈ slitPlane) :
    HasDerivAt (carlsonRG x y)
      ((1 / 8 : ℂ) * ∫ t in Ioi (0 : ℝ), ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + z) ^ (-(3 / 2) : ℂ) * t) z := by
  -- Differentiate the split representation of `carlsonRG x y` term-by-term on `slitPlane`.
  have hint₁ := integrableOn_carlsonRGWeight₁_mul_cpow hx hy hz
  have hint₂ := integrableOn_carlsonRGWeight₂_mul_cpow hx hy hz
  have hd₁ := TauCeti.hasDerivAt_integral_mul_ofReal_add_cpow hz hint₁
  have hd₂ := (hasDerivAt_id z).fun_mul (TauCeti.hasDerivAt_integral_mul_ofReal_add_cpow hz hint₂)
  have hd_raw := ((hd₁.fun_add hd₂).const_mul (1 / 4 : ℂ)).congr_of_eventuallyEq
    (Filter.Eventually.mono (isOpen_slitPlane.mem_nhds hz) fun w hw =>
      carlsonRG_eq_add_of_mem_slitPlane hx hy hw)
  -- Integrate `K(t) = -t² (t + x)^(-1/2) (t + y)^(-1/2) (t + z)^(-3/2)` on `(0, ∞)` to simplify.
  let K : ℝ → ℂ := fun t => -(t : ℂ) ^ 2 * ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) *
    ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + z) ^ (-(3 / 2) : ℂ)
  let K' : ℝ → ℂ := fun t =>
    (1 / 2 : ℂ) * (carlsonRGWeight₂ x y t * ((t : ℂ) + z) ^ (-(3 / 2) : ℂ)) -
      (1 / 2 : ℂ) * (carlsonRGWeight₁ x y t * ((t : ℂ) + z) ^ (-(3 / 2) : ℂ)) -
      (3 / 2 : ℂ) * z * (carlsonRGWeight₂ x y t * ((t : ℂ) + z) ^ (-(5 / 2) : ℂ))
  have hK_zero : K 0 = 0 := by simp [K]
  have hK0 : ContinuousWithinAt K (Ici 0) 0 :=
    continuousWithinAt_carlsonRG_antiderivative_aux hx hy hz
  have hK_deriv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt K (K' t) t := fun t ht =>
    hasDerivAt_carlsonRG_antiderivative_aux hx hy hz ht
  -- Integrability of `K'` and decay `‖K(t)‖ = O(t^(-1/2)) → 0` as `t → ∞`.
  have hint₁' : IntegrableOn
      (fun t : ℝ => carlsonRGWeight₁ x y t * ((t : ℂ) + z) ^ (-(3 / 2) : ℂ)) (Ioi 0) :=
    TauCeti.integrableOn_mul_ofReal_add_cpow_of_re_le hz hz (by norm_num) hint₁
  have hint₂' : IntegrableOn
      (fun t : ℝ => carlsonRGWeight₂ x y t * ((t : ℂ) + z) ^ (-(5 / 2) : ℂ)) (Ioi 0) :=
    TauCeti.integrableOn_mul_ofReal_add_cpow_of_re_le hz hz (by norm_num) hint₂
  have h12 : IntegrableOn (fun t : ℝ =>
      (1 / 2 : ℂ) * (carlsonRGWeight₂ x y t * ((t : ℂ) + z) ^ (-(3 / 2) : ℂ)) -
        (1 / 2 : ℂ) * (carlsonRGWeight₁ x y t * ((t : ℂ) + z) ^ (-(3 / 2) : ℂ))) (Ioi 0) :=
    (hint₂.const_mul (1 / 2 : ℂ)).sub (hint₁'.const_mul (1 / 2 : ℂ))
  have hintK' : IntegrableOn K' (Ioi 0) := h12.sub (hint₂'.const_mul ((3 / 2 : ℂ) * z))
  have hK_lim : Tendsto K atTop (𝓝 0) := tendsto_carlsonRG_antiderivative_aux hx hy hz
  -- Apply FTC on `(0, ∞)` (`∫ K' = 0 - K(0) = 0`) to collapse `hd_raw` to the integral form.
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto hK0 hK_deriv hintK' hK_lim
  rw [hK_zero, sub_zero] at hftc
  simp only [K'] at hftc
  rw [integral_sub h12 (hint₂'.const_mul _),
    integral_sub (hint₂.const_mul _) (hint₁'.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul] at hftc
  refine hd_raw.congr_deriv ?_
  have heq₁ : (-(1 / 2 : ℂ) - 1) = -(3 / 2 : ℂ) := by norm_num
  have heq₂ : (-(3 / 2 : ℂ) - 1) = -(5 / 2 : ℂ) := by norm_num
  simp only [id, one_mul, heq₁, heq₂]
  have hw₂_eq : (∫ t in Ioi (0 : ℝ), carlsonRGWeight₂ x y t * ((t : ℂ) + z) ^ (-(3 / 2) : ℂ)) =
      ∫ t in Ioi (0 : ℝ), ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + z) ^ (-(3 / 2) : ℂ) * t :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by simp only [carlsonRGWeight₂]; ring
  rw [← hw₂_eq]
  linear_combination (1 / 4 : ℂ) * hftc

/-- **Third partial derivative of `R_G`, closed form.** When at most one of `x, y` vanishes
(`x ∈ slitPlane ∪ {0}`, `y, z ∈ slitPlane`),
`∂R_G(x, y, z)/∂z = R_F(x, y, z) / 4 - z R_D(x, y, z) / 12`. -/
theorem hasDerivAt_carlsonRG_right {x y z : ℂ} (hx : x ∈ slitPlane ∪ {0}) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    HasDerivAt (carlsonRG x y) (carlsonRF x y z / 4 - z * carlsonRD x y z / 12) z := by
  refine (hasDerivAt_carlsonRG_right_integral hx (Or.inl hy) hz).congr_deriv ?_
  have hint_rf := integrableOn_carlsonRF_integrand hx hy hz
  have hint_rd := integrableOn_carlsonRD_integrand hx hy hz
  -- Split `t = ((t : ℂ) + z) - z` in the integral form of `∂R_G/∂z`.
  have hpoint : EqOn
      (fun t : ℝ => ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + z) ^ (-(3 / 2) : ℂ) * t)
      (fun t : ℝ => ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
          ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) -
        z * (((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
          ((t : ℂ) + z) ^ (-(3 / 2) : ℂ))) (Ioi 0) := by
    intro t ht
    dsimp only
    have hz_ne : (t : ℂ) + z ≠ 0 :=
      slitPlane_ne_zero (TauCeti.ofReal_add_mem_slitPlane hz (le_of_lt ht))
    have hz_mul : ((t : ℂ) + z) ^ (-(3 / 2) : ℂ) * ((t : ℂ) + z) =
        ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) := by
      conv_lhs => enter [2]; rw [← cpow_one ((t : ℂ) + z)]
      rw [← cpow_add _ _ hz_ne]; norm_num
    have ht_eq : (t : ℂ) = ((t : ℂ) + z) - z := by ring
    conv_lhs => enter [2]; rw [ht_eq]
    linear_combination (((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ)) * hz_mul
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint,
    integral_sub hint_rf (hint_rd.const_mul z), integral_const_mul, carlsonRF_def,
    carlsonRD_eq_integral]
  ring

/-- `R_G` is complex differentiable in its third argument on `slitPlane` for all
`x, y ∈ slitPlane ∪ {0}` (even when both `x` and `y` vanish). -/
theorem differentiableOn_carlsonRG_right {x y : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane ∪ {0}) : DifferentiableOn ℂ (carlsonRG x y) slitPlane :=
  fun _ hz =>
    (hasDerivAt_carlsonRG_right_integral hx hy hz).differentiableAt.differentiableWithinAt

/-- `R_G` is holomorphic in its third argument on `slitPlane` for all `x, y ∈ slitPlane ∪ {0}`
(even when both `x` and `y` vanish). -/
theorem analyticOnNhd_carlsonRG_right {x y : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane ∪ {0}) : AnalyticOnNhd ℂ (carlsonRG x y) slitPlane :=
  (differentiableOn_carlsonRG_right hx hy).analyticOnNhd isOpen_slitPlane

/-- **Second partial derivative of `R_G`, integral form.** Valid for all `x, z ∈ slitPlane ∪ {0}`
and `y ∈ slitPlane`:
`∂R_G(x, y, z)/∂y = (1/8) ∫₀^∞ (t + x)^(-1/2) (t + y)^(-3/2) (t + z)^(-1/2) t dt`. -/
theorem hasDerivAt_carlsonRG_middle_integral {x y z : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane ∪ {0}) :
    HasDerivAt (fun w => carlsonRG x w z)
      ((1 / 8 : ℂ) * ∫ t in Ioi (0 : ℝ), ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + y) ^ (-(3 / 2) : ℂ) * ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) * t) y := by
  simp_rw [carlsonRG_comm_right x _ z]
  refine (hasDerivAt_carlsonRG_right_integral hx hz hy).congr_deriv ?_
  congr 1; exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring

/-- **Second partial derivative of `R_G`, closed form.** When at most one of `x, z` vanishes
(`x ∈ slitPlane ∪ {0}`, `y, z ∈ slitPlane`),
`∂R_G(x, y, z)/∂y = R_F(x, y, z) / 4 - y R_D(x, z, y) / 12`. -/
theorem hasDerivAt_carlsonRG_middle {x y z : ℂ} (hx : x ∈ slitPlane ∪ {0}) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    HasDerivAt (fun w => carlsonRG x w z) (carlsonRF x y z / 4 - y * carlsonRD x z y / 12) y := by
  simp_rw [carlsonRG_comm_right x _ z, carlsonRF_comm_right x y z]
  exact hasDerivAt_carlsonRG_right hx hz hy

/-- `R_G` is complex differentiable in its second argument on `slitPlane` for all
`x, z ∈ slitPlane ∪ {0}`. -/
theorem differentiableOn_carlsonRG_middle {x z : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hz : z ∈ slitPlane ∪ {0}) : DifferentiableOn ℂ (fun w => carlsonRG x w z) slitPlane :=
  fun _ hy =>
    (hasDerivAt_carlsonRG_middle_integral hx hy hz).differentiableAt.differentiableWithinAt

/-- `R_G` is holomorphic in its second argument on `slitPlane` for all `x, z ∈ slitPlane ∪ {0}`. -/
theorem analyticOnNhd_carlsonRG_middle {x z : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hz : z ∈ slitPlane ∪ {0}) : AnalyticOnNhd ℂ (fun w => carlsonRG x w z) slitPlane :=
  (differentiableOn_carlsonRG_middle hx hz).analyticOnNhd isOpen_slitPlane

/-- **First partial derivative of `R_G`, integral form.** Valid for all `y, z ∈ slitPlane ∪ {0}`
and `x ∈ slitPlane`:
`∂R_G(x, y, z)/∂x = (1/8) ∫₀^∞ (t + x)^(-3/2) (t + y)^(-1/2) (t + z)^(-1/2) t dt`. -/
theorem hasDerivAt_carlsonRG_left_integral {x y z : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane ∪ {0}) (hz : z ∈ slitPlane ∪ {0}) :
    HasDerivAt (fun w => carlsonRG w y z)
      ((1 / 8 : ℂ) * ∫ t in Ioi (0 : ℝ), ((t : ℂ) + x) ^ (-(3 / 2) : ℂ) *
        ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) * t) x := by
  simp_rw [carlsonRG_comm_left _ y z]
  refine (hasDerivAt_carlsonRG_middle_integral hy hx hz).congr_deriv ?_
  congr 1; exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring

/-- **First partial derivative of `R_G`, closed form.** When at most one of `y, z` vanishes
(`x, z ∈ slitPlane`, `y ∈ slitPlane ∪ {0}`),
`∂R_G(x, y, z)/∂x = R_F(x, y, z) / 4 - x R_D(y, z, x) / 12`. -/
theorem hasDerivAt_carlsonRG_left {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane ∪ {0})
    (hz : z ∈ slitPlane) :
    HasDerivAt (fun w => carlsonRG w y z) (carlsonRF x y z / 4 - x * carlsonRD y z x / 12) x := by
  simp_rw [carlsonRG_comm_left _ y z, carlsonRF_comm_left x y z]
  exact hasDerivAt_carlsonRG_middle hy hx hz

/-- `R_G` is complex differentiable in its first argument on `slitPlane` for all
`y, z ∈ slitPlane ∪ {0}`. -/
theorem differentiableOn_carlsonRG_left {y z : ℂ} (hy : y ∈ slitPlane ∪ {0})
    (hz : z ∈ slitPlane ∪ {0}) : DifferentiableOn ℂ (fun w => carlsonRG w y z) slitPlane :=
  fun _ hx =>
    (hasDerivAt_carlsonRG_left_integral hx hy hz).differentiableAt.differentiableWithinAt

/-- `R_G` is holomorphic in its first argument on `slitPlane` for all `y, z ∈ slitPlane ∪ {0}`. -/
theorem analyticOnNhd_carlsonRG_left {y z : ℂ} (hy : y ∈ slitPlane ∪ {0})
    (hz : z ∈ slitPlane ∪ {0}) : AnalyticOnNhd ℂ (fun w => carlsonRG w y z) slitPlane :=
  (differentiableOn_carlsonRG_left hy hz).analyticOnNhd isOpen_slitPlane

end Complex

end

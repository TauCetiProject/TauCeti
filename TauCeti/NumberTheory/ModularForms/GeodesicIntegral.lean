/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import TauCeti.NumberTheory.ModularForms.ResToImagAxis
public import TauCeti.NumberTheory.ModularForms.SlashActionRat
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# Integrals of one-forms along geodesics between cusps

For `F : ℍ → ℂ` and a rational matrix `g ∈ GL(2, ℚ)` of positive determinant, the geodesic from
the cusp `g • 0` to the cusp `g • ∞` is the image under `g` of the positive imaginary axis, and
the substitution `z = g • (i t)` turns the integral of the one-form `F(z) dz` along it into

`∫_{g • 0}^{g • ∞} F(z) dz = i ∫₀^∞ (F ∣[2] g)(i t) dt`,

because the weight-`2` slash `(F ∣[2] g)(τ) = F(g • τ) · det g · (cτ + d)⁻²` is exactly the
pullback of `F(z) dz` along `τ ↦ g • τ`. This file takes the right-hand side as the definition of
the **geodesic integral** `Matrix.GeneralLinearGroup.geodesicIntegral g F` and proves that it is
intrinsic to the oriented geodesic: it depends only on the pair of endpoints `(g • 0, g • ∞)`,
changes sign when the endpoints are swapped, and transforms under a further matrix by slashing the
integrand. Both endpoints are improper, and the integral is a Bochner integral, so it vanishes when
the integrand is not integrable; the convergence criterion
`UpperHalfPlane.integrableOn_resToImagAxis_Ioi_of_slash_S` (in
`TauCeti.NumberTheory.ModularForms.ResToImagAxis`) reduces integrability near the finite end
`g • 0` to integrability near `i∞` of the reflected integrand `F ∣[2] (g S)`, so that both ends are
handled by decay at `i∞`.

The definition is total in `g`, following the convention of the rational slash action itself
(`TauCeti.NumberTheory.ModularForms.SlashActionRat`) and of the Hecke modules, which work in
`GL(2, ℚ)` and assume `0 < det g` where they need it. For `det g < 0` the value is the same
formula, but Mathlib's slash then involves complex conjugation, so it is *not* the integral of
`F(z) dz` along the geodesic from `g • 0` to `g • ∞`: every statement below whose content is
geometric — dependence on the endpoints only, `ℂ`-linearity, convergence — carries the hypothesis
`0 < det g`, and the identities stated for all `g` (`geodesicIntegral_mul`,
`geodesicIntegral_mul_S`, additivity) are algebraic consequences of the slash action, whose
geometric reading likewise requires positive determinant.

These integrals are the raw material of the period pairing between cusp forms and modular
symbols, whose integrand `f(z) P(z, 1)` and convergence are treated in
`TauCeti.NumberTheory.ModularForms.ModularSymbols.PeriodIntegral`.

## Main definitions

* `Matrix.GeneralLinearGroup.geodesicIntegral g F`: the integral `∫_{g • 0}^{g • ∞} F(z) dz`, as
  `i ∫₀^∞ (F ∣[2] g)(i t) dt`. It is an operation on the matrix `g ∈ GL(2, ℚ)` cutting out the
  geodesic, so it lives in the namespace of `GL` and is available as `g.geodesicIntegral F`.

## Main results

* `Matrix.GeneralLinearGroup.geodesicIntegral_mul`: the substitution `z ↦ g • z`,
  `∫_{gh • 0}^{gh • ∞} F(z) dz = ∫_{h • 0}^{h • ∞} (F ∣[2] g)(z) dz`.
* `Matrix.GeneralLinearGroup.geodesicIntegral_mul_of_diagonal` and
  `Matrix.GeneralLinearGroup.geodesicIntegral_eq_of_smul_eq`: the integral only depends on the
  endpoints `g • 0` and `g • ∞`, for `g` of positive determinant.
* `Matrix.GeneralLinearGroup.geodesicIntegral_mul_S`: reversing the orientation,
  `∫_{g • ∞}^{g • 0} F(z) dz = -∫_{g • 0}^{g • ∞} F(z) dz`.
* `Matrix.GeneralLinearGroup.geodesicIntegral_add` and
  `Matrix.GeneralLinearGroup.geodesicIntegral_smul`: linearity in the integrand, for integrable
  integrands.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §8.2.
* Y. I. Manin, *Parabolic points and zeta functions of modular curves*, Izv. Akad. Nauk SSSR
  Ser. Mat. **36** (1972), 19–66, §1.
-/

public section

open Complex MeasureTheory Set Matrix Matrix.GeneralLinearGroup Matrix.SpecialLinearGroup
open ModularGroup OnePoint
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm

namespace TauCeti

/-- The integral `∫_{g • 0}^{g • ∞} F(z) dz` of the one-form `F(z) dz` along the hyperbolic
geodesic from the cusp `g • 0` to the cusp `g • ∞`, for `g ∈ GL(2, ℚ)` of positive determinant:
that geodesic is the `g`-image of the positive imaginary axis, and substituting `z = g • (i t)`
gives `i ∫₀^∞ (F ∣[2] g)(i t) dt`, the imaginary-axis integral of the weight-`2` slash of `F`.
Both endpoints are improper, and the Bochner integral is `0` when the integrand is not
integrable.

The definition is total in `g`, like the slash action: for `det g < 0` it is the same formula,
which is then a junk value and not the integral along the geodesic from `g • 0` to `g • ∞` (the
slash of a negative-determinant matrix involves complex conjugation). Every result reading it as a
geodesic integral assumes `0 < det g`. -/
noncomputable def _root_.Matrix.GeneralLinearGroup.geodesicIntegral (g : GL (Fin 2) ℚ)
    (F : ℍ → ℂ) : ℂ :=
  I * ∫ t in Ioi (0 : ℝ), resToImagAxis (F ∣[(2 : ℤ)] g) t

/-- Definition of the geodesic integral. -/
theorem _root_.Matrix.GeneralLinearGroup.geodesicIntegral_def (g : GL (Fin 2) ℚ) (F : ℍ → ℂ) :
    geodesicIntegral g F = I * ∫ t in Ioi (0 : ℝ), resToImagAxis (F ∣[(2 : ℤ)] g) t := by
  rw [geodesicIntegral]

/-- **The substitution `z ↦ g • z`**: the integral of `F(z) dz` from `gh • 0` to `gh • ∞` is the
integral of the pulled-back one-form `(F ∣[2] g)(z) dz` from `h • 0` to `h • ∞`. The identity is
an algebraic consequence of the slash action and holds for every `g` and `h`; its reading as a
substitution in a geodesic integral requires `g` and `h` to have positive determinant. -/
theorem _root_.Matrix.GeneralLinearGroup.geodesicIntegral_mul (g h : GL (Fin 2) ℚ) (F : ℍ → ℂ) :
    geodesicIntegral (g * h) F = geodesicIntegral h (F ∣[(2 : ℤ)] g) := by
  rw [geodesicIntegral, geodesicIntegral, SlashAction.slash_mul]

/-- The geodesic integral of the zero one-form vanishes. -/
@[simp]
theorem _root_.Matrix.GeneralLinearGroup.geodesicIntegral_zero (g : GL (Fin 2) ℚ) :
    geodesicIntegral g 0 = 0 := by
  simp [geodesicIntegral]

/-- The geodesic integral is additive in the integrand, for integrable integrands (for every
`g`, since the slash action is additive). -/
theorem _root_.Matrix.GeneralLinearGroup.geodesicIntegral_add (g : GL (Fin 2) ℚ) {F G : ℍ → ℂ}
    (hF : IntegrableOn (resToImagAxis (F ∣[(2 : ℤ)] g)) (Ioi 0))
    (hG : IntegrableOn (resToImagAxis (G ∣[(2 : ℤ)] g)) (Ioi 0)) :
    geodesicIntegral g (F + G) = geodesicIntegral g F + geodesicIntegral g G := by
  simp only [geodesicIntegral, SlashAction.add_slash, resToImagAxis_add, Pi.add_apply]
  rw [integral_add hF hG, mul_add]

/-- The geodesic integral is `ℂ`-linear in the integrand, for `g` of positive determinant (for
negative determinant the slash conjugates the scalar). -/
theorem _root_.Matrix.GeneralLinearGroup.geodesicIntegral_smul {g : GL (Fin 2) ℚ}
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det) (c : ℂ) (F : ℍ → ℂ) :
    geodesicIntegral g (c • F) = c * geodesicIntegral g F := by
  simp only [geodesicIntegral, ModularForm.rat_smul_slash_of_det_pos _ hg, resToImagAxis_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul]
  ring

/-! ### Independence of the parametrisation -/

/-- **Reparametrising the geodesic.** A diagonal matrix `d` of positive determinant fixes the
cusps `0` and `∞` and rescales the imaginary axis, so it does not change the geodesic integral
from `g • 0` to `g • ∞`. -/
theorem _root_.Matrix.GeneralLinearGroup.geodesicIntegral_mul_of_diagonal (g : GL (Fin 2) ℚ)
    {d : GL (Fin 2) ℚ} (h₁₀ : d 1 0 = 0) (h₀₁ : d 0 1 = 0)
    (hd : 0 < (d : Matrix (Fin 2) (Fin 2) ℚ).det) (F : ℍ → ℂ) :
    geodesicIntegral (g * d) F = geodesicIntegral g F := by
  rw [geodesicIntegral_mul, geodesicIntegral_def, geodesicIntegral_def]
  -- the axis is rescaled by the positive ratio `r = d₀₀ / d₁₁`
  have hr0 : (0 : ℝ) < d 0 0 / d 1 1 := by
    have hd' : 0 < d 0 0 * d 1 1 := by
      rw [Matrix.det_fin_two, h₁₀, h₀₁] at hd
      simpa using hd
    exact_mod_cast div_pos_iff.mpr (mul_pos_iff.mp hd')
  simp only [resToImagAxis_slash_two_of_diagonal _ h₁₀ h₀₁ hd]
  rw [integral_const_mul, integral_comp_mul_left_Ioi _ _ hr0, mul_zero, Complex.real_smul,
    Complex.ofReal_inv, mul_inv_cancel_left₀ (by exact_mod_cast hr0.ne')]

/-- **The geodesic integral only depends on the endpoints.** Two matrices of positive
determinant sending `(0, ∞)` to the same pair of cusps give the same integral. -/
theorem _root_.Matrix.GeneralLinearGroup.geodesicIntegral_eq_of_smul_eq {g g' : GL (Fin 2) ℚ}
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det) (hg' : 0 < (g' : Matrix (Fin 2) (Fin 2) ℚ).det)
    (h₀ : g • ((0 : ℚ) : OnePoint ℚ) = g' • ((0 : ℚ) : OnePoint ℚ))
    (hinf : g • (∞ : OnePoint ℚ) = g' • ∞) (F : ℍ → ℂ) :
    geodesicIntegral g F = geodesicIntegral g' F := by
  -- `d = g⁻¹ g'` fixes `0` and `∞`, hence is diagonal, and has positive determinant
  set d := g⁻¹ * g' with hd
  have hg'd : g' = g * d := by rw [hd, mul_inv_cancel_left]
  have hdinf : d • (∞ : OnePoint ℚ) = ∞ := by
    rw [hd, mul_smul, ← hinf, inv_smul_smul]
  have hd₀ : d • ((0 : ℚ) : OnePoint ℚ) = ((0 : ℚ) : OnePoint ℚ) := by
    rw [hd, mul_smul, ← h₀, inv_smul_smul]
  have h₁₀ : d 1 0 = 0 := OnePoint.smul_infty_eq_self_iff.mp hdinf
  have hdet : 0 < (d : Matrix (Fin 2) (Fin 2) ℚ).det := by
    have hmem : d ∈ GLPos (Fin 2) ℚ :=
      Subgroup.mul_mem _
        (Subgroup.inv_mem _ ((mem_glpos g).mpr (by rwa [Matrix.GeneralLinearGroup.val_det_apply])))
        ((mem_glpos g').mpr (by rwa [Matrix.GeneralLinearGroup.val_det_apply]))
    rw [mem_glpos, Matrix.GeneralLinearGroup.val_det_apply] at hmem
    exact hmem
  have h₁₁ : d 1 1 ≠ 0 := by
    intro h
    rw [Matrix.det_fin_two, h₁₀, h] at hdet
    simp at hdet
  have h₀₁ : d 0 1 = 0 := by
    rw [OnePoint.smul_some_eq_ite] at hd₀
    simp only [mul_zero, zero_add, h₁₁, ite_false, OnePoint.coe_eq_coe] at hd₀
    exact (div_eq_zero_iff.mp hd₀).resolve_right h₁₁
  rw [hg'd, geodesicIntegral_mul_of_diagonal g h₁₀ h₀₁ hdet]

/-! ### Reversing the orientation -/

/-- **Reversing the orientation of the geodesic**: `g S` sends `(0, ∞)` to `(g • ∞, g • 0)`, and
the integral from `g • ∞` to `g • 0` is the negative of the integral from `g • 0` to `g • ∞`. The
identity is the substitution `t ↦ 1 / t` on the imaginary axis and holds for every `g`; its
reading as an orientation reversal of a geodesic integral requires `0 < det g`. -/
theorem _root_.Matrix.GeneralLinearGroup.geodesicIntegral_mul_S (g : GL (Fin 2) ℚ) (F : ℍ → ℂ) :
    geodesicIntegral (g * mapGL ℚ S) F = -geodesicIntegral g F := by
  rw [geodesicIntegral_mul, geodesicIntegral, geodesicIntegral, ModularForm.rat_slash_mapGL,
    ← TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← ModularForm.SL_slash]
  set G := F ∣[(2 : ℤ)] g
  -- the substitution `t ↦ 1 / t` on the positive axis
  have hsub := integral_comp_rpow_Ioi (fun s ↦ -resToImagAxis G s) (by norm_num : (-1 : ℝ) ≠ 0)
  simp only [Complex.real_smul] at hsub
  have key : EqOn (fun t : ℝ ↦ resToImagAxis (G ∣[(2 : ℤ)] S) t)
      (fun t : ℝ ↦ ((|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1) : ℝ) : ℂ) * -resToImagAxis G (t ^ (-1 : ℝ)))
      (Ioi 0) := by
    intro t ht
    have ht : (0 : ℝ) < t := ht
    -- the Jacobian `|p| t ^ (p - 1)` of `t ↦ t ^ p` at `p = -1` is `t⁻²`
    have hexp : (-1 : ℝ) - 1 = -2 := by norm_num
    simp only
    rw [resToImagAxis_slash_two_S G ht, Real.rpow_neg_one, hexp, Real.rpow_neg ht.le,
      Real.rpow_two, abs_neg, abs_one, one_mul]
    push_cast
    ring
  rw [(setIntegral_congr_fun measurableSet_Ioi key).trans hsub, integral_neg, mul_neg]

end TauCeti

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Integrals.SqrtQuadratic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Sign.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Radial actions of the Kepler problem and the isotropic oscillator

A particle of mass `m > 0` in a central potential `U` with angular momentum `ℓ` moves radially in
the effective potential `U_ℓ(r) = ℓ² / (2 m r²) + U(r)`. At energy `E` its radial momentum is
`p_r = ±√(2 m (E - U_ℓ(r)))`, and the radial motion oscillates between two **turning points**
`0 < r₁ < r₂`, the zeros of `2 m (E - U_ℓ)`. Between them one has the classical quadratures:

* the **radial action** `I_r = (1 / π) ∫_{r₁}^{r₂} √(2 m (E - U_ℓ(r))) dr`, the area enclosed by
  the radial phase curve divided by `2π`;
* the **radial period** `T_r = 2 ∫_{r₁}^{r₂} dr / √((2 / m) (E - U_ℓ(r)))`;
* the **apsidal angle** `Δθ = ∫_{r₁}^{r₂} ℓ dr / (r² √(2 m (E - U_ℓ(r))))`, the polar angle swept
  from pericentre to apocentre.

This file evaluates them in closed form for the two potentials singled out by Bertrand's theorem,
whose bounded orbits are all closed. Each turning-point hypothesis is the equation
`2 m (E - U(rᵢ)) = ℓ² / rᵢ²`.

* **Kepler**, `U(r) = -κ / r`: `I_r = κ √(m / (-2 E)) - |ℓ|`, hence
  `E = -m κ² / (2 (I_r + |ℓ|)²)`; Kepler's third law `T_r = 2π √(m / κ) a^(3/2)` for the semi-major
  axis `a = (r₁ + r₂) / 2`; and `Δθ = π sign ℓ`, so the radial and angular frequencies agree up to
  the sign of `ℓ`.
* **Isotropic oscillator**, `U(r) = m ν² r² / 2`: `I_r = (E / ν - |ℓ|) / 2`, `T_r = π / ν` and
  `Δθ = (π / 2) sign ℓ`, so the radial frequency is twice the magnitude
  of the angular one.

In both cases the turning-point equations force `2 m (E - U_ℓ(r)) = c (r - r₁) (r₂ - r) / r²`
(in the variable `r²` for the oscillator), so every quadrature is one of the integrals of
`TauCeti.Analysis.SpecialFunctions.Integrals.SqrtQuadratic`.

## Main declarations

* `TauCeti.kepler_radialAction`, `TauCeti.kepler_energy_eq_radialAction`,
  `TauCeti.kepler_radialPeriod`, `TauCeti.kepler_apsidalAngle`.
* `TauCeti.isotropicOscillator_radialAction`, `TauCeti.isotropicOscillator_radialPeriod`,
  `TauCeti.isotropicOscillator_apsidalAngle`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 8 and 50.
* H. Goldstein, C. Poole, J. Safko, *Classical Mechanics*, 3rd ed., Addison-Wesley, 2002,
  Chapter 3 and Section 10.8.
-/

public section

open Real Set intervalIntegral

namespace TauCeti

variable {m κ ν ℓ E r₁ r₂ : ℝ}

/-- Substituting `u = r²` on an interval of positive radii. -/
private theorem integral_comp_sq_mul (h₁ : 0 < r₁) (hle : r₁ ≤ r₂) (g : ℝ → ℝ) :
    ∫ r in r₁..r₂, g (r ^ 2) * (2 * r) = ∫ u in r₁ ^ 2..r₂ ^ 2, g u := by
  refine integral_comp_mul_deriv_of_deriv_nonneg (f := fun r => r ^ 2) (by fun_prop)
    (fun x _ => by simpa using hasDerivAt_pow 2 x) fun x hx => ?_
  rw [min_eq_left hle] at hx
  linarith [hx.1]

/-! ### The Kepler problem -/

/-- Two distinct positive turning points of a Kepler orbit with `ℓ ≠ 0` force negative energy
and determine `κ` and `ℓ²` by Vieta's formulas. -/
private theorem kepler_vieta (hm : 0 < m) (hℓ : ℓ ≠ 0) (h₁ : 0 < r₁) (hlt : r₁ < r₂)
    (hr₁ : 2 * m * (E + κ / r₁) = ℓ ^ 2 / r₁ ^ 2)
    (hr₂ : 2 * m * (E + κ / r₂) = ℓ ^ 2 / r₂ ^ 2) :
    E < 0 ∧ κ = -E * (r₁ + r₂) ∧ ℓ ^ 2 = -2 * m * E * (r₁ * r₂) := by
  have h₂ : 0 < r₂ := h₁.trans hlt
  have q₁ : 2 * m * E * r₁ ^ 2 + 2 * m * κ * r₁ = ℓ ^ 2 := by
    rw [eq_div_iff (by positivity)] at hr₁
    rw [← hr₁]; field_simp
  have q₂ : 2 * m * E * r₂ ^ 2 + 2 * m * κ * r₂ = ℓ ^ 2 := by
    rw [eq_div_iff (by positivity)] at hr₂
    rw [← hr₂]; field_simp
  have hprod : (2 * m * (r₂ - r₁)) * (E * (r₁ + r₂) + κ) = 0 := by
    linear_combination q₂ - q₁
  have hκ : κ = -E * (r₁ + r₂) := by
    rcases mul_eq_zero.1 hprod with h | h
    · exact absurd h (mul_pos (mul_pos two_pos hm) (sub_pos.2 hlt)).ne'
    · linarith
  have hℓ2 : ℓ ^ 2 = -2 * m * E * (r₁ * r₂) := by linear_combination -q₁ + 2 * m * r₁ * hκ
  refine ⟨?_, hκ, hℓ2⟩
  by_contra hE
  have : 0 < ℓ ^ 2 := by positivity
  nlinarith [mul_nonneg (not_lt.1 hE) (mul_pos hm (mul_pos h₁ h₂)).le]

/-- Between the turning points,
`√(2 m (E + κ / r) - ℓ² / r²) = √(-2 m E) √((r - r₁) (r₂ - r)) / r`. -/
private theorem kepler_sqrt_eq (hm : 0 < m) (hκ : κ = -E * (r₁ + r₂))
    (hℓ2 : ℓ ^ 2 = -2 * m * E * (r₁ * r₂)) (hE : E < 0) {r : ℝ} (hr : 0 < r) :
    √(2 * m * (E + κ / r) - ℓ ^ 2 / r ^ 2) = √(-2 * m * E) * √((r - r₁) * (r₂ - r)) / r := by
  have : 2 * m * (E + κ / r) - ℓ ^ 2 / r ^ 2 = -2 * m * E * ((r - r₁) * (r₂ - r)) / r ^ 2 := by
    rw [hκ, hℓ2]; field_simp; ring
  rw [this, sqrt_div' _ (by positivity), sqrt_mul (by nlinarith), sqrt_sq hr.le]

/-- `√(-2 m E) = -2 E √(m / (-2 E))` for `E < 0`. -/
private theorem sqrt_neg_two_mul_mul (hm : 0 < m) (hE : E < 0) :
    √(-2 * m * E) = -2 * E * √(m / (-2 * E)) := by
  have h2E : 0 < -2 * E := by linarith
  calc √(-2 * m * E) = √((-2 * E) ^ 2 * (m / (-2 * E))) := by
        congr 1
        field_simp
    _ = -2 * E * √(m / (-2 * E)) := by rw [sqrt_mul (sq_nonneg _), sqrt_sq h2E.le]

/-- **The Kepler radial action.** Between two distinct turning points `0 < r₁ < r₂` of a Kepler
orbit of mass `m > 0` and angular momentum `ℓ ≠ 0` in the potential `-κ / r`, the radial action
is `(1 / π) ∫_{r₁}^{r₂} √(2 m (E + κ / r) - ℓ² / r²) dr = κ √(m / (-2 E)) - |ℓ|`. -/
theorem kepler_radialAction (hm : 0 < m) (hℓ : ℓ ≠ 0) (h₁ : 0 < r₁) (hlt : r₁ < r₂)
    (hr₁ : 2 * m * (E + κ / r₁) = ℓ ^ 2 / r₁ ^ 2) (hr₂ : 2 * m * (E + κ / r₂) = ℓ ^ 2 / r₂ ^ 2) :
    π⁻¹ * ∫ r in r₁..r₂, √(2 * m * (E + κ / r) - ℓ ^ 2 / r ^ 2) = κ * √(m / (-2 * E)) - |ℓ| := by
  obtain ⟨hE, hκ, hℓ2⟩ := kepler_vieta hm hℓ h₁ hlt hr₁ hr₂
  have hint : ∫ r in r₁..r₂, √(2 * m * (E + κ / r) - ℓ ^ 2 / r ^ 2) =
      √(-2 * m * E) * ∫ r in r₁..r₂, √((r - r₁) * (r₂ - r)) / r := by
    rw [← integral_const_mul]
    refine integral_congr fun r hr => ?_
    rw [uIcc_of_le hlt.le] at hr
    simp only [kepler_sqrt_eq hm hκ hℓ2 hE (h₁.trans_le hr.1), mul_div_assoc]
  have habs : √(-2 * m * E) * √(r₁ * r₂) = |ℓ| := by
    rw [← sqrt_mul (by nlinarith), ← sqrt_sq_eq_abs, hℓ2, mul_assoc]
  have hπ : π⁻¹ * (√(-2 * m * E) * (π * ((r₁ + r₂) / 2 - √(r₁ * r₂)))) =
      √(-2 * m * E) * (r₁ + r₂) / 2 - √(-2 * m * E) * √(r₁ * r₂) := by
    field_simp
  rw [hint, integral_sqrt_mul_sub_mul_sub_div h₁ hlt.le, hπ, habs, sqrt_neg_two_mul_mul hm hE, hκ]
  ring

/-- **The Kepler energy in terms of the actions.** With `I_r` the radial action of
`TauCeti.kepler_radialAction` and `ℓ` the angular action, `E = -m κ² / (2 (I_r + |ℓ|)²)`. -/
theorem kepler_energy_eq_radialAction (hm : 0 < m) (hℓ : ℓ ≠ 0) (h₁ : 0 < r₁) (hlt : r₁ < r₂)
    (hr₁ : 2 * m * (E + κ / r₁) = ℓ ^ 2 / r₁ ^ 2) (hr₂ : 2 * m * (E + κ / r₂) = ℓ ^ 2 / r₂ ^ 2) :
    E = -(m * κ ^ 2) /
      (2 * (π⁻¹ * (∫ r in r₁..r₂, √(2 * m * (E + κ / r) - ℓ ^ 2 / r ^ 2)) + |ℓ|) ^ 2) := by
  obtain ⟨hE, hκ, -⟩ := kepler_vieta hm hℓ h₁ hlt hr₁ hr₂
  have hκ0 : 0 < κ := by rw [hκ]; nlinarith
  rw [kepler_radialAction hm hℓ h₁ hlt hr₁ hr₂, sub_add_cancel, mul_pow,
    sq_sqrt (div_nonneg hm.le (by linarith))]
  field_simp

/-- **Kepler's third law.** Between two distinct turning points `0 < r₁ < r₂` of a Kepler orbit
with `ℓ ≠ 0`, the radial period `2 ∫_{r₁}^{r₂} dr / √((2 / m) (E + κ / r) - ℓ² / (m² r²))` is
`2π √(m / κ) a^(3/2)` for the semi-major axis `a = (r₁ + r₂) / 2`. -/
theorem kepler_radialPeriod (hm : 0 < m) (hℓ : ℓ ≠ 0) (h₁ : 0 < r₁) (hlt : r₁ < r₂)
    (hr₁ : 2 * m * (E + κ / r₁) = ℓ ^ 2 / r₁ ^ 2) (hr₂ : 2 * m * (E + κ / r₂) = ℓ ^ 2 / r₂ ^ 2) :
    2 * ∫ r in r₁..r₂, 1 / √(2 / m * (E + κ / r) - ℓ ^ 2 / (m ^ 2 * r ^ 2)) =
      2 * π * √(m / κ) * ((r₁ + r₂) / 2) ^ (3 / 2 : ℝ) := by
  obtain ⟨hE, hκ, hℓ2⟩ := kepler_vieta hm hℓ h₁ hlt hr₁ hr₂
  have hκ0 : 0 < κ := by rw [hκ]; nlinarith
  have ha : 0 < (r₁ + r₂) / 2 := by linarith
  have hint : ∫ r in r₁..r₂, 1 / √(2 / m * (E + κ / r) - ℓ ^ 2 / (m ^ 2 * r ^ 2)) =
      m / √(-2 * m * E) * ∫ r in r₁..r₂, r / √((r - r₁) * (r₂ - r)) := by
    rw [← integral_const_mul]
    refine integral_congr fun r hr => ?_
    rw [uIcc_of_le hlt.le] at hr
    have hr0 : 0 < r := h₁.trans_le hr.1
    have : 2 / m * (E + κ / r) - ℓ ^ 2 / (m ^ 2 * r ^ 2) =
        (2 * m * (E + κ / r) - ℓ ^ 2 / r ^ 2) / m ^ 2 := by
      field_simp
    rw [this, sqrt_div' _ (by positivity), sqrt_sq hm.le, kepler_sqrt_eq hm hκ hℓ2 hE hr0]
    have : 0 < √(-2 * m * E) := sqrt_pos.2 (by nlinarith)
    field_simp
  rw [hint, integral_div_sqrt_mul_sub_mul_sub hlt,
    show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, rpow_add ha, rpow_one, ← sqrt_eq_rpow]
  have hm' : m / √(-2 * m * E) = √(m / κ) * √((r₁ + r₂) / 2) := by
    rw [← sqrt_mul (div_nonneg hm.le hκ0.le)]
    nth_rw 1 [← sqrt_sq hm.le]
    rw [← sqrt_div' _ (by nlinarith)]
    congr 1
    have hs : r₁ + r₂ ≠ 0 := by linarith
    rw [hκ]
    field_simp
  rw [hm']
  ring

/-- **The Kepler apsidal angle.** Between two distinct turning points `0 < r₁ < r₂` of a Kepler
orbit with `ℓ ≠ 0`, the polar angle swept from pericentre to apocentre,
`∫_{r₁}^{r₂} ℓ dr / (r² √(2 m (E + κ / r) - ℓ² / r²))`, is `π sign ℓ`: the orbit closes after one
radial period, with no precession of its apsides. -/
theorem kepler_apsidalAngle (hm : 0 < m) (hℓ : ℓ ≠ 0) (h₁ : 0 < r₁) (hlt : r₁ < r₂)
    (hr₁ : 2 * m * (E + κ / r₁) = ℓ ^ 2 / r₁ ^ 2) (hr₂ : 2 * m * (E + κ / r₂) = ℓ ^ 2 / r₂ ^ 2) :
    ∫ r in r₁..r₂, ℓ / (r ^ 2 * √(2 * m * (E + κ / r) - ℓ ^ 2 / r ^ 2)) =
      π * SignType.sign ℓ := by
  obtain ⟨hE, hκ, hℓ2⟩ := kepler_vieta hm hℓ h₁ hlt hr₁ hr₂
  have hint : ∫ r in r₁..r₂, ℓ / (r ^ 2 * √(2 * m * (E + κ / r) - ℓ ^ 2 / r ^ 2)) =
      ℓ / √(-2 * m * E) * ∫ r in r₁..r₂, 1 / (r * √((r - r₁) * (r₂ - r))) := by
    rw [← integral_const_mul]
    refine integral_congr fun r hr => ?_
    rw [uIcc_of_le hlt.le] at hr
    have hr0 : 0 < r := h₁.trans_le hr.1
    rw [kepler_sqrt_eq hm hκ hℓ2 hE hr0,
      show r ^ 2 * (√(-2 * m * E) * √((r - r₁) * (r₂ - r)) / r) =
        r * (√(-2 * m * E) * √((r - r₁) * (r₂ - r))) by field_simp]
    ring
  have habs : √(-2 * m * E) * √(r₁ * r₂) = |ℓ| := by
    rw [← sqrt_mul (by nlinarith), ← sqrt_sq_eq_abs, hℓ2, mul_assoc]
  rw [hint, integral_one_div_mul_sqrt_mul_sub_mul_sub h₁ hlt]
  nth_rw 1 [← sign_mul_abs ℓ]
  rw [← habs]
  have hc : 0 < √(-2 * m * E) := sqrt_pos.2 (by nlinarith)
  have : 0 < √(r₁ * r₂) := sqrt_pos.2 (mul_pos h₁ (h₁.trans hlt))
  generalize √(-2 * m * E) = c at hc ⊢
  field_simp

/-! ### The isotropic oscillator -/

/-- Two distinct positive turning points of an isotropic oscillator determine `E` and `ℓ²` by
Vieta's formulas in the variable `r²`. -/
private theorem isotropicOscillator_vieta (hm : 0 < m) (h₁ : 0 < r₁) (hlt : r₁ < r₂)
    (hr₁ : 2 * m * (E - m * ν ^ 2 * r₁ ^ 2 / 2) = ℓ ^ 2 / r₁ ^ 2)
    (hr₂ : 2 * m * (E - m * ν ^ 2 * r₂ ^ 2 / 2) = ℓ ^ 2 / r₂ ^ 2) :
    2 * E = m * ν ^ 2 * (r₁ ^ 2 + r₂ ^ 2) ∧ ℓ ^ 2 = (m * ν * (r₁ * r₂)) ^ 2 := by
  have h₂ : 0 < r₂ := h₁.trans hlt
  have q₁ : 2 * m * E * r₁ ^ 2 - m ^ 2 * ν ^ 2 * r₁ ^ 4 = ℓ ^ 2 := by
    rw [eq_div_iff (by positivity)] at hr₁
    rw [← hr₁]; ring
  have q₂ : 2 * m * E * r₂ ^ 2 - m ^ 2 * ν ^ 2 * r₂ ^ 4 = ℓ ^ 2 := by
    rw [eq_div_iff (by positivity)] at hr₂
    rw [← hr₂]; ring
  have hprod : (m * (r₂ ^ 2 - r₁ ^ 2)) * (2 * E - m * ν ^ 2 * (r₁ ^ 2 + r₂ ^ 2)) = 0 := by
    linear_combination q₂ - q₁
  have hE : 2 * E = m * ν ^ 2 * (r₁ ^ 2 + r₂ ^ 2) := by
    rcases mul_eq_zero.1 hprod with h | h
    · exact absurd h (mul_pos hm (by nlinarith)).ne'
    · linarith
  exact ⟨hE, by linear_combination -q₁ + m * r₁ ^ 2 * hE⟩

/-- Between the turning points,
`√(2 m (E - m ν² r² / 2) - ℓ² / r²) = m ν √((r² - r₁²) (r₂² - r²)) / r`. -/
private theorem isotropicOscillator_sqrt_eq (hm : 0 < m) (hν : 0 < ν)
    (hE : 2 * E = m * ν ^ 2 * (r₁ ^ 2 + r₂ ^ 2)) (hℓ2 : ℓ ^ 2 = (m * ν * (r₁ * r₂)) ^ 2)
    {r : ℝ} (hr : 0 < r) :
    √(2 * m * (E - m * ν ^ 2 * r ^ 2 / 2) - ℓ ^ 2 / r ^ 2) =
      m * ν * √((r ^ 2 - r₁ ^ 2) * (r₂ ^ 2 - r ^ 2)) / r := by
  have : 2 * m * (E - m * ν ^ 2 * r ^ 2 / 2) - ℓ ^ 2 / r ^ 2 =
      (m * ν) ^ 2 * ((r ^ 2 - r₁ ^ 2) * (r₂ ^ 2 - r ^ 2)) / r ^ 2 := by
    rw [hℓ2, show E = m * ν ^ 2 * (r₁ ^ 2 + r₂ ^ 2) / 2 by linarith]
    field_simp
    ring
  rw [this, sqrt_div' _ (by positivity), sqrt_mul (by positivity), sqrt_sq (by positivity),
    sqrt_sq hr.le]

/-- **The radial action of the isotropic oscillator.** Between two distinct turning points
`0 < r₁ < r₂` of a particle of mass `m > 0` in the potential `m ν² r² / 2` with `ν > 0`, the
radial action is
`(1 / π) ∫_{r₁}^{r₂} √(2 m (E - m ν² r² / 2) - ℓ² / r²) dr = (E / ν - |ℓ|) / 2`. -/
theorem isotropicOscillator_radialAction (hm : 0 < m) (hν : 0 < ν) (h₁ : 0 < r₁)
    (hlt : r₁ < r₂) (hr₁ : 2 * m * (E - m * ν ^ 2 * r₁ ^ 2 / 2) = ℓ ^ 2 / r₁ ^ 2)
    (hr₂ : 2 * m * (E - m * ν ^ 2 * r₂ ^ 2 / 2) = ℓ ^ 2 / r₂ ^ 2) :
    π⁻¹ * ∫ r in r₁..r₂, √(2 * m * (E - m * ν ^ 2 * r ^ 2 / 2) - ℓ ^ 2 / r ^ 2) =
      (E / ν - |ℓ|) / 2 := by
  obtain ⟨hE, hℓ2⟩ := isotropicOscillator_vieta hm h₁ hlt hr₁ hr₂
  have h₂ : 0 < r₂ := h₁.trans hlt
  have hint : ∫ r in r₁..r₂, √(2 * m * (E - m * ν ^ 2 * r ^ 2 / 2) - ℓ ^ 2 / r ^ 2) =
      m * ν / 2 * ∫ r in r₁..r₂,
        (fun u => √((u - r₁ ^ 2) * (r₂ ^ 2 - u)) / u) (r ^ 2) * (2 * r) := by
    rw [← integral_const_mul]
    refine integral_congr fun r hr => ?_
    rw [uIcc_of_le hlt.le] at hr
    have hr0 : 0 < r := h₁.trans_le hr.1
    rw [isotropicOscillator_sqrt_eq hm hν hE hℓ2 hr0]
    field_simp
  have habs : |ℓ| = m * ν * (r₁ * r₂) := by
    rw [← sqrt_sq_eq_abs, hℓ2, sqrt_sq (by positivity)]
  rw [hint, integral_comp_sq_mul h₁ hlt.le (fun u => √((u - r₁ ^ 2) * (r₂ ^ 2 - u)) / u),
    integral_sqrt_mul_sub_mul_sub_div (by positivity)
    (by nlinarith), ← mul_pow, sqrt_sq (by positivity), habs,
    show E = m * ν ^ 2 * (r₁ ^ 2 + r₂ ^ 2) / 2 by linarith]
  field_simp

/-- **The radial period of the isotropic oscillator.** Between two distinct turning points
`0 < r₁ < r₂` in the potential `m ν² r² / 2` with `ν > 0`, the radial period
`2 ∫_{r₁}^{r₂} dr / √((2 / m) (E - m ν² r² / 2) - ℓ² / (m² r²))` is `π / ν`, half the period
`2π / ν` of the oscillator. -/
theorem isotropicOscillator_radialPeriod (hm : 0 < m) (hν : 0 < ν) (h₁ : 0 < r₁)
    (hlt : r₁ < r₂) (hr₁ : 2 * m * (E - m * ν ^ 2 * r₁ ^ 2 / 2) = ℓ ^ 2 / r₁ ^ 2)
    (hr₂ : 2 * m * (E - m * ν ^ 2 * r₂ ^ 2 / 2) = ℓ ^ 2 / r₂ ^ 2) :
    2 * ∫ r in r₁..r₂, 1 / √(2 / m * (E - m * ν ^ 2 * r ^ 2 / 2) - ℓ ^ 2 / (m ^ 2 * r ^ 2)) =
      π / ν := by
  obtain ⟨hE, hℓ2⟩ := isotropicOscillator_vieta hm h₁ hlt hr₁ hr₂
  have hint : ∫ r in r₁..r₂,
      1 / √(2 / m * (E - m * ν ^ 2 * r ^ 2 / 2) - ℓ ^ 2 / (m ^ 2 * r ^ 2)) =
      1 / (2 * ν) * ∫ r in r₁..r₂,
        (fun u => 1 / √((u - r₁ ^ 2) * (r₂ ^ 2 - u))) (r ^ 2) * (2 * r) := by
    rw [← integral_const_mul]
    refine integral_congr fun r hr => ?_
    rw [uIcc_of_le hlt.le] at hr
    have hr0 : 0 < r := h₁.trans_le hr.1
    have : 2 / m * (E - m * ν ^ 2 * r ^ 2 / 2) - ℓ ^ 2 / (m ^ 2 * r ^ 2) =
        (2 * m * (E - m * ν ^ 2 * r ^ 2 / 2) - ℓ ^ 2 / r ^ 2) / m ^ 2 := by
      field_simp
    rw [this, sqrt_div' _ (by positivity), sqrt_sq hm.le,
      isotropicOscillator_sqrt_eq hm hν hE hℓ2 hr0]
    field_simp
  rw [hint, integral_comp_sq_mul h₁ hlt.le (fun u => 1 / √((u - r₁ ^ 2) * (r₂ ^ 2 - u))),
    integral_one_div_sqrt_mul_sub_mul_sub (pow_lt_pow_left₀ hlt h₁.le two_ne_zero)]
  field_simp

/-- **The apsidal angle of the isotropic oscillator.** Between two distinct turning points
`0 < r₁ < r₂` in the potential `m ν² r² / 2` with `ν > 0`, the polar angle swept from pericentre
to apocentre, `∫_{r₁}^{r₂} ℓ dr / (r² √(2 m (E - m ν² r² / 2) - ℓ² / r²))`, is `(π / 2) sign ℓ`:
the orbit closes after two radial periods. -/
theorem isotropicOscillator_apsidalAngle (hm : 0 < m) (hν : 0 < ν) (h₁ : 0 < r₁)
    (hlt : r₁ < r₂) (hr₁ : 2 * m * (E - m * ν ^ 2 * r₁ ^ 2 / 2) = ℓ ^ 2 / r₁ ^ 2)
    (hr₂ : 2 * m * (E - m * ν ^ 2 * r₂ ^ 2 / 2) = ℓ ^ 2 / r₂ ^ 2) :
    ∫ r in r₁..r₂, ℓ / (r ^ 2 * √(2 * m * (E - m * ν ^ 2 * r ^ 2 / 2) - ℓ ^ 2 / r ^ 2)) =
      π / 2 * SignType.sign ℓ := by
  obtain ⟨hE, hℓ2⟩ := isotropicOscillator_vieta hm h₁ hlt hr₁ hr₂
  have h₂ : 0 < r₂ := h₁.trans hlt
  have hint : ∫ r in r₁..r₂,
      ℓ / (r ^ 2 * √(2 * m * (E - m * ν ^ 2 * r ^ 2 / 2) - ℓ ^ 2 / r ^ 2)) =
      ℓ / (2 * m * ν) * ∫ r in r₁..r₂,
        (fun u => 1 / (u * √((u - r₁ ^ 2) * (r₂ ^ 2 - u)))) (r ^ 2) * (2 * r) := by
    rw [← integral_const_mul]
    refine integral_congr fun r hr => ?_
    rw [uIcc_of_le hlt.le] at hr
    have hr0 : 0 < r := h₁.trans_le hr.1
    rw [isotropicOscillator_sqrt_eq hm hν hE hℓ2 hr0,
      show r ^ 2 * (m * ν * √((r ^ 2 - r₁ ^ 2) * (r₂ ^ 2 - r ^ 2)) / r) =
        r * (m * ν * √((r ^ 2 - r₁ ^ 2) * (r₂ ^ 2 - r ^ 2))) by field_simp]
    field_simp
  have habs : |ℓ| = m * ν * (r₁ * r₂) := by
    rw [← sqrt_sq_eq_abs, hℓ2, sqrt_sq (by positivity)]
  rw [hint, integral_comp_sq_mul h₁ hlt.le (fun u => 1 / (u * √((u - r₁ ^ 2) * (r₂ ^ 2 - u)))),
    integral_one_div_mul_sqrt_mul_sub_mul_sub
    (by positivity) (pow_lt_pow_left₀ hlt h₁.le two_ne_zero), ← mul_pow, sqrt_sq (by positivity)]
  nth_rw 1 [← sign_mul_abs ℓ]
  rw [habs]
  field_simp

end TauCeti

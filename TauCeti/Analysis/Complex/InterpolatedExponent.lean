/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Data.ENNReal.InterpolatedExponent

/-!
# The exponent of the analytic families of complex interpolation

Thorin's proof of the Riesz–Thorin theorem and Calderón's identification of the complex
interpolation spaces of `Lᵖ` spaces both embed a function `f` of `Lᵖ` norm one in the analytic
family `z ↦ sgn(f) |f| ^ {P(z)}`, where `P` is an affine function of `z` with `P(θ) = 1`, chosen
so that on the line `Re z = j` the function `|f| ^ {Re P(z)}` has norm one in `L^{p_j}`. With the
reciprocal exponents `a₀ = 1 / p₀`, `a₁ = 1 / p₁` and `a = (1 - θ) a₀ + θ a₁ = 1 / p`, this is

`P(z) = 1 + (z - θ) (a₁ - a₀) / a`,

`TauCeti.interpExponent a₀ a₁ θ z`. Its real part interpolates the reciprocal exponents: if
`a ≠ 0` then `Re P(z) · a = (1 - Re z) a₀ + Re z a₁`, that is
`Re P(z) = ((1 - Re z) a₀ + Re z a₁) / a` (`TauCeti.re_interpExponent_mul_of_ne_zero`). If `a = 0`
the slope `(a₁ - a₀) / a` is `0` by the convention `x / 0 = 0`, and `P` is constantly `1`
(`TauCeti.interpExponent_of_eq_zero`); for `a₀, a₁ ≥ 0` and `0 < θ < 1` this happens only when
`a₀ = a₁ = 0`, so the identity `Re P(z) · a = (1 - Re z) a₀ + Re z a₁` still holds
(`TauCeti.re_interpExponent_mul`).

## Main declarations

* `TauCeti.interpSlope` and `TauCeti.interpExponent`: the slope `(a₁ - a₀) / a` and the exponent
  `1 + (z - θ) (a₁ - a₀) / a`, an entire function of `z` equal to `1` at `θ`.
* `TauCeti.re_interpExponent_mul_of_ne_zero`, `TauCeti.re_interpExponent_mul`:
  `Re P(z) · a = (1 - Re z) a₀ + Re z a₁`, for `a ≠ 0` or for `a₀, a₁ ≥ 0` and `0 < θ < 1`.
* `TauCeti.re_interpExponent_nonneg`, `TauCeti.abs_re_interpExponent_le`: on the closed strip
  `0 ≤ Re z ≤ 1` the real part of `P` is nonnegative and bounded.
* `TauCeti.ofReal_re_interpExponent_mul_inv`: for an interpolated exponent
  `1 / s = (1 - θ) / s₀ + θ / s₁`, the exponent `1 / s(z) = Re P(z) / s` interpolates `1 / s₀` and
  `1 / s₁` with the weight `Re z`; in particular it is `1 / s₀` on the line `Re z = 0` and `1 / s₁`
  on the line `Re z = 1` (`TauCeti.ofReal_re_interpExponent_mul_inv_of_re_eq_zero`,
  `TauCeti.ofReal_re_interpExponent_mul_inv_of_re_eq_one`).

## References

* G. O. Thorin, *An extension of a convexity theorem due to M. Riesz*, Kungl. Fysiogr. Sällsk.
  i Lund Förh. 8 (1939).
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §1.1 and §5.1.
-/

public section

open Complex
open scoped ENNReal

namespace TauCeti

/-- The slope `(a₁ - a₀) / a` of the exponent of the analytic families of complex interpolation,
where `a = (1 - θ) a₀ + θ a₁`. -/
noncomputable def interpSlope (a₀ a₁ θ : ℝ) : ℝ := (a₁ - a₀) / ((1 - θ) * a₀ + θ * a₁)

theorem interpSlope_def (a₀ a₁ θ : ℝ) :
    interpSlope a₀ a₁ θ = (a₁ - a₀) / ((1 - θ) * a₀ + θ * a₁) :=
  (rfl)

/-- Equal reciprocal exponents give the slope `0`. -/
@[simp]
theorem interpSlope_same (a θ : ℝ) : interpSlope a a θ = 0 := by
  simp [interpSlope_def]

theorem interpSlope_of_eq_zero {a₀ a₁ θ : ℝ} (ha : (1 - θ) * a₀ + θ * a₁ = 0) :
    interpSlope a₀ a₁ θ = 0 := by
  rw [interpSlope_def, ha, div_zero]

/-- The exponent `1 + (z - θ) (a₁ - a₀) / a` of the analytic families of complex interpolation,
where `a = (1 - θ) a₀ + θ a₁`. It equals `1` at `z = θ` (`TauCeti.interpExponent_self`). If
`a ≠ 0`, its real part is `a₀ / a` on the line `Re z = 0` and `a₁ / a` on the line `Re z = 1`
(`TauCeti.re_interpExponent_mul_of_ne_zero`). If `a = 0` the exponent is constantly `1`
(`TauCeti.interpExponent_of_eq_zero`); for `a₀, a₁ ≥ 0` and `0 < θ < 1` this happens only when
`a₀ = a₁ = 0`. -/
noncomputable def interpExponent (a₀ a₁ θ : ℝ) (z : ℂ) : ℂ :=
  1 + (z - θ) * (interpSlope a₀ a₁ θ : ℂ)

theorem interpExponent_def (a₀ a₁ θ : ℝ) (z : ℂ) :
    interpExponent a₀ a₁ θ z = 1 + (z - θ) * (interpSlope a₀ a₁ θ : ℂ) :=
  (rfl)

@[fun_prop]
theorem differentiable_interpExponent (a₀ a₁ θ : ℝ) :
    Differentiable ℂ (interpExponent a₀ a₁ θ) := by
  have h : interpExponent a₀ a₁ θ = fun z => 1 + (z - θ) * (interpSlope a₀ a₁ θ : ℂ) :=
    funext (interpExponent_def a₀ a₁ θ)
  rw [h]
  fun_prop

@[fun_prop]
theorem continuous_interpExponent (a₀ a₁ θ : ℝ) : Continuous (interpExponent a₀ a₁ θ) :=
  (differentiable_interpExponent a₀ a₁ θ).continuous

theorem re_interpExponent (a₀ a₁ θ : ℝ) (z : ℂ) :
    (interpExponent a₀ a₁ θ z).re = 1 + (z.re - θ) * interpSlope a₀ a₁ θ := by
  simp [interpExponent_def]

@[simp]
theorem interpExponent_self (a₀ a₁ θ : ℝ) : interpExponent a₀ a₁ θ θ = 1 := by
  simp [interpExponent_def]

/-- For equal reciprocal exponents the exponent is constantly `1`. -/
@[simp]
theorem interpExponent_same (a θ : ℝ) (z : ℂ) : interpExponent a a θ z = 1 := by
  simp [interpExponent_def]

/-- If `(1 - θ) a₀ + θ a₁ = 0` the exponent is constantly `1`. -/
theorem interpExponent_of_eq_zero {a₀ a₁ θ : ℝ} (ha : (1 - θ) * a₀ + θ * a₁ = 0) (z : ℂ) :
    interpExponent a₀ a₁ θ z = 1 := by
  simp [interpExponent_def, interpSlope_of_eq_zero ha]

/-- If `a = (1 - θ) a₀ + θ a₁ ≠ 0`, the real part of the exponent interpolates the reciprocal
exponents: `Re P(z) · a = (1 - Re z) a₀ + Re z a₁`. -/
theorem re_interpExponent_mul_of_ne_zero {a₀ a₁ θ : ℝ} (ha : (1 - θ) * a₀ + θ * a₁ ≠ 0)
    (z : ℂ) :
    (interpExponent a₀ a₁ θ z).re * ((1 - θ) * a₀ + θ * a₁) = (1 - z.re) * a₀ + z.re * a₁ := by
  rw [re_interpExponent, interpSlope_def, add_mul, one_mul, mul_assoc, div_mul_cancel₀ _ ha]
  ring

/-- The real part of the exponent interpolates nonnegative reciprocal exponents:
`Re P(z) · ((1 - θ) a₀ + θ a₁) = (1 - Re z) a₀ + Re z a₁`. -/
theorem re_interpExponent_mul {a₀ a₁ θ : ℝ} (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) (z : ℂ) :
    (interpExponent a₀ a₁ θ z).re * ((1 - θ) * a₀ + θ * a₁) = (1 - z.re) * a₀ + z.re * a₁ := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  rcases eq_or_ne ((1 - θ) * a₀ + θ * a₁) 0 with ha | ha
  · obtain ⟨rfl, rfl⟩ : a₀ = 0 ∧ a₁ = 0 := by
      constructor <;> nlinarith [mul_nonneg (sub_pos.2 hθ1).le ha₀, mul_nonneg hθ0.le ha₁]
    simp
  · exact re_interpExponent_mul_of_ne_zero ha z

/-- On the closed strip `0 ≤ Re z ≤ 1` the real part of the exponent is nonnegative. -/
theorem re_interpExponent_nonneg {a₀ a₁ θ : ℝ} (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    {z : ℂ} (hz : z.re ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ (interpExponent a₀ a₁ θ z).re := by
  rcases eq_or_ne ((1 - θ) * a₀ + θ * a₁) 0 with ha | ha
  · simp [interpExponent_of_eq_zero ha]
  · have hpos : 0 < (1 - θ) * a₀ + θ * a₁ := lt_of_le_of_ne
      (add_nonneg (mul_nonneg (sub_nonneg.2 hθ.2) ha₀) (mul_nonneg hθ.1 ha₁)) ha.symm
    have h : 0 ≤ (1 - z.re) * a₀ + z.re * a₁ :=
      add_nonneg (mul_nonneg (sub_nonneg.2 hz.2) ha₀) (mul_nonneg hz.1 ha₁)
    rw [← re_interpExponent_mul_of_ne_zero ha z] at h
    exact nonneg_of_mul_nonneg_left h hpos

/-- On the closed strip `0 ≤ Re z ≤ 1` the real part of the exponent is bounded independently
of `z`. -/
theorem abs_re_interpExponent_le {a₀ a₁ θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) {z : ℂ}
    (hz : z.re ∈ Set.Icc (0 : ℝ) 1) :
    |(interpExponent a₀ a₁ θ z).re| ≤ 1 + |interpSlope a₀ a₁ θ| := by
  rw [re_interpExponent]
  have h1 : |z.re - θ| ≤ 1 := abs_le.2 ⟨by linarith [hz.1, hθ.2], by linarith [hz.2, hθ.1]⟩
  calc _ ≤ |(1 : ℝ)| + |(z.re - θ) * interpSlope a₀ a₁ θ| := abs_add_le _ _
    _ ≤ 1 + 1 * |interpSlope a₀ a₁ θ| := by
        rw [abs_one, abs_mul]; gcongr
    _ = _ := by ring

variable {s₀ s₁ s : ℝ≥0∞} {θ : ℝ}

/-- For an interpolated exponent `1 / s = (1 - θ) / s₀ + θ / s₁`, the exponent
`1 / s(z) = Re P(z) / s` of the analytic family at a point `z` of the closed strip interpolates
`1 / s₀` and `1 / s₁` with the weight `Re z`. -/
theorem ofReal_re_interpExponent_mul_inv (hs₀ : s₀ ≠ 0) (hs₁ : s₁ ≠ 0)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s⁻¹ = ENNReal.ofReal (1 - θ) * s₀⁻¹ + ENNReal.ofReal θ * s₁⁻¹) {z : ℂ}
    (hz : z.re ∈ Set.Icc (0 : ℝ) 1) :
    ENNReal.ofReal (interpExponent (s₀⁻¹).toReal (s₁⁻¹).toReal θ z).re * s⁻¹ =
      ENNReal.ofReal (1 - z.re) * s₀⁻¹ + ENNReal.ofReal z.re * s₁⁻¹ := by
  have h₀ : s₀⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hs₀
  have h₁ : s₁⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hs₁
  have hz1 : 0 ≤ 1 - z.re := sub_nonneg.2 hz.2
  have hre := re_interpExponent_mul (ENNReal.toReal_nonneg (a := s₀⁻¹))
    (ENNReal.toReal_nonneg (a := s₁⁻¹)) hθ z
  have hnn := re_interpExponent_nonneg (ENNReal.toReal_nonneg (a := s₀⁻¹))
    (ENNReal.toReal_nonneg (a := s₁⁻¹)) (Set.Ioo_subset_Icc_self hθ) hz
  have h0 : (0 : ℝ) ≤ (s₀⁻¹).toReal := ENNReal.toReal_nonneg
  have h1 : (0 : ℝ) ≤ (s₁⁻¹).toReal := ENNReal.toReal_nonneg
  rw [inv_eq_ofReal_of_inv_eq hs₀ hs₁ (Set.Ioo_subset_Icc_self hθ) hs, ← ENNReal.ofReal_mul hnn,
    hre, ENNReal.ofReal_add (mul_nonneg hz1 h0) (mul_nonneg hz.1 h1),
    ENNReal.ofReal_mul hz1, ENNReal.ofReal_mul hz.1, ENNReal.ofReal_toReal h₀,
    ENNReal.ofReal_toReal h₁]

/-- On the line `Re z = 0` the exponent `1 / s(z) = Re P(z) / s` of the analytic family is
`1 / s₀`. -/
theorem ofReal_re_interpExponent_mul_inv_of_re_eq_zero (hs₀ : s₀ ≠ 0) (hs₁ : s₁ ≠ 0)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s⁻¹ = ENNReal.ofReal (1 - θ) * s₀⁻¹ + ENNReal.ofReal θ * s₁⁻¹) {z : ℂ}
    (hz : z.re = 0) :
    ENNReal.ofReal (interpExponent (s₀⁻¹).toReal (s₁⁻¹).toReal θ z).re * s⁻¹ = s₀⁻¹ := by
  rw [ofReal_re_interpExponent_mul_inv hs₀ hs₁ hθ hs (by simp [hz]), hz]
  simp

/-- On the line `Re z = 1` the exponent `1 / s(z) = Re P(z) / s` of the analytic family is
`1 / s₁`. -/
theorem ofReal_re_interpExponent_mul_inv_of_re_eq_one (hs₀ : s₀ ≠ 0) (hs₁ : s₁ ≠ 0)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s⁻¹ = ENNReal.ofReal (1 - θ) * s₀⁻¹ + ENNReal.ofReal θ * s₁⁻¹) {z : ℂ}
    (hz : z.re = 1) :
    ENNReal.ofReal (interpExponent (s₀⁻¹).toReal (s₁⁻¹).toReal θ z).re * s⁻¹ = s₁⁻¹ := by
  rw [ofReal_re_interpExponent_mul_inv hs₀ hs₁ hθ hs (by simp [hz]), hz]
  simp

end TauCeti

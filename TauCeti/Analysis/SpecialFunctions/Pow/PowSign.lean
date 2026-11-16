/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.ENNReal.Real
import TauCeti.Data.ENNReal.InterpolatedExponent

/-!
# Complex powers of the modulus with the sign kept

For a vector `c` in a complex normed space and `w ∈ ℂ`, `TauCeti.powSign w c = ‖c‖ ^ (w - 1) • c`
is `sgn(c) |c| ^ w`: it keeps the direction of `c` and replaces its length by the complex power
`‖c‖ ^ w`, with `powSign w 0 = 0`. It is entire in `w`, equals `c` at `w = 1`
(`TauCeti.powSign_one`) and has norm `‖c‖ ^ re w` (`TauCeti.norm_powSign_le`). Applied pointwise to
a function `f`, it gives Thorin's analytic family `sgn(f) |f| ^ w` through `f`, used to prove the
Riesz–Thorin theorem and to compute the complex interpolation spaces of the Lebesgue couple.

The exponent of that family is `TauCeti.thorinExponent a₀ a₁ θ z = 1 + (z - θ) (a₁ - a₀) / a`,
where `a = (1 - θ) a₀ + θ a₁`: it equals `1` at `z = θ` (`TauCeti.thorinExponent_self`), so the
family passes through `f`, and, for interpolated exponents `1 / s = (1 - θ) / s₀ + θ / s₁` with
`a₀ = 1 / s₀` and `a₁ = 1 / s₁`, its real part satisfies `re w / s = (1 - re z) / s₀ + re z / s₁`
(`TauCeti.ofReal_re_thorinExponent_mul_inv`). On the line `re z = j` the family therefore lies in
`L^{sⱼ}` when `f` lies in `Lˢ`.
-/

public section

open Complex

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- `powSign w c = ‖c‖ ^ (w - 1) • c`, the value at `c` of the analytic family `sgn(f) |f| ^ w`.
The convention `Real.log 0 = 0` gives `powSign w 0 = 0`. -/
noncomputable def powSign (w : ℂ) (c : E) : E :=
  exp ((w - 1) * Real.log ‖c‖) • c

theorem powSign_def (w : ℂ) (c : E) : powSign w c = exp ((w - 1) * Real.log ‖c‖) • c :=
  (rfl)

@[simp]
theorem powSign_one (c : E) : powSign 1 c = c := by
  simp [powSign]

@[simp]
theorem powSign_zero_right (w : ℂ) : powSign w (0 : E) = 0 := by
  simp [powSign]

theorem powSign_ne_zero (w : ℂ) {c : E} (hc : c ≠ 0) : powSign w c ≠ 0 :=
  smul_ne_zero (exp_ne_zero _) hc

theorem norm_powSign (w : ℂ) {c : E} (hc : c ≠ 0) : ‖powSign w c‖ = ‖c‖ ^ w.re := by
  have hpos : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hre : ((w - 1) * (Real.log ‖c‖ : ℂ)).re = Real.log ‖c‖ * (w.re - 1) := by
    simp [mul_comm]
  rw [powSign, norm_smul, norm_exp, hre, ← Real.rpow_def_of_pos hpos,
    Real.rpow_sub_one hpos.ne', div_mul_cancel₀ _ hpos.ne']

theorem norm_powSign_le (w : ℂ) (c : E) : ‖powSign w c‖ ≤ ‖c‖ ^ w.re := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [Real.rpow_nonneg]
  · exact (norm_powSign w hc).le

theorem norm_powSign_le_exp (w : ℂ) (c : E) :
    ‖powSign w c‖ ≤ Real.exp (|w.re| * |Real.log ‖c‖|) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have hpos : 0 < ‖c‖ := norm_pos_iff.2 hc
    rw [norm_powSign w hc, Real.rpow_def_of_pos hpos, mul_comm]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans (abs_mul _ _).le)

/-! ### The exponent of the analytic family -/

/-- The slope `(a₁ - a₀) / a` of the exponent of Thorin's analytic family, where
`a = (1 - θ) a₀ + θ a₁`. -/
noncomputable def thorinSlope (a₀ a₁ θ : ℝ) : ℝ := (a₁ - a₀) / ((1 - θ) * a₀ + θ * a₁)

/-- The exponent `1 + (z - θ) (a₁ - a₀) / a` of Thorin's analytic family, where
`a = (1 - θ) a₀ + θ a₁`. It equals `1` at `z = θ`, and if `a ≠ 0` its real part is `a₀ / a` on
the line `re z = 0` and `a₁ / a` on the line `re z = 1`. If `a = 0` it is constantly `1`. -/
noncomputable def thorinExponent (a₀ a₁ θ : ℝ) (z : ℂ) : ℂ :=
  1 + (z - θ) * (thorinSlope a₀ a₁ θ : ℂ)

theorem thorinExponent_def (a₀ a₁ θ : ℝ) (z : ℂ) :
    thorinExponent a₀ a₁ θ z = 1 + (z - θ) * (thorinSlope a₀ a₁ θ : ℂ) :=
  (rfl)

theorem re_thorinExponent (a₀ a₁ θ : ℝ) (z : ℂ) :
    (thorinExponent a₀ a₁ θ z).re = 1 + (z.re - θ) * thorinSlope a₀ a₁ θ := by
  simp [thorinExponent]

@[simp]
theorem thorinExponent_self (a₀ a₁ θ : ℝ) : thorinExponent a₀ a₁ θ θ = 1 := by
  simp [thorinExponent]

theorem re_thorinExponent_mul {a₀ a₁ θ : ℝ} (ha : (1 - θ) * a₀ + θ * a₁ ≠ 0) (z : ℂ) :
    (thorinExponent a₀ a₁ θ z).re * ((1 - θ) * a₀ + θ * a₁) = (1 - z.re) * a₀ + z.re * a₁ := by
  rw [re_thorinExponent, thorinSlope, add_mul, one_mul, mul_assoc, div_mul_cancel₀ _ ha]
  ring

theorem re_thorinExponent_nonneg {a₀ a₁ θ : ℝ} (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) {z : ℂ} (hz : z.re ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ (thorinExponent a₀ a₁ θ z).re := by
  have ha : 0 ≤ (1 - θ) * a₀ + θ * a₁ := by
    have := sub_nonneg.2 hθ.2
    have := hθ.1
    positivity
  rcases ha.eq_or_lt with ha | ha
  · simp [re_thorinExponent, thorinSlope, ← ha]
  · have h := re_thorinExponent_mul ha.ne' z
    have : 0 ≤ (1 - z.re) * a₀ + z.re * a₁ := by
      have := hz.1
      have := sub_nonneg.2 hz.2
      positivity
    nlinarith

theorem abs_re_thorinExponent_le (a₀ a₁ : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) {z : ℂ}
    (hz : z.re ∈ Set.Icc (0 : ℝ) 1) :
    |(thorinExponent a₀ a₁ θ z).re - 1| ≤ |thorinSlope a₀ a₁ θ| := by
  rw [re_thorinExponent, add_sub_cancel_left, abs_mul]
  have h1 : |z.re - θ| ≤ 1 := abs_le.2 ⟨by linarith [hz.1, hθ.2], by linarith [hz.2, hθ.1]⟩
  exact mul_le_of_le_one_left (abs_nonneg _) h1

open scoped ENNReal in
/-- Along Thorin's analytic family between interpolated exponents
`1 / s = (1 - θ) / s₀ + θ / s₁`, the exponent `(1 - re z) / s₀ + re z / s₁` is `re w / s`, where
`w = thorinExponent (1 / s₀) (1 / s₁) θ z`. The hypothesis that `s` is finite unless both `s₀` and
`s₁` are holds automatically for `0 < θ < 1` (`TauCeti.eq_top_iff_of_inv_eq`). -/
theorem ofReal_re_thorinExponent_mul_inv {s₀ s₁ s : ℝ≥0∞} (hs₀ : s₀ ≠ 0) (hs₁ : s₁ ≠ 0) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hs : s⁻¹ = ENNReal.ofReal (1 - θ) * s₀⁻¹ + ENNReal.ofReal θ * s₁⁻¹)
    (hs_top : s = ∞ → s₀ = ∞ ∧ s₁ = ∞) {z : ℂ} (hz : z.re ∈ Set.Icc (0 : ℝ) 1) :
    ENNReal.ofReal (thorinExponent (s₀⁻¹).toReal (s₁⁻¹).toReal θ z).re * s⁻¹ =
      ENNReal.ofReal (1 - z.re) * s₀⁻¹ + ENNReal.ofReal z.re * s₁⁻¹ := by
  have h0 : (0 : ℝ) ≤ (s₀⁻¹).toReal := ENNReal.toReal_nonneg
  have h1 : (0 : ℝ) ≤ (s₁⁻¹).toReal := ENNReal.toReal_nonneg
  have hz1 : 0 ≤ 1 - z.re := sub_nonneg.2 hz.2
  have hs' := inv_eq_ofReal_of_inv_eq hs₀ hs₁ hθ hs
  rcases eq_or_ne ((1 - θ) * (s₀⁻¹).toReal + θ * (s₁⁻¹).toReal) 0 with ha | ha
  · have hs_inf : s = ∞ := ENNReal.inv_eq_zero.1 (by rw [hs', ha, ENNReal.ofReal_zero])
    obtain ⟨rfl, rfl⟩ := hs_top hs_inf
    simp [hs_inf]
  rw [hs', ← ENNReal.ofReal_mul (re_thorinExponent_nonneg h0 h1 hθ hz), re_thorinExponent_mul ha,
    ENNReal.ofReal_add (mul_nonneg hz1 h0) (mul_nonneg hz.1 h1), ENNReal.ofReal_mul hz1,
    ENNReal.ofReal_mul hz.1, ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 hs₀),
    ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 hs₁)]

end TauCeti

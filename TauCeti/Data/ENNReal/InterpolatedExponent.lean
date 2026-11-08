/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.ConjExponents
public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Interpolated exponents in `ℝ≥0∞`

For exponents `s₀, s₁ ∈ (0, ∞]` and `0 ≤ θ ≤ 1`, the interpolated exponent `s` is defined by
`1 / s = (1 - θ) / s₀ + θ / s₁`, written `s⁻¹ = ofReal (1 - θ) * s₀⁻¹ + ofReal θ * s₁⁻¹`. This is
the exponent relation of complex and real interpolation of `Lᵖ` spaces (Riesz–Thorin,
Marcinkiewicz). This file records its elementary arithmetic.

## Main declarations

* `TauCeti.inv_eq_ofReal_of_inv_eq`: `1 / s` is the real convex combination of `1 / s₀` and
  `1 / s₁`.
* `TauCeti.mem_uIcc_of_inv_eq`: `s` lies between `s₀` and `s₁`.
* `TauCeti.eq_top_iff_of_inv_eq`: for `0 < θ < 1`, `s = ∞` exactly when `s₀ = s₁ = ∞`.
* `TauCeti.one_le_of_inv_eq`: interpolating exponents in `[1, ∞]` stays in `[1, ∞]`.
* `TauCeti.inv_conjExponent_eq_of_inv_eq`: the conjugate exponents interpolate in the same way.
-/

public section

open scoped ENNReal

namespace TauCeti

variable {s₀ s₁ s : ℝ≥0∞} {θ : ℝ}

/-- An interpolated exponent `1 / s = (1 - θ) / s₀ + θ / s₁` is the reciprocal of a real number in
the closed interval between the reciprocals of the endpoints. -/
theorem inv_eq_ofReal_of_inv_eq (hs₀ : s₀ ≠ 0) (hs₁ : s₁ ≠ 0) (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hs : s⁻¹ = ENNReal.ofReal (1 - θ) * s₀⁻¹ + ENNReal.ofReal θ * s₁⁻¹) :
    s⁻¹ = ENNReal.ofReal ((1 - θ) * (s₀⁻¹).toReal + θ * (s₁⁻¹).toReal) := by
  have h₀ : s₀⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hs₀
  have h₁ : s₁⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hs₁
  have hθ1 : 0 ≤ 1 - θ := sub_nonneg.2 hθ.2
  rw [ENNReal.ofReal_add (mul_nonneg hθ1 ENNReal.toReal_nonneg)
    (mul_nonneg hθ.1 ENNReal.toReal_nonneg), ENNReal.ofReal_mul hθ1, ENNReal.ofReal_mul hθ.1,
    ENNReal.ofReal_toReal h₀, ENNReal.ofReal_toReal h₁, hs]

/-- An interpolated exponent lies between the two endpoint exponents. -/
theorem mem_uIcc_of_inv_eq (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hs : s⁻¹ = ENNReal.ofReal (1 - θ) * s₀⁻¹ + ENNReal.ofReal θ * s₁⁻¹) :
    s ∈ Set.uIcc s₀ s₁ := by
  have h1 (x : ℝ≥0∞) : x = ENNReal.ofReal (1 - θ) * x + ENNReal.ofReal θ * x := by
    rw [← add_mul, ← ENNReal.ofReal_add (sub_nonneg.2 hθ.2) hθ.1, sub_add_cancel,
      ENNReal.ofReal_one, one_mul]
  have hs' : s⁻¹ ∈ Set.uIcc s₀⁻¹ s₁⁻¹ := by
    rw [hs]
    refine ⟨(h1 _).trans_le ?_, le_trans ?_ (h1 _).ge⟩ <;> gcongr <;> simp
  simpa using ENNReal.inv_strictAnti.antitone.mapsTo_uIcc hs'

/-- For `0 < θ < 1`, an interpolated exponent is infinite exactly when both endpoint exponents
are. -/
theorem eq_top_iff_of_inv_eq (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s⁻¹ = ENNReal.ofReal (1 - θ) * s₀⁻¹ + ENNReal.ofReal θ * s₁⁻¹) :
    s = ∞ ↔ s₀ = ∞ ∧ s₁ = ∞ := by
  rw [← ENNReal.inv_eq_zero, hs]
  simp [hθ.1.not_ge, hθ.2.not_ge]

/-- Interpolating between exponents in `[1, ∞]` gives an exponent in `[1, ∞]`. -/
theorem one_le_of_inv_eq (hs₀ : 1 ≤ s₀) (hs₁ : 1 ≤ s₁) (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hs : s⁻¹ = ENNReal.ofReal (1 - θ) * s₀⁻¹ + ENNReal.ofReal θ * s₁⁻¹) : 1 ≤ s :=
  (le_inf hs₀ hs₁).trans (mem_uIcc_of_inv_eq hθ hs).1

/-- Conjugate exponents interpolate in the same way as the exponents themselves. -/
theorem inv_conjExponent_eq_of_inv_eq (hs₀ : 1 ≤ s₀) (hs₁ : 1 ≤ s₁)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hs : s⁻¹ = ENNReal.ofReal (1 - θ) * s₀⁻¹ + ENNReal.ofReal θ * s₁⁻¹) :
    s.conjExponent⁻¹ =
      ENNReal.ofReal (1 - θ) * s₀.conjExponent⁻¹ + ENNReal.ofReal θ * s₁.conjExponent⁻¹ := by
  have hs1 := one_le_of_inv_eq hs₀ hs₁ hθ hs
  rw [← (ENNReal.HolderConjugate.conjExponent hs1).one_sub_inv,
    ← (ENNReal.HolderConjugate.conjExponent hs₀).one_sub_inv,
    ← (ENNReal.HolderConjugate.conjExponent hs₁).one_sub_inv]
  refine ENNReal.sub_eq_of_eq_add (ENNReal.inv_ne_top.2 (zero_lt_one.trans_le hs1).ne') ?_
  rw [hs, add_add_add_comm, ← mul_add, ← mul_add, tsub_add_cancel_of_le (ENNReal.inv_le_one.2 hs₀),
    tsub_add_cancel_of_le (ENNReal.inv_le_one.2 hs₁), mul_one, mul_one,
    ← ENNReal.ofReal_add (sub_nonneg.2 hθ.2) hθ.1, sub_add_cancel, ENNReal.ofReal_one]

end TauCeti

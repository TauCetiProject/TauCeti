/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.ConjExponents
public import Mathlib.Order.Interval.Set.UnorderedInterval
import TauCeti.Basic.ENNReal.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Interpolated exponents in `ℝ≥0∞`

For exponents `s₀, s₁ ∈ (0, ∞]` and `0 ≤ θ ≤ 1`, the interpolated exponent `s` is defined by
`1 / s = (1 - θ) / s₀ + θ / s₁`, written `s⁻¹ = ofReal (1 - θ) * s₀⁻¹ + ofReal θ * s₁⁻¹`. This is
the exponent relation of complex and real interpolation of `Lᵖ` spaces (Riesz–Thorin,
Marcinkiewicz). This file records its elementary arithmetic.

## Main declarations

* `TauCeti.inv_eq_ofReal_of_inv_eq`: `1 / s` is the real convex combination of `1 / s₀` and
  `1 / s₁`.
* `TauCeti.toReal_mul_inv_add`: for finite `s`, `s * ((1 - θ) / s₀) + s * (θ / s₁) = 1`.
* `TauCeti.inv_toReal_eq_of_inv_eq`: the same relation between the real exponents.
* `TauCeti.exists_inv_eq_ofReal_mul_inv_of_inv_eq`: for `s < ∞`, `1 / s₀ = r(0) / s` and
  `1 / s₁ = r(1) / s` for an affine `r ≥ 0` on `[0, 1]` with `r(θ) = 1`.
* `TauCeti.mem_uIcc_of_inv_eq`: `s` lies between `s₀` and `s₁`.
* `TauCeti.exists_inv_eq_of_mem_Ioo`: conversely, every `s` strictly between `s₀` and `s₁` is
  interpolated with some `0 < θ < 1`.
* `TauCeti.eq_top_iff_of_inv_eq`: for `0 < θ < 1`, `s = ∞` exactly when `s₀ = s₁ = ∞`.
* `TauCeti.one_le_of_inv_eq`: interpolating exponents in `[1, ∞]` stays in `[1, ∞]`.
* `TauCeti.inv_conjExponent_eq_of_inv_eq`: the conjugate exponents interpolate in the same way.
* `TauCeti.exists_slope_of_inv_eq`: for `0 < θ < 1`, the exponents `(1 - t) / s₀ + t / s₁` along
  `0 ≤ t ≤ 1` are `(1 + (t - θ) κ) / s` for a fixed slope `κ`, with nonnegative factor.
* `TauCeti.exists_inv_eq_of_inv_lt_inv_add`: an exponent `q ≥ p` with `1/p - 1/q < ν` is
  interpolated, with `θ < 1`, between `p` and a finite `s` with `1/p - 1/s < ν`.
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

/-- Real normalization identity for a finite interpolated exponent
`1 / s = (1 - θ) / s₀ + θ / s₁`: `s * ((1 - θ) / s₀) + s * (θ / s₁) = 1`. -/
theorem toReal_mul_inv_add (hs₀ : s₀ ≠ 0) (hs₁ : s₁ ≠ 0) (hs_top : s ≠ ∞)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hs : s⁻¹ = ENNReal.ofReal (1 - θ) * s₀⁻¹ + ENNReal.ofReal θ * s₁⁻¹) :
    s.toReal * ((1 - θ) * (s₀⁻¹).toReal) + s.toReal * (θ * (s₁⁻¹).toReal) = 1 := by
  have hs' := inv_eq_ofReal_of_inv_eq hs₀ hs₁ hθ hs
  have hs0 : s ≠ 0 := ENNReal.inv_ne_top.1 (hs' ▸ ENNReal.ofReal_ne_top)
  have hinv := congrArg ENNReal.toReal hs'
  have hθ1 : 0 ≤ 1 - θ := sub_nonneg.2 hθ.2
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal
    (add_nonneg (mul_nonneg hθ1 ENNReal.toReal_nonneg)
      (mul_nonneg hθ.1 ENNReal.toReal_nonneg))] at hinv
  rw [← mul_add, ← hinv, mul_inv_cancel₀ (ENNReal.toReal_pos hs0 hs_top).ne']

/-- An interpolated exponent `1 / s = (1 - θ) / s₀ + θ / s₁` satisfies the same relation between
the real exponents `s.toReal`, `s₀.toReal` and `s₁.toReal`, with `∞` read as `0`. -/
theorem inv_toReal_eq_of_inv_eq (hs₀ : s₀ ≠ 0) (hs₁ : s₁ ≠ 0) (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hs : s⁻¹ = ENNReal.ofReal (1 - θ) * s₀⁻¹ + ENNReal.ofReal θ * s₁⁻¹) :
    s.toReal⁻¹ = (1 - θ) * s₀.toReal⁻¹ + θ * s₁.toReal⁻¹ := by
  have h := congrArg ENNReal.toReal (inv_eq_ofReal_of_inv_eq hs₀ hs₁ hθ hs)
  have h1 : 0 ≤ 1 - θ := sub_nonneg.2 hθ.2
  have h2 : 0 ≤ θ := hθ.1
  rwa [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_inv, ENNReal.toReal_inv,
    ENNReal.toReal_inv] at h

/-- For a finite interpolated exponent `1 / s = (1 - θ) / s₀ + θ / s₁`, there is a slope `k` with
`1 / s₀ = (1 - θ k) / s` and `1 / s₁ = (1 + (1 - θ) k) / s`, both factors nonnegative. These are
the exponents on the boundary lines of the analytic family `|f| ^ (1 + (z - θ) k)` through
`f ∈ Lˢ` used in complex interpolation. -/
theorem exists_inv_eq_ofReal_mul_inv_of_inv_eq (hs₀ : s₀ ≠ 0) (hs₁ : s₁ ≠ 0) (hs_top : s ≠ ∞)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hs : s⁻¹ = ENNReal.ofReal (1 - θ) * s₀⁻¹ + ENNReal.ofReal θ * s₁⁻¹) :
    ∃ k : ℝ, 0 ≤ 1 - θ * k ∧ 0 ≤ 1 + (1 - θ) * k ∧
      s₀⁻¹ = ENNReal.ofReal (1 - θ * k) * s⁻¹ ∧ s₁⁻¹ = ENNReal.ofReal (1 + (1 - θ) * k) * s⁻¹ := by
  have hs' := inv_eq_ofReal_of_inv_eq hs₀ hs₁ hθ hs
  have hs_inv : s⁻¹ ≠ ∞ := hs' ▸ ENNReal.ofReal_ne_top
  -- with `a₀ = 1 / s₀`, `a₁ = 1 / s₁` and `a = 1 / s = (1 - θ) a₀ + θ a₁ > 0`, take
  -- `k = (a₁ - a₀) / a`, so that `1 - θ k = a₀ / a` and `1 + (1 - θ) k = a₁ / a`
  set a := (s⁻¹).toReal with ha_def
  have ha₀ : 0 ≤ (s₀⁻¹).toReal := ENNReal.toReal_nonneg
  have ha₁ : 0 ≤ (s₁⁻¹).toReal := ENNReal.toReal_nonneg
  have ha : a = (1 - θ) * (s₀⁻¹).toReal + θ * (s₁⁻¹).toReal := by
    rw [ha_def, hs', ENNReal.toReal_ofReal (by nlinarith [hθ.1, hθ.2])]
  have hapos : 0 < a := ENNReal.toReal_pos (ENNReal.inv_ne_zero.2 hs_top) hs_inv
  have hq (q : ℝ≥0∞) (hq0 : q ≠ 0) : q⁻¹ = ENNReal.ofReal ((q⁻¹).toReal / a) * s⁻¹ := by
    rw [← ENNReal.ofReal_toReal hs_inv, ← ENNReal.ofReal_mul (by positivity),
      div_mul_cancel₀ _ hapos.ne', ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 hq0)]
  have hr₀ : 1 - θ * (((s₁⁻¹).toReal - (s₀⁻¹).toReal) / a) = (s₀⁻¹).toReal / a := by
    field_simp
    linarith
  have hr₁ : 1 + (1 - θ) * (((s₁⁻¹).toReal - (s₀⁻¹).toReal) / a) = (s₁⁻¹).toReal / a := by
    field_simp
    linarith
  refine ⟨((s₁⁻¹).toReal - (s₀⁻¹).toReal) / a, ?_, ?_, ?_, ?_⟩
  · rw [hr₀]
    positivity
  · rw [hr₁]
    positivity
  · rw [hr₀]
    exact hq s₀ hs₀
  · rw [hr₁]
    exact hq s₁ hs₁

/-- An interpolated exponent lies between the two endpoint exponents. -/
theorem mem_uIcc_of_inv_eq (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hs : s⁻¹ = ENNReal.ofReal (1 - θ) * s₀⁻¹ + ENNReal.ofReal θ * s₁⁻¹) :
    s ∈ Set.uIcc s₀ s₁ := by
  have h1 (x : ℝ≥0∞) : x = ENNReal.ofReal (1 - θ) * x + ENNReal.ofReal θ * x := by
    rw [← add_mul, ofReal_sub_add_ofReal hθ.1 hθ.2, ENNReal.ofReal_one, one_mul]
  have hs' : s⁻¹ ∈ Set.uIcc s₀⁻¹ s₁⁻¹ := by
    rw [hs]
    refine ⟨(h1 _).trans_le ?_, le_trans ?_ (h1 _).ge⟩ <;> gcongr <;> simp
  simpa using ENNReal.inv_strictAnti.antitone.mapsTo_uIcc hs'

/-- Every exponent strictly between `s₀ ≠ 0` and `s₁` is an interpolated exponent
`1 / s = (1 - θ) / s₀ + θ / s₁` for some `0 < θ < 1`. -/
theorem exists_inv_eq_of_mem_Ioo (hs₀ : s₀ ≠ 0) (hs : s ∈ Set.Ioo s₀ s₁) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) 1, s⁻¹ = ENNReal.ofReal (1 - θ) * s₀⁻¹ + ENNReal.ofReal θ * s₁⁻¹ := by
  have hs0 : s ≠ 0 := (pos_iff_ne_zero.2 hs₀).trans hs.1 |>.ne'
  have h₀ : s₀⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hs₀
  have h : s⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hs0
  have h₁ : s₁⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 ((pos_iff_ne_zero.2 hs0).trans hs.2).ne'
  rw [← ENNReal.ofReal_toReal h₀, ← ENNReal.ofReal_toReal h, ← ENNReal.ofReal_toReal h₁]
  have hr₀ : s⁻¹.toReal < s₀⁻¹.toReal := ENNReal.toReal_strict_mono h₀ (ENNReal.inv_lt_inv.2 hs.1)
  have hr₁ : s₁⁻¹.toReal < s⁻¹.toReal := ENNReal.toReal_strict_mono h (ENNReal.inv_lt_inv.2 hs.2)
  have hb : 0 ≤ s₁⁻¹.toReal := ENNReal.toReal_nonneg
  generalize s₀⁻¹.toReal = a, s⁻¹.toReal = r, s₁⁻¹.toReal = b at *
  have hab : 0 < a - b := by linarith
  have hθ₀ : 0 < (a - r) / (a - b) := div_pos (by linarith) hab
  have hθ₁ : (a - r) / (a - b) < 1 := (div_lt_one hab).2 (by linarith)
  refine ⟨(a - r) / (a - b), ⟨hθ₀, hθ₁⟩, ?_⟩
  rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul hθ₀.le,
    ← ENNReal.ofReal_add (by nlinarith) (by positivity)]
  congr 1
  field_simp
  ring

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
  calc 1 = ENNReal.ofReal (1 - θ) * (1 - s₀⁻¹ + s₀⁻¹) + ENNReal.ofReal θ * (1 - s₁⁻¹ + s₁⁻¹) := by
        rw [tsub_add_cancel_of_le (ENNReal.inv_le_one.2 hs₀),
          tsub_add_cancel_of_le (ENNReal.inv_le_one.2 hs₁), mul_one, mul_one,
          ofReal_sub_add_ofReal hθ.1 hθ.2, ENNReal.ofReal_one]
    _ = _ := by rw [hs]; ring

/-- **The exponent along the segment.** Let `1 / s = (1 - θ) / s₀ + θ / s₁` with `0 < θ < 1`.
There is a slope `κ` such that for every `0 ≤ t ≤ 1` the factor `1 + (t - θ) κ` is nonnegative and
`(1 + (t - θ) κ) / s = (1 - t) / s₀ + t / s₁`. The factor equals `1` at `t = θ`; it is the real
part of the exponent of the analytic families in three-lines proofs of complex interpolation. -/
theorem exists_slope_of_inv_eq (hs₀ : s₀ ≠ 0) (hs₁ : s₁ ≠ 0) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s⁻¹ = ENNReal.ofReal (1 - θ) * s₀⁻¹ + ENNReal.ofReal θ * s₁⁻¹) :
    ∃ κ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ 1 + (t - θ) * κ ∧
      ENNReal.ofReal (1 + (t - θ) * κ) * s⁻¹ =
        ENNReal.ofReal (1 - t) * s₀⁻¹ + ENNReal.ofReal t * s₁⁻¹ := by
  rw [inv_eq_ofReal_of_inv_eq hs₀ hs₁ (Set.Ioo_subset_Icc_self hθ) hs]
  obtain ⟨hθ0, hθ1⟩ := hθ
  -- Work with the real reciprocals `a₀ = 1 / s₀`, `a₁ = 1 / s₁` and `a = 1 / s`.
  set a₀ := (s₀⁻¹).toReal
  set a₁ := (s₁⁻¹).toReal
  have ha₀ : 0 ≤ a₀ := ENNReal.toReal_nonneg
  have ha₁ : 0 ≤ a₁ := ENNReal.toReal_nonneg
  have e₀ : s₀⁻¹ = ENNReal.ofReal a₀ := (ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 hs₀)).symm
  have e₁ : s₁⁻¹ = ENNReal.ofReal a₁ := (ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 hs₁)).symm
  rw [e₀, e₁]
  set a := (1 - θ) * a₀ + θ * a₁
  have ha : 0 ≤ a := add_nonneg (mul_nonneg (sub_pos.2 hθ1).le ha₀) (mul_nonneg hθ0.le ha₁)
  -- The factor times `a` is the convex combination of `a₀` and `a₁`. If `a = 0`, both vanish.
  have key (t : ℝ) : (1 + (t - θ) * ((a₁ - a₀) / a)) * a = (1 - t) * a₀ + t * a₁ := by
    rcases ha.eq_or_lt with ha | ha
    · obtain ⟨h₀, h₁⟩ : a₀ = 0 ∧ a₁ = 0 := by
        constructor <;> nlinarith [mul_nonneg (sub_pos.2 hθ1).le ha₀, mul_nonneg hθ0.le ha₁]
      simp [← ha, h₀, h₁]
    · field_simp
      ring
  refine ⟨(a₁ - a₀) / a, fun t ht => ?_⟩
  have ht₁ : 0 ≤ 1 - t := sub_nonneg.2 ht.2
  have hβ : 0 ≤ 1 + (t - θ) * ((a₁ - a₀) / a) := by
    rcases ha.eq_or_lt with ha | ha
    · simp [← ha]
    · nlinarith [key t, mul_nonneg ht₁ ha₀, mul_nonneg ht.1 ha₁]
  refine ⟨hβ, ?_⟩
  rw [← ENNReal.ofReal_mul hβ, key, ENNReal.ofReal_add (mul_nonneg ht₁ ha₀) (mul_nonneg ht.1 ha₁),
    ENNReal.ofReal_mul ht₁, ENNReal.ofReal_mul ht.1]

/-- Let `p ≤ q` with `1 ≤ q < ∞`, and let `ν` with `1/p - 1/q < ν`. Then `q` is interpolated
between `p` and a larger finite exponent still in this range: there are a finite `s ≥ 1` with
`1/p - 1/s < ν` and `0 ≤ θ < 1` with `1/q = (1 - θ)/p + θ/s`. With `ν = 1/n` this chooses the
auxiliary exponent for compactness of subcritical Sobolev embeddings by interpolation. -/
theorem exists_inv_eq_of_inv_lt_inv_add {p q ν : ℝ≥0∞} (hq₁ : 1 ≤ q) (hq : q ≠ ∞)
    (hpq : p ≤ q) (h : p⁻¹ < q⁻¹ + ν) :
    ∃ s : ℝ≥0∞, ∃ θ : ℝ, 1 ≤ s ∧ s ≠ ∞ ∧ p⁻¹ < s⁻¹ + ν ∧ 0 ≤ θ ∧ θ < 1 ∧
      q⁻¹ = ENNReal.ofReal (1 - θ) * p⁻¹ + ENNReal.ofReal θ * s⁻¹ := by
  have hq₀ : q ≠ 0 := (zero_lt_one.trans_le hq₁).ne'
  have hp : p ≠ ∞ := ne_top_of_le_ne_top hq hpq
  -- `p ≠ 0`, since otherwise `1/p = ∞` could not be less than `1/q + ν`.
  have hp₀ : p ≠ 0 := by
    rintro rfl
    simp at h
  wlog hν : ν ≠ ∞ generalizing ν
  · have hp' : p⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hp₀
    have hq' : q⁻¹ ≠ 0 := (ENNReal.inv_pos.2 hq).ne'
    obtain ⟨s, θ, hs₁, hs, -, hθ₀, hθ₁, hsθ⟩ :=
      this (ν := p⁻¹) (add_comm p⁻¹ q⁻¹ ▸ ENNReal.lt_add_right hp' hq') hp'
    exact ⟨s, θ, hs₁, hs, by rw [not_not.1 hν, add_top]; exact hp'.lt_top, hθ₀, hθ₁, hsθ⟩
  -- Work with the real reciprocals `a = 1/p`, `b = 1/q` and `ν`.
  have hinv {r : ℝ≥0∞} (hr : r ≠ 0) (hr' : r ≠ ∞) : r⁻¹ = ENNReal.ofReal r.toReal⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hr hr'), ENNReal.ofReal_toReal hr']
  rw [hinv hp₀ hp, hinv hq₀ hq, ← ENNReal.ofReal_toReal hν] at h ⊢
  set a := p.toReal⁻¹
  set b := q.toReal⁻¹
  set ν := ν.toReal
  have hb0 : 0 < b := inv_pos.2 (ENNReal.toReal_pos hq₀ hq)
  have hb1 : b ≤ 1 := inv_le_one_of_one_le₀ (by simpa using ENNReal.toReal_mono hq hq₁)
  have hν0 : 0 ≤ ν := ENNReal.toReal_nonneg
  have hba : b ≤ a := inv_anti₀ (ENNReal.toReal_pos hp₀ hp) (ENNReal.toReal_mono hq hpq)
  rw [← ENNReal.ofReal_add hb0.le hν0,
    ENNReal.ofReal_lt_ofReal_iff (add_pos_of_pos_of_nonneg hb0 hν0)] at h
  -- The reciprocal `c = 1/s` lies strictly between `max (a - ν) 0` and `b`.
  set c := (b + max (a - ν) 0) / 2
  have hmb : max (a - ν) 0 < b := max_lt (by linarith) hb0
  have hc0 : 0 < c := by have := le_max_right (a - ν) 0; simp only [c]; linarith
  have hcb : c < b := by simp only [c]; linarith
  have hac : a < c + ν := by have := le_max_left (a - ν) 0; simp only [c]; linarith
  have hs : (ENNReal.ofReal c⁻¹)⁻¹ = ENNReal.ofReal c := by
    rw [← ENNReal.ofReal_inv_of_pos (inv_pos.2 hc0), inv_inv]
  have hac' : 0 < a - c := by linarith
  have hθ0 : 0 ≤ (a - b) / (a - c) := div_nonneg (by linarith) hac'.le
  have hθ1 : (a - b) / (a - c) < 1 := (div_lt_one hac').2 (by linarith)
  have hθ : (a - b) / (a - c) * (a - c) = a - b := div_mul_cancel₀ _ hac'.ne'
  refine ⟨ENNReal.ofReal c⁻¹, (a - b) / (a - c),
    ENNReal.one_le_ofReal.2 ((one_le_inv₀ hc0).2 (by linarith)), ENNReal.ofReal_ne_top, ?_,
    hθ0, hθ1, ?_⟩
  · rwa [hs, ← ENNReal.ofReal_add hc0.le hν0,
      ENNReal.ofReal_lt_ofReal_iff (add_pos_of_pos_of_nonneg hc0 hν0)]
  · rw [hs, ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul hθ0,
      ← ENNReal.ofReal_add (mul_nonneg (by linarith) (by linarith)) (mul_nonneg hθ0 hc0.le)]
    congr 1
    linear_combination hθ

end TauCeti

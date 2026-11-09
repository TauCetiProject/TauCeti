/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.ConjExponents
public import Mathlib.Order.Interval.Set.UnorderedInterval
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
* `TauCeti.mem_uIcc_of_inv_eq`: `s` lies between `s₀` and `s₁`.
* `TauCeti.eq_top_iff_of_inv_eq`: for `0 < θ < 1`, `s = ∞` exactly when `s₀ = s₁ = ∞`.
* `TauCeti.one_le_of_inv_eq`: interpolating exponents in `[1, ∞]` stays in `[1, ∞]`.
* `TauCeti.inv_conjExponent_eq_of_inv_eq`: the conjugate exponents interpolate in the same way.
* `TauCeti.exists_inv_eq_of_inv_lt_inv_add`: an exponent `q ≥ p` with `1/p - 1/q < ν` is
  interpolated, with `θ < 1`, between `p` and a finite `s` with `1/p - 1/s < ν`.
-/

public section

open scoped ENNReal

namespace TauCeti

open ENNReal

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
theorem mem_uIcc_of_inv_eq (hs₀ : s₀ ≠ 0) (hs₁ : s₁ ≠ 0) (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hs : s⁻¹ = ENNReal.ofReal (1 - θ) * s₀⁻¹ + ENNReal.ofReal θ * s₁⁻¹) :
    s ∈ Set.uIcc s₀ s₁ := by
  rw [Set.mem_uIcc]
  have e := inv_eq_ofReal_of_inv_eq hs₀ hs₁ hθ hs
  have e₀ : s₀⁻¹ = ENNReal.ofReal (s₀⁻¹).toReal :=
    (ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 hs₀)).symm
  have e₁ : s₁⁻¹ = ENNReal.ofReal (s₁⁻¹).toReal :=
    (ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 hs₁)).symm
  have hθ0 := hθ.1
  have hθ1 := hθ.2
  rcases le_total (s₀⁻¹).toReal (s₁⁻¹).toReal with h | h
  · right
    constructor
    · rw [← ENNReal.inv_le_inv, e]
      exact (ENNReal.ofReal_le_ofReal (by nlinarith)).trans_eq e₁.symm
    · rw [← ENNReal.inv_le_inv, e]
      exact e₀.le.trans (ENNReal.ofReal_le_ofReal (by nlinarith))
  · left
    constructor
    · rw [← ENNReal.inv_le_inv, e]
      exact (ENNReal.ofReal_le_ofReal (by nlinarith)).trans_eq e₀.symm
    · rw [← ENNReal.inv_le_inv, e]
      exact e₁.le.trans (ENNReal.ofReal_le_ofReal (by nlinarith))

/-- For `0 < θ < 1`, an interpolated exponent is infinite exactly when both endpoint exponents
are. -/
theorem eq_top_iff_of_inv_eq (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s⁻¹ = ENNReal.ofReal (1 - θ) * s₀⁻¹ + ENNReal.ofReal θ * s₁⁻¹) :
    s = ∞ ↔ s₀ = ∞ ∧ s₁ = ∞ := by
  have hθ0 : ENNReal.ofReal θ ≠ 0 := by simpa using hθ.1
  have hθ1 : ENNReal.ofReal (1 - θ) ≠ 0 := by simpa using hθ.2
  rw [← ENNReal.inv_eq_zero, hs, add_eq_zero, mul_eq_zero, mul_eq_zero, ENNReal.inv_eq_zero,
    ENNReal.inv_eq_zero]
  simp [hθ0, hθ1]

/-- Interpolating between exponents in `[1, ∞]` gives an exponent in `[1, ∞]`. -/
theorem one_le_of_inv_eq (hs₀ : 1 ≤ s₀) (hs₁ : 1 ≤ s₁) (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hs : s⁻¹ = ENNReal.ofReal (1 - θ) * s₀⁻¹ + ENNReal.ofReal θ * s₁⁻¹) : 1 ≤ s := by
  rcases Set.mem_uIcc.1 (mem_uIcc_of_inv_eq (zero_lt_one.trans_le hs₀).ne'
    (zero_lt_one.trans_le hs₁).ne' hθ hs) with ⟨h, -⟩ | ⟨h, -⟩
  · exact hs₀.trans h
  · exact hs₁.trans h

/-- Conjugate exponents interpolate in the same way as the exponents themselves. -/
theorem inv_conjExponent_eq_of_inv_eq (hs₀ : 1 ≤ s₀) (hs₁ : 1 ≤ s₁)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hs : s⁻¹ = ENNReal.ofReal (1 - θ) * s₀⁻¹ + ENNReal.ofReal θ * s₁⁻¹) :
    s.conjExponent⁻¹ =
      ENNReal.ofReal (1 - θ) * s₀.conjExponent⁻¹ + ENNReal.ofReal θ * s₁.conjExponent⁻¹ := by
  have hs₀0 : s₀ ≠ 0 := (zero_lt_one.trans_le hs₀).ne'
  have hs₁0 : s₁ ≠ 0 := (zero_lt_one.trans_le hs₁).ne'
  have e := inv_eq_ofReal_of_inv_eq hs₀0 hs₁0 hθ hs
  set r₀ := (s₀⁻¹).toReal
  set r₁ := (s₁⁻¹).toReal
  have hr₀ : r₀ ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by simpa using ENNReal.inv_le_one.2 hs₀)
  have hr₁ : r₁ ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by simpa using ENNReal.inv_le_one.2 hs₁)
  have hθ0 := hθ.1
  have hθ1 := hθ.2
  have conj : ∀ {t : ℝ≥0∞}, 1 ≤ t → t⁻¹ ≠ ∞ →
      t.conjExponent⁻¹ = ENNReal.ofReal (1 - (t⁻¹).toReal) := fun {t} ht ht' => by
    have := ENNReal.HolderConjugate.conjExponent ht
    rw [← ENNReal.HolderConjugate.one_sub_inv t t.conjExponent, ENNReal.ofReal_sub _
      ENNReal.toReal_nonneg, ENNReal.ofReal_one, ENNReal.ofReal_toReal ht']
  rw [conj (one_le_of_inv_eq hs₀ hs₁ hθ hs) (by rw [e]; exact ENNReal.ofReal_ne_top), e,
    conj hs₀ (ENNReal.inv_ne_top.2 hs₀0), conj hs₁ (ENNReal.inv_ne_top.2 hs₁0),
    ENNReal.toReal_ofReal (by positivity), ← ENNReal.ofReal_mul (sub_nonneg.2 hθ1),
    ← ENNReal.ofReal_mul hθ0, ← ENNReal.ofReal_add (by nlinarith) (by nlinarith)]
  congr 1
  ring


/-- Let `p ≤ q` with `1 ≤ q < ∞`, and let `ν < ∞` with `1/p - 1/q < ν`. Then `q` is interpolated
between `p` and a larger finite exponent still in this range: there are a finite `s ≥ 1` with
`1/p - 1/s < ν` and `0 ≤ θ < 1` with `1/q = (1 - θ)/p + θ/s`. With `ν = 1/n` this chooses the
auxiliary exponent for compactness of subcritical Sobolev embeddings by interpolation. -/
theorem exists_inv_eq_of_inv_lt_inv_add {p q ν : ℝ≥0∞} (hq₁ : 1 ≤ q) (hq : q ≠ ∞) (hν : ν ≠ ∞)
    (hpq : p ≤ q) (h : p⁻¹ < q⁻¹ + ν) :
    ∃ s : ℝ≥0∞, ∃ θ : ℝ, 1 ≤ s ∧ s ≠ ∞ ∧ p⁻¹ < s⁻¹ + ν ∧ 0 ≤ θ ∧ θ < 1 ∧
      q⁻¹ = ENNReal.ofReal (1 - θ) * p⁻¹ + ENNReal.ofReal θ * s⁻¹ := by
  have hq₀ : q ≠ 0 := (zero_lt_one.trans_le hq₁).ne'
  have hp : p ≠ ∞ := ne_top_of_le_ne_top hq hpq
  -- `p ≠ 0`, since otherwise `1/p = ∞` could not be less than `1/q + ν`.
  have hp₀ : p ≠ 0 := by
    rintro rfl
    simp at h
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

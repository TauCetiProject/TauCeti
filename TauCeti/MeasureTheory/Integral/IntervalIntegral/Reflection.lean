/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Interval integrals under reflection

Reversing `[a, b]` by `t ↦ a + b - t` does not change integrals over it
(`TauCeti.intervalIntegral.integral_comp_add_sub`). A function `f` that agrees with `g` on
`(a, b)` and with its reflection `t ↦ g (2b - t)` in `b` on `(b, 2b - a)` is interval integrable
on `[a, b]` and on `[b, 2b - a]` when `g` is interval integrable on `[a, b]`
(`IntervalIntegrable.of_eqOn_reflect`), and its integral over `[a, 2b - a]` is twice the integral
of `g` over `[a, b]` (`TauCeti.intervalIntegral.integral_eq_two_smul_of_eqOn_reflect`). This is
how an even reflection doubles both integrals of a Poincaré-type inequality.
-/

public section

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] {f g : ℝ → E} {a b : ℝ}

/-- If `f` agrees with `g` on `(a, b)` and with its reflection `t ↦ g (2b - t)` in `b` on
`(b, 2b - a)`, and `g` is interval integrable on `[a, b]`, then `f` is interval integrable on
`[a, b]` and on `[b, 2b - a]`. -/
theorem IntervalIntegrable.of_eqOn_reflect (hg : IntervalIntegrable g volume a b)
    (h₁ : EqOn f g (uIoo a b)) (h₂ : EqOn f (fun t ↦ g (2 * b - t)) (uIoo b (2 * b - a))) :
    IntervalIntegrable f volume a b ∧ IntervalIntegrable f volume b (2 * b - a) := by
  refine ⟨hg.congr_uIoo h₁.symm, ?_⟩
  have h := (hg.comp_sub_left (2 * b)).symm
  rw [show 2 * b - b = b by ring] at h
  exact h.congr_uIoo h₂.symm

namespace TauCeti.intervalIntegral

variable [NormedSpace ℝ E]

/-- Reversing `[a, b]` by `t ↦ a + b - t` does not change integrals over it. -/
theorem integral_comp_add_sub (g : ℝ → E) :
    ∫ t in a..b, g (a + b - t) = ∫ t in a..b, g t := by
  rw [_root_.intervalIntegral.integral_comp_sub_left, add_sub_cancel_left, add_sub_cancel_right]

/-- **Doubling an interval integral by reflection.** If `f` agrees with `g` on `(a, b)` and with
its reflection `t ↦ g (2b - t)` in `b` on `(b, 2b - a)`, and `g` is interval integrable on
`[a, b]`, then the integral of `f` over `[a, 2b - a]` is twice the integral of `g` over
`[a, b]`. -/
theorem integral_eq_two_smul_of_eqOn_reflect (hg : IntervalIntegrable g volume a b)
    (h₁ : EqOn f g (uIoo a b)) (h₂ : EqOn f (fun t ↦ g (2 * b - t)) (uIoo b (2 * b - a))) :
    ∫ t in a..(2 * b - a), f t = (2 : ℝ) • ∫ t in a..b, g t := by
  obtain ⟨hf₁, hf₂⟩ := hg.of_eqOn_reflect h₁ h₂
  rw [← _root_.intervalIntegral.integral_add_adjacent_intervals hf₁ hf₂,
    _root_.intervalIntegral.integral_congr_uIoo h₁, _root_.intervalIntegral.integral_congr_uIoo h₂,
    _root_.intervalIntegral.integral_comp_sub_left g, sub_sub_cancel,
    show 2 * b - b = b by ring, two_smul]

end TauCeti.intervalIntegral

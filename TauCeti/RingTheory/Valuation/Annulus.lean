/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Basic

/-!
# Avoiding an open annulus with one inequality

Let `w` be a valuation on a commutative ring and let `r, σ` be elements with `0 ≠ w r < w σ`.
The condition that `w f` lies outside the open interval `(w r, w σ)`, a disjunction of two
inequalities, is equivalent to the single inequality

```text
w (σ f) ≤ w (f² - r σ) ≠ 0.
```

Indeed `w (f² - r σ)` is `w (r σ)` when `w f ^ 2 < w (r σ)`, and `w f ^ 2` when
`w f ^ 2 > w (r σ)`. In the first case the inequality says `w f ≤ w r`, in the second it says
`w σ ≤ w f`, and in the remaining case `w f ^ 2 = w (r σ)` it fails.

In an adic spectrum this exhibits the complement `{|f| ≤ |r|} ∪ {|σ| ≤ |f|}` of an open annulus
as the rational subset `R({σ f, f² - r σ} / (f² - r σ))`. This is how finite unions of discs and
of complements of discs in the closed unit disc are shown to be rational.

## Main results

* `Valuation.le_or_le_iff_map_mul_le_map_mul_self_sub`: `w f ≤ w r ∨ w σ ≤ w f` if and only if
  `w (σ f) ≤ w (f² - r σ)` and `w (f² - r σ) ≠ 0`.
-/

public section

namespace Valuation

variable {A Γ₀ : Type*} [CommRing A] [LinearOrderedCommGroupWithZero Γ₀] (w : Valuation A Γ₀)

/-- **The complement of an open annulus is cut out by one inequality.** If `0 ≠ w r < w σ`, then
`w f ≤ w r` or `w σ ≤ w f` exactly when `w (σ f) ≤ w (f² - r σ)` and `w (f² - r σ) ≠ 0`. -/
theorem le_or_le_iff_map_mul_le_map_mul_self_sub {f r σ : A} (hr : w r ≠ 0) (hrσ : w r < w σ) :
    (w f ≤ w r ∨ w σ ≤ w f) ↔ w (σ * f) ≤ w (f * f - r * σ) ∧ w (f * f - r * σ) ≠ 0 := by
  have hσ : w σ ≠ 0 := (zero_le.trans_lt hrσ).ne'
  constructor
  · rintro (h | h)
    · -- `w f² ≤ w r² < w (r σ)`, so `w (f² - r σ) = w (r σ)`
      have hlt : w (f * f) < w (r * σ) := by
        rw [map_mul, map_mul]
        exact (mul_le_mul' h h).trans_lt (mul_lt_mul_of_pos_left hrσ (zero_lt_iff.mpr hr))
      rw [Valuation.map_sub_eq_of_lt_right _ hlt, map_mul, map_mul, mul_comm (w σ)]
      exact ⟨mul_le_mul_left h _, mul_ne_zero hr hσ⟩
    · -- `w (r σ) < w σ² ≤ w f²`, so `w (f² - r σ) = w f²`
      have hlt : w (r * σ) < w (f * f) := by
        rw [map_mul, map_mul]
        exact (mul_lt_mul_of_pos_right hrσ (zero_lt_iff.mpr hσ)).trans_le (mul_le_mul' h h)
      rw [Valuation.map_sub_eq_of_lt_left _ hlt, map_mul, map_mul]
      exact ⟨mul_le_mul_left h _, map_mul w f f ▸ (zero_le.trans_lt hlt).ne'⟩
  · rintro ⟨h₁, h₂⟩
    rw [map_mul] at h₁
    rcases lt_trichotomy (w (f * f)) (w (r * σ)) with hlt | heq | hgt
    · left
      rw [Valuation.map_sub_eq_of_lt_right _ hlt, map_mul, mul_comm (w r)] at h₁
      exact le_of_mul_le_mul_left h₁ (zero_lt_iff.mpr hσ)
    · right
      have hf : w f ≠ 0 := by
        intro h0
        rw [map_mul, map_mul, h0, zero_mul] at heq
        exact mul_ne_zero hr hσ heq.symm
      have h₃ : w (f * f - r * σ) ≤ w f * w f := by
        rw [← map_mul]
        exact (Valuation.map_sub _ _ _).trans (by rw [heq, max_self])
      exact le_of_mul_le_mul_right (h₁.trans h₃) (zero_lt_iff.mpr hf)
    · right
      rw [Valuation.map_sub_eq_of_lt_left _ hgt, map_mul] at h₁ h₂
      exact le_of_mul_le_mul_right h₁ (zero_lt_iff.mpr (left_ne_zero_of_mul h₂))

end Valuation

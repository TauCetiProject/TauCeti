/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Ordinal.Principal

/-!
# Divisibility by additively principal ordinals

An ordinal `a` is additively principal when it is closed under addition, as are the powers
`ω ^ c`. Divisibility of ordinals is left divisibility, `a ∣ b` meaning `b = a * θ` for some `θ`.
If `a` is additively principal and divides `b + c`, then it divides `c`: every final segment of a
multiple of `a` is again a multiple of `a`. For instance, a final segment of a well-order of type
`ω ^ c * δ` has order type a multiple of `ω ^ c`.

## Main results

* `Ordinal.IsPrincipal.dvd_of_dvd_add`: an additively principal ordinal dividing `b + c` divides
  `c`.
-/

public section

universe u

namespace Ordinal

variable {a b c : Ordinal.{u}}

/-- An additively principal ordinal that divides `b + c` divides `c`. -/
theorem IsPrincipal.dvd_of_dvd_add (ha : IsPrincipal (· + ·) a) (h : a ∣ b + c) : a ∣ c := by
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [zero_dvd_iff, add_eq_zero] at h
    rw [h.2]
  -- Write `b = a * (b / a) + b % a`; then `a` divides `b % a + c`, with `b % a < a`.
  rw [← div_add_mod b a, add_assoc, dvd_add_iff (dvd_mul_right a _)] at h
  obtain ⟨θ, hθ⟩ := h
  rcases eq_or_ne θ 0 with rfl | hθ0
  · rw [mul_zero, add_eq_zero] at hθ
    exact hθ.2 ▸ dvd_zero a
  -- The remainder `b % a < a` is absorbed by the nonzero multiple `a * θ`.
  refine ⟨θ, add_left_cancel (a := b % a) ?_⟩
  rw [hθ, ha.add_eq_right_of_le (mod_lt b ha0) (le_mul_left a (pos_iff_ne_zero.2 hθ0))]

end Ordinal

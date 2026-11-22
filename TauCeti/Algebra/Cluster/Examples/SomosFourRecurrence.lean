/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Rat

/-!
# The positive rational Somos–4 recurrence

The four initial values are one. Each subsequent value is the sum of two products
of preceding values, divided by the oldest value in the window. Positivity makes
this division valid and gives uniqueness even in the multiplied form of the recurrence.

See Fomin–Zelevinsky, *The Laurent Phenomenon*, Example 3.3, for the recurrence.
-/

namespace TauCeti.SomosFour

/-- Four consecutive terms of the rational recurrence. -/
private def window : ℕ → ℚ × ℚ × ℚ × ℚ
  | 0 => (1, 1, 1, 1)
  | n + 1 =>
    let (a, b, c, d) := window n
    (b, c, d, (b * d + c ^ 2) / a)

/-- Every entry of a recurrence window is positive. -/
private theorem window_pos (n : ℕ) :
    0 < (window n).1 ∧ 0 < (window n).2.1 ∧
      0 < (window n).2.2.1 ∧ 0 < (window n).2.2.2 := by
  induction n with
  | zero => exact ⟨zero_lt_one, zero_lt_one, zero_lt_one, zero_lt_one⟩
  | succ n ih =>
    obtain ⟨ha, hb, hc, hd⟩ := ih
    exact ⟨hb, hc, hd, div_pos (add_pos (mul_pos hb hd) (pow_pos hc 2)) ha⟩

public section

/-- The rational Somos–4 sequence starting from four ones. -/
def rational (n : ℕ) : ℚ := (window n).1

/-- The first Somos–4 value is one. -/
@[simp] theorem rational_zero : rational 0 = 1 := by rfl

/-- The second Somos–4 value is one. -/
@[simp] theorem rational_one : rational 1 = 1 := by rfl

/-- The third Somos–4 value is one. -/
@[simp] theorem rational_two : rational 2 = 1 := by rfl

/-- The fourth Somos–4 value is one. -/
@[simp] theorem rational_three : rational 3 = 1 := by rfl

/-- Every rational Somos–4 value is strictly positive. -/
theorem rational_pos (n : ℕ) : 0 < rational n := (window_pos n).1

/-- The next rational Somos–4 value is given by its defining quotient. -/
theorem rational_add_four (n : ℕ) :
    rational (n + 4) = (rational (n + 1) * rational (n + 3) + rational (n + 2) ^ 2) /
      rational n := by rfl

/-- The rational sequence satisfies the Somos–4 recurrence with denominators cleared. -/
theorem rational_add_four_mul (n : ℕ) :
    rational (n + 4) * rational n =
      rational (n + 1) * rational (n + 3) + rational (n + 2) ^ 2 :=
  (eq_div_iff (ne_of_gt (rational_pos n))).mp (rational_add_four n)

/-- The multiplied recurrence and the four initial values determine the rational sequence. -/
theorem eq_rational_of_recurrence (b : ℕ → ℚ)
    (h₀ : b 0 = 1) (h₁ : b 1 = 1) (h₂ : b 2 = 1) (h₃ : b 3 = 1)
    (h : ∀ n, b (n + 4) * b n = b (n + 1) * b (n + 3) + b (n + 2) ^ 2) :
    b = rational := by
  funext n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _ | _ | _ | _ | n
    · simpa using h₀
    · simpa using h₁
    · simpa using h₂
    · simpa using h₃
    apply mul_right_cancel₀ (ne_of_gt (rational_pos n))
    have hn : b n = rational n := ih n (by omega)
    have hn₁ : b (n + 1) = rational (n + 1) := ih (n + 1) (by omega)
    have hn₂ : b (n + 2) = rational (n + 2) := ih (n + 2) (by omega)
    have hn₃ : b (n + 3) = rational (n + 3) := ih (n + 3) (by omega)
    rw [← hn, h n, hn₁, hn₂, hn₃, ← rational_add_four_mul, hn]

end
end TauCeti.SomosFour

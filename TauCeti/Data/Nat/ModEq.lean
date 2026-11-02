/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.ModEq

/-!
# Distinct residues modulo `p`

Two distinct residues `a, b < p` never differ by a multiple of `p`: if `b ≤ p * m + a`, so that
the natural subtraction does not truncate, the difference `p * m + a - b` is not divisible by `p`.
This is the arithmetic behind the uniqueness of the decomposition of an exponent as `p • μ + ν`
with `ν i < p`. Likewise, since `(p - 1) a ≡ -a` modulo `p`, two residues `a, b < p` with
`p ∣ (p - 1) a + b` are equal.

## Main results

* `Nat.not_dvd_mul_add_sub`: for distinct `a, b < p` with `b ≤ p * m + a`, `p` does not divide
  `p * m + a - b`.
* `Nat.eq_of_dvd_sub_one_mul_add`: for residues `a, b < p`, `p ∣ (p - 1) * a + b` forces `b = a`.
-/

public section

namespace Nat

/-- Two distinct residues modulo `p` do not differ by a multiple of `p`. -/
theorem not_dvd_mul_add_sub {p m a b : ℕ} (ha : a < p) (hb : b < p) (hab : a ≠ b)
    (hle : b ≤ p * m + a) : ¬ p ∣ p * m + a - b := by
  intro h
  have h' : b ≡ p * m + a [MOD p] := (modEq_iff_dvd' hle).mpr h
  have h'' : b ≡ a [MOD p] := h'.trans (by simp [ModEq])
  exact hab (ModEq.eq_of_lt_of_lt h''.symm ha hb)

/-- Two residues `a, b < p` with `p ∣ (p - 1) * a + b` are equal, since `(p - 1) * a ≡ -a`
modulo `p`. -/
theorem eq_of_dvd_sub_one_mul_add {p a b : ℕ} (ha : a < p) (hb : b < p)
    (h : p ∣ (p - 1) * a + b) : b = a := by
  obtain ⟨q, hq⟩ := h
  have hab : p * a + b = p * q + a := by
    rw [← hq, add_right_comm, ← add_one_mul, Nat.sub_add_cancel (by omega)]
  have := congrArg (· % p) hab
  simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

end Nat

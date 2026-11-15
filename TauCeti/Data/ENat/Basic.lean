/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ENat.Monoid

/-!
# Successor inequalities in `ℕ∞`

Depth inequalities for a short exact sequence `0 → A → B → C → 0` bound one depth below by the
minimum of the other two, shifted by one. This file collects the `ℕ∞` arithmetic that combines
such bounds into equalities.

## Main results

* `ENat.le_of_inf_le_of_inf_le`: if `c ⊓ (b + 1) ≤ a` and `c ⊓ (a + 1) ≤ b`, then `c ≤ a`.
* `ENat.add_succ_eq_of_le_of_le`: the bounds `(b + p) ⊓ (b - 1) ≤ a` and `a + 1 ≤ b` give
  `a + (p + 1) = b + p`.
-/

public section

namespace ENat

/-- If `c ⊓ (b + 1) ≤ a` and `c ⊓ (a + 1) ≤ b`, then `c ≤ a`. -/
theorem le_of_inf_le_of_inf_le {a b c : ℕ∞} (ha : c ⊓ (b + 1) ≤ a)
    (hb : c ⊓ (a + 1) ≤ b) : c ≤ a := by
  induction a using ENat.recTopCoe <;> induction b using ENat.recTopCoe <;>
    induction c using ENat.recTopCoe <;> simp_all <;> norm_cast at * <;> omega

/-- If `(b + p) ⊓ (b - 1) ≤ a` and `a + 1 ≤ b`, then `a + (p + 1) = b + p`. -/
theorem add_succ_eq_of_le_of_le {a b : ℕ∞} {p : ℕ}
    (h₁ : (b + p) ⊓ (b - 1) ≤ a) (h₂ : a + 1 ≤ b) : a + (p + 1 : ℕ) = b + p := by
  induction b using ENat.recTopCoe with
  | top => simp_all
  | coe b =>
    induction a using ENat.recTopCoe with
    | top => simp at h₂
    | coe a =>
      norm_cast at h₂ ⊢
      rcases min_le_iff.mp h₁ with h | h <;> norm_cast at h <;> omega

end ENat

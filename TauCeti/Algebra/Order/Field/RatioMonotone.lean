/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith

/-!
# Comparing the terms of a sequence through positive weights

Let `b` be a sequence of positive weights in a linearly ordered field. If a sequence `w` satisfies
`w n ≤ b n / b (n + 1) * w (n + 1)` for every `n`, then the ratios `w n / b n` are nondecreasing,
so `w m ≤ b m / b n * w n` whenever `m ≤ n` (`TauCeti.le_div_mul_of_forall_le_div_mul_succ`).
When the weights lie between `1` and `2`, every term is therefore at most twice any later term.

Mazur's construction of basic subsequences uses this comparison with weights decreasing from a
prescribed basis constant `B > 1` to `1`: the loss `b n / b (n + 1) > 1` allowed at each step of
the selection multiplies to at most `b 0 / b n ≤ B`.
-/

public section

namespace TauCeti

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-- If `w n ≤ b n / b (n + 1) * w (n + 1)` for positive weights `b`, then the ratios `w n / b n`
are nondecreasing, so `w m ≤ b m / b n * w n` whenever `m ≤ n`. -/
theorem le_div_mul_of_forall_le_div_mul_succ {b w : ℕ → α} (hb : ∀ n, 0 < b n)
    (hw : ∀ n, w n ≤ b n / b (n + 1) * w (n + 1)) {m n : ℕ} (hmn : m ≤ n) :
    w m ≤ b m / b n * w n := by
  have hmono : Monotone fun n ↦ w n / b n := monotone_nat_of_le_succ fun n ↦ by
    have h := hw n
    rw [div_mul_eq_mul_div, le_div_iff₀ (hb (n + 1))] at h
    rw [div_le_div_iff₀ (hb n) (hb (n + 1))]
    linarith
  calc w m = w m / b m * b m := (div_mul_cancel₀ _ (hb m).ne').symm
    _ ≤ w n / b n * b m := mul_le_mul_of_nonneg_right (hmono hmn) (hb m).le
    _ = b m / b n * w n := by rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_comm]

end TauCeti

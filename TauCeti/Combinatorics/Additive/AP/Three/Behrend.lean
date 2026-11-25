/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Additive.AP.Three.Behrend

/-!
# Complements to Behrend's construction

Facts about Mathlib's `Behrend.map`, which reads a vector `x : Fin n → ℕ` as the base-`d` digits
of the natural number `∑ k, x k * d ^ k`.

## Main results

* `Behrend.map_lt_pow`: if every coordinate of `x` is less than `d`, then `Behrend.map d x` is
  less than `d ^ n`.
-/

public section

namespace Behrend

/-- If every coordinate of `x` is less than `d`, then `Behrend.map d x < d ^ n`. -/
theorem map_lt_pow {n d : ℕ} {x : Fin n → ℕ} (hx : ∀ k, x k < d) : map d x < d ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := ih (x := x ∘ Fin.succ) fun k => hx k.succ
    have h0 := hx 0
    rw [map_succ', pow_succ]
    linarith [Nat.mul_le_mul_right d (Nat.succ_le_of_lt h)]

end Behrend

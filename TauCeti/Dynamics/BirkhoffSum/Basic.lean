/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Basic

/-!
# Birkhoff sums of iterates

The Birkhoff sums of `birkhoffSum f g k` along the iterate `f^[k]` are the Birkhoff sums of `g`
along `f` at the times `k * n` (`TauCeti.birkhoffSum_iterate_birkhoffSum`).
-/

public section

namespace TauCeti

variable {α M : Type*} [AddCommMonoid M]

/-- The Birkhoff sums of `birkhoffSum f g k` along `f^[k]` at time `n` are the Birkhoff sums of `g`
along `f` at time `k * n`. -/
@[simp]
theorem birkhoffSum_iterate_birkhoffSum (f : α → α) (g : α → M) (k n : ℕ) (x : α) :
    birkhoffSum (f^[k]) (birkhoffSum f g k) n x = birkhoffSum f g (k * n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [birkhoffSum_succ_apply, ih, ← Function.iterate_mul, Nat.mul_succ,
      birkhoffSum_add_right_apply]

end TauCeti

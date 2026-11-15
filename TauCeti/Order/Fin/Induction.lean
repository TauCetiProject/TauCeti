/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Order.Fin.Basic

/-!
# Induction over ordered pairs of a finite ordinal

`Fin.le_induction_castSucc` proves a property of all pairs `i ≤ j` in `Fin (n + 1)` from the
reflexive pairs `i ≤ i` and the step from `i ≤ k.castSucc` to `i ≤ k.succ`, which adds one
consecutive step to the right end. It is the shape of induction used for the arrows `i ⟶ j` of a
string of `n` composable arrows, built up one consecutive arrow at a time.
-/

public section

namespace Fin

/-- Induction over the pairs `i ≤ j` in `Fin (n + 1)`: a property of the reflexive pairs that
passes from `i ≤ k.castSucc` to `i ≤ k.succ` holds for every pair `i ≤ j`. -/
theorem le_induction_castSucc {n : ℕ} {P : ∀ i j : Fin (n + 1), i ≤ j → Prop}
    (refl : ∀ i, P i i le_rfl)
    (succ : ∀ i (k : Fin n) (hik : i ≤ k.castSucc), P i k.castSucc hik →
      P i k.succ (hik.trans k.castSucc_le_succ))
    (i j : Fin (n + 1)) (hij : i ≤ j) : P i j hij := by
  induction j using Fin.induction with
  | zero => obtain rfl := Fin.le_zero_iff.1 hij; exact refl 0
  | succ k ih =>
    by_cases hik : i ≤ k.castSucc
    · exact succ i k hik (ih hik)
    · obtain rfl : i = k.succ := le_antisymm hij (Fin.castSucc_lt_iff_succ_le.1 (not_le.1 hik))
      exact refl _

end Fin

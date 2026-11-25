/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Bitwise

/-!
# Bits of a bitwise operation accumulated over a list

A natural number assembled by folding a bitwise operation over a list, as a mask of chosen bits
is, can be read bit by bit: `Nat.testBit_foldl_or` says that a bit of the inclusive-or of an
initial value and the terms `f i`, for `i` in a list, is set exactly when it is set in the initial
value or in one of the terms.
-/

public section

namespace Nat

variable {α : Type*}

/-- A bit of an inclusive-or accumulated over a list is set exactly when it is set in the initial
value or in one of the terms. -/
theorem testBit_foldl_or (f : α → ℕ) (l : List α) (a p : ℕ) :
    (l.foldl (fun acc i ↦ acc ||| f i) a).testBit p =
      (a.testBit p || l.any fun i ↦ (f i).testBit p) := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, testBit_or, List.any_cons, Bool.or_assoc]

end Nat

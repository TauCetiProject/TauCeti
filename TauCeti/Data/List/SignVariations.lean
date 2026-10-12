/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.List.SignVariations

/-! # Leading signs and variations of lists

The first nonzero sign determines the change in sign variations when a nonzero
entry is prepended to a list.
-/

public section

namespace List

variable {R : Type*} [Zero R] [LinearOrder R]

/-- The sign of the first nonzero entry of a list, or `0` if every entry is zero. -/
def firstSign (l : List R) : SignType :=
  ((l.filter (fun v => decide (v ≠ 0))).head?.map SignType.sign).getD 0

@[simp, grind =]
theorem firstSign_nil : firstSign ([] : List R) = 0 := (rfl)

@[simp, grind =]
theorem firstSign_zero_cons (l : List R) : firstSign (0 :: l) = firstSign l := by
  simp [firstSign]

@[simp, grind =]
theorem firstSign_cons_of_ne_zero {a : R} (l : List R) (ha : a ≠ 0) :
    firstSign (a :: l) = SignType.sign a := by
  simp [firstSign, ha]

/-- Prepending an entry `a` adds one sign variation exactly when its sign is
opposite the sign of the next surviving entry. -/
theorem signVariations_cons {a : R} (l : List R) :
    List.signVariations (a :: l) =
      (if SignType.sign a * firstSign l = -1 then 1 else 0) + List.signVariations l := by
  by_cases ha : a = 0
  · subst a
    simp
  · induction l with
    | nil => simp [firstSign]
    | cons b l ih =>
      by_cases hb : b = 0
      · subst b
        simpa only [List.signVariations_cons_zero_cons, List.signVariations_zero_cons,
          firstSign_zero_cons] using ih
      · rw [firstSign_cons_of_ne_zero l hb, List.signVariations_cons_cons_of_ne_zero l ha hb]
        have ha' : SignType.sign a ≠ 0 := by simpa using ha
        have hb' : SignType.sign b ≠ 0 := by simpa using hb
        have h : (if SignType.sign a = SignType.sign b then (0 : ℕ) else 1) =
            (if SignType.sign a * SignType.sign b = -1 then 1 else 0) := by
          revert ha' hb'
          cases SignType.sign a <;> cases SignType.sign b <;> decide
        rw [h, Nat.add_comm]

end List

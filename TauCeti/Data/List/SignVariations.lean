/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.List.SignVariations

/-! # Leading signs and variations of lists

The first nonzero sign determines the change in sign variations when a nonzero
entry is prepended to a list. Dually, the last nonzero sign `List.lastSign` and
the first nonzero sign of a second list decide whether concatenation creates one
extra variation at the junction (`List.signVariations_append`). Consequences are
invariance under reversal and splitting the count at any nonzero entry. Finally,
scaling every entry by a nonzero element of an ordered ring preserves the count.

These are the append and scaling laws for variations of sign sequences used in
the Sturm and Descartes counting arguments; see Basu–Pollack–Roy, *Algorithms
in Real Algebraic Geometry*, Chapter 2.
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

@[simp, grind =]
theorem firstSign_singleton (a : R) : firstSign [a] = SignType.sign a := by
  by_cases ha : a = 0
  · simp [ha]
  · exact firstSign_cons_of_ne_zero [] ha

/-- A list has leading sign `0` exactly when all its entries vanish. -/
theorem firstSign_eq_zero_iff {l : List R} : firstSign l = 0 ↔ ∀ x ∈ l, x = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases ha : a = 0
    · simp [ha, ih]
    · simp [ha]

/-- The leading sign of a concatenation is that of the first list, unless the
first list vanishes identically. -/
theorem firstSign_append (l₁ l₂ : List R) :
    firstSign (l₁ ++ l₂) = if firstSign l₁ = 0 then firstSign l₂ else firstSign l₁ := by
  induction l₁ with
  | nil => simp
  | cons a l ih =>
    by_cases ha : a = 0
    · simp [ha, ih]
    · simp [firstSign_cons_of_ne_zero _ ha, ha]

/-- A list whose entries all vanish has no sign variations. -/
theorem signVariations_eq_zero_of_forall_eq_zero {l : List R} (h : ∀ x ∈ l, x = 0) :
    List.signVariations l = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [h a mem_cons_self, signVariations_zero_cons]
    exact ih fun x hx => h x (mem_cons_of_mem a hx)

/-- The sign of the last nonzero entry of a list, or `0` if every entry is zero. -/
def lastSign (l : List R) : SignType :=
  firstSign l.reverse

@[simp, grind =]
theorem firstSign_reverse (l : List R) : firstSign l.reverse = lastSign l := (rfl)

@[simp, grind =]
theorem lastSign_reverse (l : List R) : lastSign l.reverse = firstSign l := by
  rw [← firstSign_reverse, reverse_reverse]

@[simp, grind =]
theorem lastSign_nil : lastSign ([] : List R) = 0 := (rfl)

@[simp, grind =]
theorem lastSign_singleton (a : R) : lastSign [a] = SignType.sign a := by
  rw [← firstSign_reverse, reverse_singleton, firstSign_singleton]

/-- A list has trailing sign `0` exactly when all its entries vanish. -/
theorem lastSign_eq_zero_iff {l : List R} : lastSign l = 0 ↔ ∀ x ∈ l, x = 0 := by
  simp [← firstSign_reverse, firstSign_eq_zero_iff]

/-- The trailing sign of a concatenation is that of the second list, unless the
second list vanishes identically. -/
theorem lastSign_append (l₁ l₂ : List R) :
    lastSign (l₁ ++ l₂) = if lastSign l₂ = 0 then lastSign l₁ else lastSign l₂ := by
  simp only [← firstSign_reverse, reverse_append, firstSign_append]

/-- Prepending an entry determines the trailing sign only when the rest of the
list vanishes identically. -/
theorem lastSign_cons (a : R) (l : List R) :
    lastSign (a :: l) = if lastSign l = 0 then SignType.sign a else lastSign l := by
  rw [← singleton_append, lastSign_append, lastSign_singleton]

/-- A list has trailing sign `0` exactly when it has leading sign `0`. -/
theorem lastSign_eq_zero_iff_firstSign_eq_zero {l : List R} :
    lastSign l = 0 ↔ firstSign l = 0 := by
  rw [lastSign_eq_zero_iff, firstSign_eq_zero_iff]

/-- Concatenating two lists adds their sign variations, plus one exactly when the
last nonzero entry of the first list and the first nonzero entry of the second
have opposite signs. -/
theorem signVariations_append (l₁ l₂ : List R) :
    List.signVariations (l₁ ++ l₂) =
      List.signVariations l₁ + (if lastSign l₁ * firstSign l₂ = -1 then 1 else 0) +
        List.signVariations l₂ := by
  induction l₁ with
  | nil => simp
  | cons a l ih =>
    by_cases hl : firstSign l = 0
    · simp [signVariations_cons, firstSign_append, lastSign_cons, ih, hl,
        lastSign_eq_zero_iff_firstSign_eq_zero.mpr hl,
        signVariations_eq_zero_of_forall_eq_zero (firstSign_eq_zero_iff.mp hl)]
    · simp [signVariations_cons, firstSign_append, lastSign_cons, ih, hl,
        lastSign_eq_zero_iff_firstSign_eq_zero.not.mpr hl]
      omega

/-- Reversing a list does not change its sign variations. -/
@[simp]
theorem signVariations_reverse (l : List R) :
    List.signVariations l.reverse = List.signVariations l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [signVariations_append, signVariations_cons, ih, mul_comm]
    omega

/-- The sign variations of a list split at any nonzero entry. -/
theorem signVariations_append_cons_of_ne_zero (l₁ l₂ : List R) {a : R} (ha : a ≠ 0) :
    List.signVariations (l₁ ++ a :: l₂) =
      List.signVariations (l₁ ++ [a]) + List.signVariations (a :: l₂) := by
  rw [signVariations_append, signVariations_append, firstSign_cons_of_ne_zero _ ha,
    firstSign_singleton, signVariations_singleton, add_zero]

end List

namespace List

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Multiplying every entry on the left by a nonzero constant preserves the sign
variations. -/
theorem signVariations_map_mul_left (l : List R) {c : R} (hc : c ≠ 0) :
    List.signVariations (l.map (c * ·)) = List.signVariations l := by
  rcases hc.lt_or_gt with hc | hc
  · exact signVariations_map_of_sign_eq_neg (fun x => by rw [sign_mul, sign_neg hc, neg_one_mul]) l
  · exact signVariations_map (fun x => by rw [sign_mul, sign_pos hc, one_mul]) l

end List

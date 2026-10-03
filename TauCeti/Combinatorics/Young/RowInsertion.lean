/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Sort

/-!
# Row bumping and its inverse

Row insertion replaces the first entry strictly greater than the inserted letter and bumps
that entry to the next row. If there is no such entry, it appends the letter and stops.
The strict comparison is essential: repeated letters remain in the row, as required for
semistandard tableaux with weakly increasing rows and strictly increasing columns.

`TauCeti.rowBump` performs this local step on a list over any linearly ordered alphabet.
Its split characterization specifies both the changed row and the bumped letter. It preserves
weak row order and the combined content of the row and the travelling letter.

Reverse insertion replaces the rightmost entry strictly smaller than the incoming letter.
This is the same operation on the reversed row over the order-dual alphabet.
`TauCeti.rowBump_reverse_of_sortedLE` proves that it recovers a forward bump, including
when a row has repeated entries. These local inverse steps are the operations iterated along
the bumping route in the Robinson--Schensted--Knuth correspondence.

## References

* W. Fulton, *Young Tableaux*, Cambridge University Press (1997), for row insertion and
  reverse row insertion.
-/

public section

namespace TauCeti

variable {α : Type*} [LinearOrder α]

/-- Insert a letter into a row, bumping its first strictly larger entry. If no entry is larger,
append the letter. The second component is the letter to insert into the next row, if any. -/
def rowBump (x : α) : List α → List α × Option α
  | [] => ([x], none)
  | y :: row => if x < y then (x :: row, some y) else
      let result := rowBump x row
      (y :: result.1, result.2)

@[simp]
theorem rowBump_nil (x : α) : rowBump x [] = ([x], none) := (rfl)

/-- Row bumping stops at the first strictly larger entry. -/
theorem rowBump_cons (x y : α) (row : List α) :
    rowBump x (y :: row) = if x < y then (x :: row, some y) else
      (y :: (rowBump x row).1, (rowBump x row).2) := (rfl)

/-- An entry at most the inserted letter is passed without changing it. -/
@[simp]
theorem rowBump_cons_of_le {x y : α} (row : List α) (h : y ≤ x) :
    rowBump x (y :: row) = (y :: (rowBump x row).1, (rowBump x row).2) := by
  simp [rowBump_cons, not_lt.mpr h]

/-- A strictly larger entry is replaced and bumped. -/
@[simp]
theorem rowBump_cons_of_lt {x y : α} (row : List α) (h : x < y) :
    rowBump x (y :: row) = (x :: row, some y) := by
  simp [rowBump_cons, h]

/-- A prefix whose letters are at most the inserted letter is unchanged. -/
theorem rowBump_append (x : α) (before row : List α)
    (h : ∀ z ∈ before, z ≤ x) :
    rowBump x (before ++ row) =
      (before ++ (rowBump x row).1, (rowBump x row).2) := by
  induction before with
  | nil => simp
  | cons z before ih =>
    rw [List.cons_append, rowBump_cons_of_le _ (h z (by simp)),
      ih (fun a ha => h a (by simp [ha]))]
    rfl

/-- Appending occurs precisely when all existing letters are at most the inserted letter. -/
@[simp]
theorem rowBump_snd_eq_none_iff (x : α) (row : List α) :
    (rowBump x row).2 = none ↔ ∀ z ∈ row, z ≤ x := by
  induction row with
  | nil => simp
  | cons y row ih =>
    by_cases h : x < y
    · simp [rowBump_cons_of_lt row h, not_le.mpr h]
    · simp [rowBump_cons_of_le row (not_lt.mp h), ih, not_lt.mp h]

/-- If nothing is bumped, the output row is the original row with the inserted letter appended. -/
theorem rowBump_of_forall_le (x : α) (row : List α) (h : ∀ z ∈ row, z ≤ x) :
    rowBump x row = (row ++ [x], none) := by
  simpa using rowBump_append x row [] h

/-- The full characterization of a bump: a prefix at most `x` is followed by the first entry
`y > x`, and only that entry is replaced. No ordering hypothesis on the row is needed. -/
theorem rowBump_eq_some_iff (x y : α) (row result : List α) :
    rowBump x row = (result, some y) ↔
      ∃ before after, row = before ++ y :: after ∧ result = before ++ x :: after ∧
        (∀ z ∈ before, z ≤ x) ∧ x < y := by
  constructor
  · induction row generalizing result with
    | nil => simp
    | cons z row ih =>
      intro h
      by_cases hxz : x < z
      · rw [rowBump_cons_of_lt row hxz] at h
        have hr : result = x :: row := (congrArg Prod.fst h).symm
        have hy : z = y := Option.some.inj (congrArg Prod.snd h)
        subst y
        exact ⟨[], row, by simp, hr, by simp, hxz⟩
      · rw [rowBump_cons_of_le row (not_lt.mp hxz)] at h
        have hs : (rowBump x row).2 = some y := congrArg Prod.snd h
        obtain ⟨before, after, hp, hr, hle, hxy⟩ :=
          ih (rowBump x row).1 (Prod.ext rfl hs)
        refine ⟨z :: before, after, by simp [hp], ?_, ?_, hxy⟩
        · simpa [hr] using (congrArg Prod.fst h).symm
        · simp only [List.mem_cons, forall_eq_or_imp]
          exact ⟨not_lt.mp hxz, hle⟩
  · rintro ⟨before, after, rfl, rfl, hle, hxy⟩
    rw [rowBump_append x before _ hle, rowBump_cons_of_lt after hxy]

/-- The bumped letter was an entry of the original row. -/
theorem mem_of_rowBump_snd_eq_some {x y : α} {row : List α}
    (h : (rowBump x row).2 = some y) : y ∈ row := by
  obtain ⟨before, after, rfl, _, _, _⟩ :=
    (rowBump_eq_some_iff x y row (rowBump x row).1).mp (Prod.ext rfl h)
  simp

/-- A bumped letter is strictly greater than the inserted letter. -/
theorem lt_of_rowBump_snd_eq_some {x y : α} {row : List α}
    (h : (rowBump x row).2 = some y) : x < y := by
  obtain ⟨_, _, _, _, _, hxy⟩ :=
    (rowBump_eq_some_iff x y row (rowBump x row).1).mp (Prod.ext rfl h)
  exact hxy

/-- Row insertion conserves the letters: the changed row together with the bumped letter
has the content of the original row together with the inserted letter. -/
theorem rowBump_perm (x : α) (row : List α) :
    ((rowBump x row).1 ++ (rowBump x row).2.toList).Perm (x :: row) := by
  induction row with
  | nil => simp
  | cons y row ih =>
    by_cases h : x < y
    · rw [rowBump_cons_of_lt row h]
      simp
    · rw [rowBump_cons_of_le row (not_lt.mp h)]
      exact (ih.cons y).trans (List.Perm.swap x y row)

/-- A bump preserves row length; appending increases it by one. -/
theorem length_rowBump (x : α) (row : List α) :
    (rowBump x row).1.length + (rowBump x row).2.toList.length = row.length + 1 := by
  have h := (rowBump_perm x row).length_eq
  simpa using h

/-- Inserting into a weakly increasing row preserves weak increase. -/
theorem rowBump_sortedLE (x : α) {row : List α} (hrow : row.SortedLE) :
    (rowBump x row).1.SortedLE := by
  cases hs : (rowBump x row).2 with
  | none =>
    have hle := (rowBump_snd_eq_none_iff x row).mp hs
    rw [rowBump_of_forall_le x row hle]
    exact List.sortedLE_append.mpr
      ⟨hrow, List.sortedLE_cons.mpr ⟨by simp, List.sortedLE_nil⟩, by simpa⟩
  | some y =>
    obtain ⟨before, after, hr, hout, hle, hxy⟩ :=
      (rowBump_eq_some_iff x y row (rowBump x row).1).mp (Prod.ext rfl hs)
    rw [hout]
    rw [hr, List.sortedLE_append, List.sortedLE_cons] at hrow
    rw [List.sortedLE_append, List.sortedLE_cons]
    refine ⟨hrow.1, ⟨fun z hz => hxy.le.trans (hrow.2.1.1 z hz), hrow.2.1.2⟩, ?_⟩
    intro a ha z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hle a ha
    · exact hrow.2.2 a ha z (by simp [hz])

/-- Inserting a new letter into a row without repetitions introduces no repetition. -/
theorem rowBump_nodup (x : α) {row : List α} (hrow : row.Nodup) (hx : x ∉ row) :
    (rowBump x row).1.Nodup :=
  (List.nodup_append.mp ((rowBump_perm x row).nodup_iff.mpr
    (List.nodup_cons.mpr ⟨hx, hrow⟩))).1

/-- Inserting a new letter into a strictly increasing row preserves strict increase. -/
theorem rowBump_sortedLT (x : α) {row : List α} (hrow : row.SortedLT) (hx : x ∉ row) :
    (rowBump x row).1.SortedLT :=
  (rowBump_sortedLE x hrow.sortedLE).sortedLT_of_nodup (rowBump_nodup x hrow.nodup hx)

/-- The letters bumped by two successively inserted weakly increasing letters are weakly
increasing. This is the one-row comparison used to propagate the order of bumping routes. -/
theorem rowBump_bumped_le_of_le {x x' y y' : α} {row : List α} (hrow : row.SortedLE)
    (hxx' : x ≤ x') (hfirst : (rowBump x row).2 = some y)
    (hsecond : (rowBump x' (rowBump x row).1).2 = some y') : y ≤ y' := by
  obtain ⟨before, after, hr, hout, hle, _⟩ :=
    (rowBump_eq_some_iff x y row (rowBump x row).1).mp (Prod.ext rfl hfirst)
  rw [hr, List.sortedLE_append, List.sortedLE_cons] at hrow
  have hpassed : ∀ z ∈ before ++ [x], z ≤ x' := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact (hle z hz).trans hxx'
    · simp only [List.mem_singleton] at hz
      exact hz ▸ hxx'
  have hbump : (rowBump x' after).2 = some y' := by
    rw [hout, ← List.singleton_append, ← List.append_assoc,
      rowBump_append x' _ _ hpassed] at hsecond
    exact hsecond
  exact hrow.2.1.1 y' (mem_of_rowBump_snd_eq_some hbump)

/-- Reverse row insertion recovers a forward bump in a weakly increasing row. Reverse insertion
is row bumping on the reversed row with the order reversed, so it replaces the rightmost letter
strictly smaller than the returning letter. -/
theorem rowBump_reverse_of_sortedLE (x y : α) {row : List α} (hrow : row.SortedLE)
    (hbump : (rowBump x row).2 = some y) :
    rowBump (OrderDual.toDual y) ((rowBump x row).1.reverse.map OrderDual.toDual) =
      (row.reverse.map OrderDual.toDual, some (OrderDual.toDual x)) := by
  obtain ⟨before, after, hr, hout, hle, hxy⟩ :=
    (rowBump_eq_some_iff x y row (rowBump x row).1).mp (Prod.ext rfl hbump)
  rw [hr, List.sortedLE_append, List.sortedLE_cons] at hrow
  rw [hout, List.reverse_append, List.reverse_cons, List.map_append, List.map_append]
  have hafter : ∀ z ∈ after.reverse.map OrderDual.toDual, z ≤ OrderDual.toDual y := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    exact hrow.2.1.1 a (List.mem_reverse.mp ha)
  simp only [List.map_cons, List.map_nil, List.singleton_append, List.append_assoc]
  rw [rowBump_append _ _ _ hafter,
    rowBump_cons_of_lt (α := OrderDual α) (x := OrderDual.toDual y)
      (y := OrderDual.toDual x) _ hxy]
  simp [hr, List.reverse_append, List.reverse_cons, List.append_assoc]

end TauCeti

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
`TauCeti.reverseRowBump` exposes this step in the original row orientation.
The recovery theorems prove both inverse directions for bumps in weakly increasing rows,
including when a row has repeated entries. These local inverse steps are iterated along the
bumping route in the Robinson--Schensted--Knuth correspondence.

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
theorem sortedLE_rowBump (x : α) {row : List α} (hrow : row.SortedLE) :
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
theorem nodup_rowBump (x : α) {row : List α} (hrow : row.Nodup) (hx : x ∉ row) :
    (rowBump x row).1.Nodup :=
  (List.nodup_append.mp ((rowBump_perm x row).nodup_iff.mpr
    (List.nodup_cons.mpr ⟨hx, hrow⟩))).1

/-- Inserting a new letter into a strictly increasing row preserves strict increase. -/
theorem sortedLT_rowBump (x : α) {row : List α} (hrow : row.SortedLT) (hx : x ∉ row) :
    (rowBump x row).1.SortedLT :=
  (sortedLE_rowBump x hrow.sortedLE).sortedLT_of_nodup (nodup_rowBump x hrow.nodup hx)

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

/-- Reverse insert a letter by replacing and returning the rightmost strictly smaller entry.
If no entry is smaller, prepend the letter and return `none`. The row is returned in its
original orientation. -/
def reverseRowBump (y : α) (row : List α) : List α × Option α :=
  let result := rowBump (α := OrderDual α) (OrderDual.toDual y) (row.reverse.map OrderDual.toDual)
  (result.1.map OrderDual.ofDual |>.reverse, result.2.map OrderDual.ofDual)

@[simp]
theorem reverseRowBump_nil (y : α) : reverseRowBump y [] = ([y], none) := by
  simp [reverseRowBump]

/-- A suffix whose letters are at least the incoming letter is unchanged. -/
theorem reverseRowBump_append (y : α) (row after : List α)
    (h : ∀ z ∈ after, y ≤ z) :
    reverseRowBump y (row ++ after) =
      ((reverseRowBump y row).1 ++ after, (reverseRowBump y row).2) := by
  have hd : ∀ z ∈ after.reverse.map OrderDual.toDual, z ≤ OrderDual.toDual y := by
    simpa using h
  dsimp only [reverseRowBump]
  simp only [List.reverse_append, List.map_append]
  rw [rowBump_append _ _ _ hd]
  simp [List.map_reverse, List.reverse_append]

/-- A final entry at least the incoming letter is passed without changing it. -/
@[simp]
theorem reverseRowBump_append_singleton_of_le {x y : α} (row : List α) (h : y ≤ x) :
    reverseRowBump y (row ++ [x]) =
      ((reverseRowBump y row).1 ++ [x], (reverseRowBump y row).2) := by
  simpa using reverseRowBump_append y row [x] (by simpa using h)

/-- A strictly smaller final entry is replaced and returned. -/
@[simp]
theorem reverseRowBump_append_singleton_of_lt {x y : α} (row : List α) (h : x < y) :
    reverseRowBump y (row ++ [x]) = (row ++ [y], some x) := by
  simp [reverseRowBump, List.reverse_append, h, List.map_reverse]

/-- Reverse insertion prepends precisely when no entry is strictly smaller. -/
@[simp]
theorem reverseRowBump_snd_eq_none_iff (y : α) (row : List α) :
    (reverseRowBump y row).2 = none ↔ ∀ z ∈ row, y ≤ z := by
  simp [reverseRowBump, rowBump_snd_eq_none_iff]

/-- With no smaller entry to replace, reverse insertion prepends the incoming letter. -/
theorem reverseRowBump_of_forall_le (y : α) (row : List α) (h : ∀ z ∈ row, y ≤ z) :
    reverseRowBump y row = (y :: row, none) := by
  have hd : ∀ z ∈ row.reverse.map OrderDual.toDual, z ≤ OrderDual.toDual y := by
    simpa using h
  dsimp only [reverseRowBump]
  rw [rowBump_of_forall_le _ _ hd]
  simp [List.map_reverse]

/-- Reverse insertion replaces the rightmost entry `x < y`, passing a suffix of entries at
least `y`. No ordering hypothesis on the row is needed. -/
theorem reverseRowBump_eq_some_iff (x y : α) (row result : List α) :
    reverseRowBump y row = (result, some x) ↔
      ∃ before after, row = before ++ x :: after ∧ result = before ++ y :: after ∧
        (∀ z ∈ after, y ≤ z) ∧ x < y := by
  constructor
  · intro h
    have hs : (rowBump (OrderDual.toDual y) (row.reverse.map OrderDual.toDual)).2 =
        some (OrderDual.toDual x) := by
      simpa [reverseRowBump] using congrArg Prod.snd h
    obtain ⟨after, before, hr, hout, hle, hxy⟩ :=
      (rowBump_eq_some_iff (α := OrderDual α) (OrderDual.toDual y)
        (OrderDual.toDual x) _ _).mp (Prod.ext rfl hs)
    refine ⟨before.reverse.map OrderDual.ofDual, after.reverse.map OrderDual.ofDual,
      ?_, ?_, ?_, hxy⟩
    · simpa [List.map_reverse, List.reverse_append, List.reverse_cons, List.append_assoc]
        using congrArg (fun l => (l.map OrderDual.ofDual).reverse) hr
    · have hf := congrArg Prod.fst h
      dsimp only [reverseRowBump] at hf
      have he := congrArg (fun l : List (OrderDual α) => (l.map OrderDual.ofDual).reverse) hout
      simpa [List.map_reverse, List.reverse_append,
        List.reverse_cons, List.append_assoc] using hf.symm.trans he
    · simpa using hle
  · rintro ⟨before, after, rfl, rfl, hle, hxy⟩
    have hd : ∀ z ∈ after.reverse.map OrderDual.toDual, z ≤ OrderDual.toDual y := by
      simpa using hle
    simp only [reverseRowBump, List.reverse_append, List.reverse_cons, List.map_append,
      List.map_cons, List.singleton_append, List.append_assoc]
    rw [rowBump_append _ _ _ hd,
      rowBump_cons_of_lt (α := OrderDual α) (x := OrderDual.toDual y)
        (y := OrderDual.toDual x) _ hxy]
    simp [List.map_reverse, List.reverse_append, List.reverse_cons, List.append_assoc]

/-- The letter returned by reverse insertion was an entry of the original row. -/
theorem mem_of_reverseRowBump_snd_eq_some {x y : α} {row : List α}
    (h : (reverseRowBump y row).2 = some x) : x ∈ row := by
  obtain ⟨before, after, rfl, _, _, _⟩ :=
    (reverseRowBump_eq_some_iff x y row (reverseRowBump y row).1).mp (Prod.ext rfl h)
  simp

/-- A letter returned by reverse insertion is strictly smaller than the incoming letter. -/
theorem lt_of_reverseRowBump_snd_eq_some {x y : α} {row : List α}
    (h : (reverseRowBump y row).2 = some x) : x < y := by
  obtain ⟨_, _, _, _, _, hxy⟩ :=
    (reverseRowBump_eq_some_iff x y row (reverseRowBump y row).1).mp (Prod.ext rfl h)
  exact hxy

/-- Reverse insertion conserves the letters: the changed row together with the returned letter
has the content of the original row together with the incoming letter. -/
theorem reverseRowBump_perm (y : α) (row : List α) :
    ((reverseRowBump y row).1 ++ (reverseRowBump y row).2.toList).Perm (y :: row) := by
  dsimp only [reverseRowBump]
  refine ((List.reverse_perm _).append_right _).trans
    (List.Perm.trans ?_ ((List.reverse_perm row).cons y))
  simpa [Option.toList_map] using (rowBump_perm (OrderDual.toDual y)
    (row.reverse.map OrderDual.toDual)).map OrderDual.ofDual

/-- A reverse bump preserves row length; prepending increases it by one. -/
theorem length_reverseRowBump (y : α) (row : List α) :
    (reverseRowBump y row).1.length + (reverseRowBump y row).2.toList.length =
      row.length + 1 := by
  simpa using (reverseRowBump_perm y row).length_eq

/-- Reverse inserting into a weakly increasing row preserves weak increase. -/
theorem sortedLE_reverseRowBump (y : α) {row : List α} (hrow : row.SortedLE) :
    (reverseRowBump y row).1.SortedLE := by
  have hd : (row.reverse.map OrderDual.toDual).SortedLE :=
    List.sortedLE_map_toDual.mpr hrow.reverse
  simpa [reverseRowBump] using sortedLE_rowBump (OrderDual.toDual y) hd

/-- Reverse inserting a new letter into a row without repetitions introduces no repetition. -/
theorem nodup_reverseRowBump (y : α) {row : List α} (hrow : row.Nodup) (hy : y ∉ row) :
    (reverseRowBump y row).1.Nodup :=
  (List.nodup_append.mp ((reverseRowBump_perm y row).nodup_iff.mpr
    (List.nodup_cons.mpr ⟨hy, hrow⟩))).1

/-- Reverse inserting a new letter into a strictly increasing row preserves strict increase. -/
theorem sortedLT_reverseRowBump (y : α) {row : List α} (hrow : row.SortedLT) (hy : y ∉ row) :
    (reverseRowBump y row).1.SortedLT :=
  (sortedLE_reverseRowBump y hrow.sortedLE).sortedLT_of_nodup
    (nodup_reverseRowBump y hrow.nodup hy)

/-- Reverse insertion recovers a forward bump in a weakly increasing row. -/
theorem reverseRowBump_rowBump_of_sortedLE (x y : α) {row : List α}
    (hrow : row.SortedLE) (hbump : (rowBump x row).2 = some y) :
    reverseRowBump y (rowBump x row).1 = (row, some x) := by
  obtain ⟨before, after, hr, hout, hle, hxy⟩ :=
    (rowBump_eq_some_iff x y row (rowBump x row).1).mp (Prod.ext rfl hbump)
  rw [hr, List.sortedLE_append, List.sortedLE_cons] at hrow
  exact (reverseRowBump_eq_some_iff x y _ row).mpr
    ⟨before, after, hout, hr, hrow.2.1.1, hxy⟩

/-- Forward insertion recovers a reverse bump in a weakly increasing row. -/
theorem rowBump_reverseRowBump_of_sortedLE (x y : α) {row : List α}
    (hrow : row.SortedLE) (hbump : (reverseRowBump y row).2 = some x) :
    rowBump x (reverseRowBump y row).1 = (row, some y) := by
  obtain ⟨before, after, hr, hout, hle, hxy⟩ :=
    (reverseRowBump_eq_some_iff x y row (reverseRowBump y row).1).mp (Prod.ext rfl hbump)
  rw [hr, List.sortedLE_append] at hrow
  exact (rowBump_eq_some_iff x y _ row).mpr
    ⟨before, after, hout, hr, fun z hz => hrow.2.2 z hz x (by simp), hxy⟩

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Nat.Find

/-!
# Maximal blocks of a list with respect to a set of exceptional words

Let `E` be a finite set of lists, the *exceptions*. A list is cut into *maximal blocks*
(`List.maximalBlocks`) by reading it from the left and taking at each position the longest
exception of length at least two that begins there, or the single entry there if there is none.
When the exceptions satisfy the overlap condition of [IFT], Lemma 51 (if `w₁ ++ w₂` and `w₂ ++ w₃`
are exceptions occurring in a word, so is `w₁ ++ w₂ ++ w₃`), this greedy decomposition is the
decomposition of the word into maximal occurrences of letters and exceptions, the irreducible
decomposition of [IFT], Definition 31.

## Main definitions

* `List.maximalBlocks`: the decomposition of a list into maximal blocks.

## Main results

* `List.flatten_maximalBlocks`: the blocks concatenate to the list.
* `List.mem_maximalBlocks`: every block is an entry or an exception.
* `List.maximalBlocks_append_of_maximal`: the first block is the longest exception at the front of
  the list, or its first entry if no exception of length at least two is a prefix of the list.
* `List.maximalBlocks_eq_cons_iff`: the maximal blocks of a list are `u :: us` exactly when `u` is
  such a first block and `us` are the maximal blocks of the rest.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §7.1, Definition 31 and Lemma 51.
-/

public section

namespace List

variable {β : Type*} [DecidableEq β]

/-- The length of the first maximal block of a list: the length of its longest prefix of length at
least two that is an exception, or `1` if there is none. -/
private def firstBlockLength (E : Finset (List β)) (l : List β) : ℕ :=
  max 1 (Nat.findGreatest (fun k => 2 ≤ k ∧ l.take k ∈ E) l.length)

/-- The decomposition into maximal blocks, with fuel `k` (the length of the list suffices, since
every block is nonempty). -/
private def maximalBlocksAux (E : Finset (List β)) : ℕ → List β → List (List β)
  | 0, _ => []
  | _, [] => []
  | k + 1, l@(_ :: _) =>
    l.take (firstBlockLength E l) :: maximalBlocksAux E k (l.drop (firstBlockLength E l))

/-- The decomposition of a list into maximal blocks with respect to a finite set `E` of exceptions
([IFT], Definition 31): reading from the left, the next block is the longest exception of length at
least two that is a prefix of the rest of the list, or the next entry if there is none. -/
def maximalBlocks (E : Finset (List β)) (l : List β) : List (List β) :=
  maximalBlocksAux E l.length l

section Aux

variable {E : Finset (List β)}

private theorem one_le_firstBlockLength (l : List β) : 1 ≤ firstBlockLength E l :=
  le_max_left _ _

private theorem firstBlockLength_le_length {l : List β} (hl : l ≠ []) :
    firstBlockLength E l ≤ l.length :=
  max_le (length_pos_iff.2 hl) (Nat.findGreatest_le _)

private theorem le_firstBlockLength {l : List β} {n : ℕ} (hn : n ≤ l.length) (h2 : 2 ≤ n)
    (hE : l.take n ∈ E) : n ≤ firstBlockLength E l :=
  le_max_of_le_right (Nat.le_findGreatest hn ⟨h2, hE⟩)

private theorem firstBlockLength_le {l : List β} {n : ℕ} (hn : 1 ≤ n)
    (h : ∀ v ∈ E, v <+: l → 2 ≤ v.length → v.length ≤ n) : firstBlockLength E l ≤ n := by
  refine max_le hn ?_
  obtain h0 | h0 := eq_or_ne (Nat.findGreatest (fun k => 2 ≤ k ∧ l.take k ∈ E) l.length) 0
  · lia
  obtain ⟨h2, hE⟩ := Nat.findGreatest_of_ne_zero rfl h0
  have := h _ hE (take_prefix _ _)
  rw [length_take_of_le (Nat.findGreatest_le _)] at this
  exact this h2

-- The first block is a single entry or an exception of length at least two.
private theorem take_firstBlockLength {l : List β} (hl : l ≠ []) :
    (l.take (firstBlockLength E l)).length = 1 ∨
      2 ≤ (l.take (firstBlockLength E l)).length ∧ l.take (firstBlockLength E l) ∈ E := by
  rw [length_take_of_le (firstBlockLength_le_length hl)]
  unfold firstBlockLength
  obtain h0 | h0 := eq_or_ne (Nat.findGreatest (fun k => 2 ≤ k ∧ l.take k ∈ E) l.length) 0
  · simp [h0]
  · rw [max_eq_right (by lia)]
    exact .inr (Nat.findGreatest_of_ne_zero rfl h0)

-- The fuel does not matter once it is at least the length of the list.
private theorem maximalBlocksAux_congr {k₁ k₂ : ℕ} {l : List β} (h₁ : l.length ≤ k₁)
    (h₂ : l.length ≤ k₂) : maximalBlocksAux E k₁ l = maximalBlocksAux E k₂ l := by
  induction k₁ generalizing k₂ l with
  | zero => cases k₂ <;> simp_all [maximalBlocksAux]
  | succ k₁ ih =>
    rcases l with _ | ⟨a, l⟩
    · cases k₂ <;> simp [maximalBlocksAux]
    obtain ⟨k₂, rfl⟩ : ∃ k, k₂ = k + 1 := ⟨k₂ - 1, by simp at h₂; lia⟩
    have := one_le_firstBlockLength (E := E) (a :: l)
    simp only [maximalBlocksAux, cons.injEq, true_and]
    exact ih (by simp at h₁ ⊢; lia) (by simp at h₂ ⊢; lia)

-- Unfolding `maximalBlocks` on a nonempty list.
private theorem maximalBlocks_of_ne_nil {l : List β} (hl : l ≠ []) :
    maximalBlocks E l = l.take (firstBlockLength E l) ::
      maximalBlocks E (l.drop (firstBlockLength E l)) := by
  obtain ⟨a, l, rfl⟩ := exists_cons_of_ne_nil hl
  have := one_le_firstBlockLength (E := E) (a :: l)
  simp only [maximalBlocks, length_cons, maximalBlocksAux, cons.injEq, true_and]
  exact maximalBlocksAux_congr (by simp; lia) le_rfl

-- Induction on a list along its maximal blocks.
private theorem maximalBlocks_induction {motive : List β → Prop} (nil : motive [])
    (cons : ∀ l, l ≠ [] → motive (l.drop (firstBlockLength E l)) → motive l) (l : List β) :
    motive l := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    rcases eq_or_ne l [] with rfl | hl
    · exact nil
    have := one_le_firstBlockLength (E := E) l
    have := length_pos_iff.2 hl
    exact cons l hl (ih _ (by simp only [length_drop]; lia) _ rfl)

end Aux

/-- The empty list has no blocks. -/
@[simp]
theorem maximalBlocks_nil (E : Finset (List β)) : maximalBlocks E [] = [] :=
  (rfl)

/-- The maximal blocks of a list concatenate to the list. -/
@[simp]
theorem flatten_maximalBlocks (E : Finset (List β)) (l : List β) :
    (maximalBlocks E l).flatten = l := by
  induction l using maximalBlocks_induction (E := E) with
  | nil => simp
  | cons l hl ih => rw [maximalBlocks_of_ne_nil hl, flatten_cons, ih, take_append_drop]

/-- Every maximal block is a single entry or an exception of length at least two. -/
theorem mem_maximalBlocks {E : Finset (List β)} {l u : List β} (hu : u ∈ maximalBlocks E l) :
    u.length = 1 ∨ 2 ≤ u.length ∧ u ∈ E := by
  induction l using maximalBlocks_induction (E := E) with
  | nil => simp at hu
  | cons l hl ih =>
    rw [maximalBlocks_of_ne_nil hl, mem_cons] at hu
    rcases hu with rfl | hu
    exacts [take_firstBlockLength hl, ih hu]

/-- The maximal blocks of `u ++ l` are `u` followed by the maximal blocks of `l` if `u` is a single
entry or an exception of length at least two, and no longer exception of length at least two is a
prefix of `u ++ l`. Together with `List.maximalBlocks_nil` this determines `List.maximalBlocks`. -/
theorem maximalBlocks_append_of_maximal {E : Finset (List β)} {u l : List β}
    (hu : u.length = 1 ∨ 2 ≤ u.length ∧ u ∈ E)
    (hmax : ∀ v ∈ E, v <+: u ++ l → 2 ≤ v.length → v.length ≤ u.length) :
    maximalBlocks E (u ++ l) = u :: maximalBlocks E l := by
  have hu₁ : 1 ≤ u.length := by rcases hu with hu | ⟨hu, -⟩ <;> lia
  -- The first block has the length of `u`: no longer exception is a prefix, and `u` is one.
  have hfirst : firstBlockLength E (u ++ l) = u.length := by
    refine le_antisymm (firstBlockLength_le hu₁ hmax) ?_
    rcases hu with hu | ⟨h2, hE⟩
    · rw [hu]
      exact one_le_firstBlockLength _
    · exact le_firstBlockLength (by simp) h2 (by simpa using hE)
  rw [maximalBlocks_of_ne_nil (ne_nil_of_length_pos (by simp; lia)), hfirst, take_left, drop_left]

/-- The maximal blocks of `l` are `u :: us` if and only if `l` is `u ++ us.flatten`, `u` is a single
entry or an exception of length at least two, no longer exception of length at least two is a
prefix of `l`, and `us` are the maximal blocks of their concatenation. -/
theorem maximalBlocks_eq_cons_iff {E : Finset (List β)} {l u : List β} {us : List (List β)} :
    maximalBlocks E l = u :: us ↔ l = u ++ us.flatten ∧ (u.length = 1 ∨ 2 ≤ u.length ∧ u ∈ E) ∧
      (∀ v ∈ E, v <+: l → 2 ≤ v.length → v.length ≤ u.length) ∧
      maximalBlocks E us.flatten = us := by
  refine ⟨fun h => ?_, ?_⟩
  · have hl : l ≠ [] := by rintro rfl; simp at h
    rw [maximalBlocks_of_ne_nil hl, cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by rw [flatten_maximalBlocks, take_append_drop], take_firstBlockLength hl, ?_,
      by rw [flatten_maximalBlocks]⟩
    -- The first block is at least as long as every exceptional prefix of length at least two.
    rintro v hv ⟨t, rfl⟩ h2
    rw [length_take_of_le (firstBlockLength_le_length hl)]
    exact le_firstBlockLength (by simp) h2 (by simpa using hv)
  · rintro ⟨rfl, hu, hmax, hus⟩
    rw [maximalBlocks_append_of_maximal hu hmax, hus]

/-- With the exceptions `0 1` and `0 1 2`, the list `0 1 2 0 3` is cut as `(0 1 2) 0 3`: the longest
exception at the front is taken. -/
example : maximalBlocks {[0, 1], [0, 1, 2]} [0, 1, 2, 0, 3] = [[0, 1, 2], [0], [3]] := by
  decide

/-- With the overlapping exceptions `0 1` and `1 2`, the list `0 1 2` is cut as `(0 1) 2`: the
greedy decomposition reads from the left. Here `0 1 2` is not an exception, so the overlap condition
of [IFT], Lemma 51 fails, and both occurrences of exceptions are maximal. -/
example : maximalBlocks {[0, 1], [1, 2]} [0, 1, 2] = [[0, 1], [2]] := by
  decide

end List

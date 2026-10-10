/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.Schensted

/-!
# The Robinson--Schensted correspondence for words

Inserting the letters of a word `w = w₁ w₂ ⋯ wₙ` one after another into the empty tableau by
Schensted row insertion gives its **insertion tableau** `P(w) = (⋯((∅ ← w₁) ← w₂) ⋯) ← wₙ`.
Recording, for each `k`, the row `rₖ` in which the insertion of `wₖ` adds its new cell gives its
**recording word** `r₁ r₂ ⋯ rₙ`. The recording word is the row-by-row record of the usual
recording tableau `Q(w)`, the standard tableau with the entry `k` in the cell added at step `k`:
a standard tableau is determined by the row of each of its entries, and the words arising this
way from standard tableaux of shape `λ` are exactly the lattice words in which each letter `i`
occurs `λᵢ` times.

The **Robinson--Schensted correspondence** `TauCeti.robinsonSchenstedEquiv` says that
`w ↦ (P(w), r(w))` is a bijection from words onto the pairs of a semistandard tableau `P` and a
lattice word `r` such that row `i` of `P` has as many cells as `r` has letters `i`. Injectivity and
surjectivity both follow, one letter at a time, from the fact that a single row insertion is a
bijection onto tableaux with a chosen corner (`TauCeti.rowInsertEquiv`). For a word without
repeated letters, such as a permutation in one-line notation, the insertion tableau has distinct
entries (`TauCeti.flatten_robinsonSchensted_fst_perm`); this is the case underlying the classical
bijection between permutations and pairs of standard tableaux of the same shape.

## Main definitions

* `List.IsLatticeWord`: a lattice word, in which every prefix contains each letter `i` at least as
  often as `i + 1`.
* `TauCeti.robinsonSchensted`: the insertion tableau and the recording word of a word.
* `TauCeti.robinsonSchenstedEquiv`: the Robinson--Schensted correspondence, as a bijection.

## Main statements

* `TauCeti.flatten_robinsonSchensted_fst_perm`: the insertion tableau has the letters of the word.
* `TauCeti.length_getD_robinsonSchensted_fst`: the shape of the insertion tableau is the content of
  the recording word.
* `TauCeti.isLatticeWord_robinsonSchensted_snd`: the recording word is a lattice word.
* `TauCeti.robinsonSchensted_injective` and `TauCeti.exists_robinsonSchensted_eq_iff`: the
  correspondence is injective, and its image is described by the three properties above.

## References

* W. Fulton, *Young Tableaux*, Cambridge University Press (1997), Section 4.1.
* B. E. Sagan, *The Symmetric Group*, 2nd ed., Springer GTM 203 (2001), Sections 3.1 and 3.3.
* C. Schensted, *Longest increasing and decreasing subsequences*, Canad. J. Math. 13 (1961).
-/

public section

namespace List

/-- A **lattice word** (also called a Yamanouchi word or a ballot sequence) is a word in the
letters `0, 1, 2, …` every prefix of which contains the letter `i` at least as often as the
letter `i + 1`. -/
def IsLatticeWord (r : List ℕ) : Prop :=
  ∀ p, p <+: r → ∀ i, p.count (i + 1) ≤ p.count i

/-- Unfolds `List.IsLatticeWord`. -/
theorem isLatticeWord_iff {r : List ℕ} :
    r.IsLatticeWord ↔ ∀ p, p <+: r → ∀ i, p.count (i + 1) ≤ p.count i :=
  Iff.rfl

/-- The empty word is a lattice word. -/
@[simp]
theorem isLatticeWord_nil : IsLatticeWord [] := by
  intro p hp i
  simp [prefix_nil.mp hp]

/-- A prefix of a lattice word is a lattice word. -/
theorem IsLatticeWord.of_prefix {r s : List ℕ} (h : r.IsLatticeWord) (hs : s <+: r) :
    s.IsLatticeWord :=
  fun p hp => h p (hp.trans hs)

/-- A lattice word contains each letter `i` at least as often as the letter `i + 1`. -/
theorem IsLatticeWord.count_succ_le {r : List ℕ} (h : r.IsLatticeWord) (i : ℕ) :
    r.count (i + 1) ≤ r.count i :=
  h r (prefix_refl r) i

/-- A word ending in the letter `k` is a lattice word exactly when the rest of it is a lattice
word which, if `k = i + 1`, contains `k` strictly fewer times than `i`. -/
theorem isLatticeWord_append_singleton {r : List ℕ} {k : ℕ} :
    (r ++ [k]).IsLatticeWord ↔
      r.IsLatticeWord ∧ ∀ i, k = i + 1 → r.count (i + 1) < r.count i := by
  constructor
  · intro h
    refine ⟨h.of_prefix (prefix_append r [k]), fun i hk => ?_⟩
    have := h.count_succ_le i
    simp only [count_append, count_singleton, beq_iff_eq] at this
    split_ifs at this <;> omega
  · rintro ⟨h, hk⟩ p hp i
    rcases prefix_concat_iff.mp hp with rfl | hp
    · have := h.count_succ_le i
      simp only [count_append, count_singleton, beq_iff_eq]
      by_cases hki : k = i + 1
      · have := hk i hki
        split_ifs <;> omega
      · split_ifs <;> omega
    · exact h p hp i

end List

namespace TauCeti

open List

variable {α : Type*} [LinearOrder α]

/-- The **Robinson--Schensted correspondence** of a word `w₁ w₂ ⋯ wₙ`: the rows of its insertion
tableau `(⋯((∅ ← w₁) ← w₂) ⋯) ← wₙ`, together with its recording word, whose `k`-th letter is the
row in which the insertion of `wₖ` adds its new cell. -/
def robinsonSchensted (w : List α) : List (List α) × List ℕ :=
  w.foldl (fun p x => (rowInsert x p.1, p.2 ++ [rowInsertIndex x p.1])) ([], [])

/-- The empty word has the empty tableau and the empty recording word. -/
@[simp]
theorem robinsonSchensted_nil : robinsonSchensted ([] : List α) = ([], []) := (rfl)

/-- Appending a letter `x` to a word inserts `x` into its insertion tableau, and appends to its
recording word the row of the new cell. -/
@[simp]
theorem robinsonSchensted_append_singleton (w : List α) (x : α) :
    robinsonSchensted (w ++ [x]) =
      (rowInsert x (robinsonSchensted w).1,
        (robinsonSchensted w).2 ++ [rowInsertIndex x (robinsonSchensted w).1]) := by
  simp [robinsonSchensted]

/-- The insertion tableau of a word is a tableau. -/
theorem isTableauRows_robinsonSchensted_fst (w : List α) :
    (robinsonSchensted w).1.IsTableauRows := by
  induction w using reverseRecOn with
  | nil => simp
  | append_singleton w x ih => simpa using ih.rowInsert x

/-- **The insertion tableau has the letters of the word.** -/
theorem flatten_robinsonSchensted_fst_perm (w : List α) :
    (robinsonSchensted w).1.flatten.Perm w := by
  induction w using reverseRecOn with
  | nil => simp
  | append_singleton w x ih =>
    rw [robinsonSchensted_append_singleton]
    exact (flatten_rowInsert_perm x _).trans ((ih.cons x).trans (perm_append_singleton x w).symm)

/-- The recording word has one letter for each letter of the word. -/
@[simp]
theorem length_robinsonSchensted_snd (w : List α) :
    (robinsonSchensted w).2.length = w.length := by
  induction w using reverseRecOn with
  | nil => simp
  | append_singleton w x ih => simp [ih]

/-- **The shape of the insertion tableau is the content of the recording word**: row `i` of the
insertion tableau has as many cells as the recording word has letters `i`. -/
theorem length_getD_robinsonSchensted_fst (w : List α) (i : ℕ) :
    ((robinsonSchensted w).1.getD i []).length = (robinsonSchensted w).2.count i := by
  induction w using reverseRecOn with
  | nil => simp
  | append_singleton w x ih =>
    simp only [robinsonSchensted_append_singleton, length_getD_rowInsert, ih, count_append,
      count_singleton, beq_iff_eq]
    split_ifs <;> omega

/-- **The recording word is a lattice word.** -/
theorem isLatticeWord_robinsonSchensted_snd (w : List α) :
    (robinsonSchensted w).2.IsLatticeWord := by
  induction w using reverseRecOn with
  | nil => simp
  | append_singleton w x ih =>
    rw [robinsonSchensted_append_singleton, isLatticeWord_append_singleton]
    refine ⟨ih, fun i hi => ?_⟩
    rw [← length_getD_robinsonSchensted_fst, ← length_getD_robinsonSchensted_fst]
    exact length_getD_succ_lt_of_rowInsertIndex_eq_succ (isTableauRows_robinsonSchensted_fst w) hi

/-- **The Robinson--Schensted correspondence is injective**: a word is determined by its
insertion tableau and its recording word. -/
theorem robinsonSchensted_injective : Function.Injective (robinsonSchensted (α := α)) := by
  intro w v h
  induction w using reverseRecOn generalizing v with
  | nil =>
    have := congrArg (fun p => p.2.length) h
    simp only [robinsonSchensted_nil, length_nil, length_robinsonSchensted_snd] at this
    exact (length_eq_zero_iff.mp this.symm).symm
  | append_singleton w x ih =>
    obtain rfl | ⟨v, y, rfl⟩ := v.eq_nil_or_concat'
    · have := congrArg (fun p => p.2.length) h
      simp at this
    simp only [robinsonSchensted_append_singleton, Prod.mk.injEq, append_singleton_inj] at h
    obtain ⟨hins, hrec, hidx⟩ := h
    -- A single row insertion is injective, so the last letters and the earlier tableaux agree.
    have := rowInsertEquiv.injective (a₁ := (⟨_, isTableauRows_robinsonSchensted_fst w⟩, x))
      (a₂ := (⟨_, isTableauRows_robinsonSchensted_fst v⟩, y))
      (Subtype.ext (by simp [hins, hidx]))
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at this
    rw [ih (Prod.ext this.1 hrec), this.2]

/-- **The image of the Robinson--Schensted correspondence**: a pair of a list of rows and a word
of row indices consists of the insertion tableau and the recording word of some word exactly when
the rows form a tableau, the word is a lattice word, and row `i` has as many cells as the word has
letters `i`. -/
theorem exists_robinsonSchensted_eq_iff {p : List (List α) × List ℕ} :
    (∃ w, robinsonSchensted w = p) ↔
      p.1.IsTableauRows ∧ p.2.IsLatticeWord ∧ ∀ i, (p.1.getD i []).length = p.2.count i := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨isTableauRows_robinsonSchensted_fst w, isLatticeWord_robinsonSchensted_snd w,
      length_getD_robinsonSchensted_fst w⟩
  obtain ⟨P, r⟩ := p
  rintro ⟨hP, hr, hshape⟩
  induction r using reverseRecOn generalizing P with
  | nil =>
    cases P with
    | nil => exact ⟨[], rfl⟩
    | cons row rows =>
      have := hshape 0
      simp only [getD_cons_zero, count_nil, length_eq_zero_iff] at this
      exact absurd this (isTableauRows_cons.mp hP).1
  | append_singleton r k ih =>
    obtain ⟨hr', _⟩ := isLatticeWord_append_singleton.mp hr
    -- Row `k` of `P` ends in a corner, so reverse insertion from it undoes a row insertion.
    have hcorner : (P.getD (k + 1) []).length < (P.getD k []).length := by
      have := hr'.count_succ_le k
      simp only [hshape, count_append, count_singleton, beq_iff_eq]
      split_ifs <;> omega
    obtain ⟨x, -, hins, hidx⟩ := rowInsert_reverseRowInsert hP hcorner
    have hshape' (i : ℕ) : ((reverseRowInsert k P).1.getD i []).length = r.count i := by
      have := length_getD_rowInsert x (reverseRowInsert k P).1 i
      rw [hins, hidx, hshape, count_append, count_singleton] at this
      simp only [beq_iff_eq] at this
      split_ifs at this <;> omega
    obtain ⟨w, hw⟩ := ih _ (hP.reverseRowInsert hcorner) hr' hshape'
    exact ⟨w ++ [x], by simp [hw, hins, hidx]⟩

/-- **The Robinson--Schensted correspondence**: inserting the letters of a word into the empty
tableau and recording the rows of the new cells is a bijection from words onto the pairs of a
tableau and a lattice word such that row `i` of the tableau has as many cells as the lattice word
has letters `i`. -/
noncomputable def robinsonSchenstedEquiv :
    List α ≃ {p : List (List α) × List ℕ //
      p.1.IsTableauRows ∧ p.2.IsLatticeWord ∧ ∀ i, (p.1.getD i []).length = p.2.count i} :=
  Equiv.ofBijective (fun w => ⟨robinsonSchensted w, exists_robinsonSchensted_eq_iff.mp ⟨w, rfl⟩⟩)
    ⟨fun _ _ h => robinsonSchensted_injective (congrArg Subtype.val h),
      fun p => (exists_robinsonSchensted_eq_iff.mpr p.2).imp fun _ hw => Subtype.ext hw⟩

/-- `robinsonSchenstedEquiv` sends a word to its insertion tableau and recording word. -/
@[simp]
theorem robinsonSchenstedEquiv_apply_coe (w : List α) :
    (robinsonSchenstedEquiv w : List (List α) × List ℕ) = robinsonSchensted w := (rfl)

end TauCeti

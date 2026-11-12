/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Sort
public import Mathlib.Data.Set.Finite.Lattice
public import TauCeti.Data.List.Infix
public import TauCeti.GroupTheory.FreeGroup.CyclicallyReduced

/-!
# Merzljakov words

For two letters `a`, `b` and a list of exponents `m₁, …, m_n`, the *Merzljakov word* is the
positive word `b a^{m₁} b a^{m₂} b ⋯ a^{m_n} b`, and its *blocks* are the subwords `b a^{m_i} b`;
consecutive blocks overlap in one letter `b`. These words are the test values substituted for the
universally quantified variables in the proof of Merzljakov's theorem on positive sentences of
free groups: their blocks can be recognised inside any factorisation of the word.

This file records the combinatorics of these words which that proof uses. Here a word is a list
of signed letters `α × Bool` and a subword is an infix, `List.IsInfix`.

## Main definitions

* `FreeGroup.merzljakovBlock a b m`: the block `b a^m b`.
* `FreeGroup.merzljakovWord a b ms`: the word `b a^{m₁} b ⋯ a^{m_n} b` with exponent list `ms`.

## Main results

* `FreeGroup.isCyclicallyReduced_merzljakovWord`: a Merzljakov word is cyclically reduced.
* `FreeGroup.append_merzljakovBlock_append_eq_merzljakovWord_iff`: for `a ≠ b`, the occurrences
  of a block `b a^m b` in a Merzljakov word are exactly the splittings of its exponent list at an
  entry `m`.
* `FreeGroup.merzljakovBlock_isInfix_merzljakovWord_iff`: for `a ≠ b`, the block `b a^m b` occurs
  in a Merzljakov word exactly when `m` is one of its exponents.
* `FreeGroup.existsUnique_append_merzljakovBlock_append_eq`: for `a ≠ b` and pairwise distinct
  exponents, each block occurs exactly once.
* `FreeGroup.not_merzljakovBlock_isInfix_invRev_merzljakovWord`: no block occurs in the inverse
  of a Merzljakov word.
* `FreeGroup.exists_merzljakovBlock_isInfix_of_isInfix_flatten`: if a Merzljakov word with `n`
  exponents occurs in a concatenation of at most `n` words, then one of these words contains a
  whole block.
* `FreeGroup.exists_sortedLT_forall_not_merzljakovBlock_isInfix`: for finitely many given words
  and every `n` there are `n` strictly increasing exponents none of whose blocks occurs in a
  given word.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), 1–203, Section 4.4, proof of Merzljakov's Theorem.
* Yu. I. Merzljakov, *Positive formulae on free groups*, Algebra i Logika 5 (1966), 25–42.
-/

public section

namespace FreeGroup

open List

variable {α : Type*} {a b : α} {m : ℕ} {ms : List ℕ}

/-- The block `b a^m b`, as a positive word. -/
def merzljakovBlock (a b : α) (m : ℕ) : List (α × Bool) :=
  (b, true) :: (replicate m (a, true) ++ [(b, true)])

/-- The Merzljakov word `b a^{m₁} b a^{m₂} b ⋯ a^{m_n} b` with exponent list
`ms = [m₁, …, m_n]`, as a positive word. For the empty exponent list it is the letter `b`. -/
def merzljakovWord (a b : α) (ms : List ℕ) : List (α × Bool) :=
  (b, true) :: ms.flatMap fun m ↦ replicate m (a, true) ++ [(b, true)]

/-- The block `b a^m b` consists of the letter `b`, then `m` letters `a`, then the letter `b`. -/
theorem merzljakovBlock_eq (a b : α) (m : ℕ) :
    merzljakovBlock a b m = (b, true) :: (replicate m (a, true) ++ [(b, true)]) :=
  (rfl)

/-- The Merzljakov word with no exponents is the letter `b`. -/
@[simp]
theorem merzljakovWord_nil (a b : α) : merzljakovWord a b [] = [(b, true)] :=
  (rfl)

/-- A Merzljakov word with first exponent `m` is `b a^m` followed by the Merzljakov word of the
remaining exponents. -/
theorem merzljakovWord_cons (a b : α) (m : ℕ) (ms : List ℕ) :
    merzljakovWord a b (m :: ms) =
      (b, true) :: (replicate m (a, true) ++ merzljakovWord a b ms) := by
  simp [merzljakovWord]

/-- The Merzljakov word with a single exponent `m` is the block `b a^m b`. -/
@[simp]
theorem merzljakovWord_singleton (a b : α) (m : ℕ) :
    merzljakovWord a b [m] = merzljakovBlock a b m := by
  simp [merzljakovWord, merzljakovBlock]

/-- Splitting the exponent list at an entry `m` splits the Merzljakov word into the Merzljakov
words of the two parts, joined by `a^m`. -/
theorem merzljakovWord_append_cons (a b : α) (ms₁ : List ℕ) (m : ℕ) (ms₂ : List ℕ) :
    merzljakovWord a b (ms₁ ++ m :: ms₂) =
      merzljakovWord a b ms₁ ++ (replicate m (a, true) ++ merzljakovWord a b ms₂) := by
  simp [merzljakovWord]

/-- A Merzljakov word begins with the letter `b`. -/
@[simp]
theorem head?_merzljakovWord (a b : α) (ms : List ℕ) :
    (merzljakovWord a b ms).head? = some (b, true) :=
  (rfl)

/-- The block `b a^m b` has `m + 2` letters. -/
@[simp]
theorem length_merzljakovBlock (a b : α) (m : ℕ) : (merzljakovBlock a b m).length = m + 2 := by
  simp [merzljakovBlock]

/-- The Merzljakov word with exponents `m₁, …, m_n` has `m₁ + ⋯ + m_n + n + 1` letters. -/
@[simp]
theorem length_merzljakovWord (a b : α) (ms : List ℕ) :
    (merzljakovWord a b ms).length = ms.sum + ms.length + 1 := by
  induction ms with
  | nil => simp
  | cons m ms ih =>
    simp [merzljakovWord_cons, ih]
    omega

/-- Every letter of a Merzljakov word is positive. -/
theorem snd_eq_true_of_mem_merzljakovWord {x : α × Bool} (hx : x ∈ merzljakovWord a b ms) :
    x.2 = true := by
  induction ms with
  | nil => simp_all
  | cons m ms ih =>
    rw [merzljakovWord_cons, mem_cons, mem_append, mem_replicate] at hx
    rcases hx with rfl | ⟨-, rfl⟩ | hx
    exacts [rfl, rfl, ih hx]

/-- A Merzljakov word is reduced. -/
@[simp]
theorem isReduced_merzljakovWord (a b : α) (ms : List ℕ) : IsReduced (merzljakovWord a b ms) :=
  isReduced_of_forall_snd_eq fun _ ↦ snd_eq_true_of_mem_merzljakovWord

/-- A Merzljakov word is cyclically reduced. -/
@[simp]
theorem isCyclicallyReduced_merzljakovWord (a b : α) (ms : List ℕ) :
    IsCyclicallyReduced (merzljakovWord a b ms) :=
  isCyclicallyReduced_of_forall_snd_eq fun _ ↦ snd_eq_true_of_mem_merzljakovWord

/-- Free reduction leaves a Merzljakov word unchanged, so it is the reduced word of the element
it represents. -/
@[simp]
theorem reduce_merzljakovWord [DecidableEq α] (a b : α) (ms : List ℕ) :
    reduce (merzljakovWord a b ms) = merzljakovWord a b ms :=
  (isReduced_merzljakovWord a b ms).reduce_eq

/-- The Merzljakov word with exponents `m₁, …, m_n` represents the element
`b a^{m₁} b ⋯ a^{m_n} b` of the free group. -/
theorem mk_merzljakovWord (a b : α) (ms : List ℕ) :
    mk (merzljakovWord a b ms) = of b * (ms.map fun m ↦ of a ^ m * of b).prod := by
  induction ms with
  | nil => simp [of]
  | cons m ms ih =>
    have hm : mk (replicate m (a, true)) = of a ^ m := by
      rw [of, pow_mk, flatten_replicate_singleton]
    rw [merzljakovWord_cons, map_cons, prod_cons, ← singleton_append, ← mul_mk, ← mul_mk, ih, hm]
    simp only [of, mul_assoc]

section Occurrences

variable {s t : List (α × Bool)}

private theorem exists_of_append_merzljakovBlock_append_eq (hab : a ≠ b) :
    ∀ {ms : List ℕ} {s : List (α × Bool)},
      s ++ merzljakovBlock a b m ++ t = merzljakovWord a b ms →
      ∃ ms₁ ms₂, ms = ms₁ ++ m :: ms₂ ∧ s ++ [(b, true)] = merzljakovWord a b ms₁ ∧
        (b, true) :: t = merzljakovWord a b ms₂
  | [], s, h => by
    have := congrArg length h
    simp at this
    omega
  | k :: ms, [], h => by
    have hab' : (a, true) ≠ (b, true) := by simpa using hab
    obtain ⟨tl, htl⟩ : ∃ tl, merzljakovWord a b ms = (b, true) :: tl := ⟨_, rfl⟩
    rw [merzljakovWord_cons, merzljakovBlock_eq] at h
    replace h : replicate m (a, true) ++ (b, true) :: t =
        replicate k (a, true) ++ merzljakovWord a b ms := by simpa using h
    have h₁ := (replicate_prefix_of_append_cons_eq hab' h).length_le
    have h₂ := (replicate_prefix_of_append_cons_eq hab' (htl ▸ h.symm)).length_le
    obtain rfl : m = k := by simp at h₁ h₂; omega
    exact ⟨[], ms, rfl, by simp, append_cancel_left h⟩
  | k :: ms, c :: s, h => by
    have hab' : (a, true) ≠ (b, true) := by simpa using hab
    rw [merzljakovWord_cons, merzljakovBlock_eq] at h
    obtain ⟨rfl, h'⟩ : c = (b, true) ∧
        s ++ (b, true) :: (replicate m (a, true) ++ (b, true) :: t) =
          replicate k (a, true) ++ merzljakovWord a b ms := by simpa using h
    obtain ⟨s', rfl⟩ := replicate_prefix_of_append_cons_eq hab' h'
    rw [append_assoc, append_cancel_left_eq] at h'
    obtain ⟨ms₁, ms₂, rfl, h₁, h₂⟩ := exists_of_append_merzljakovBlock_append_eq hab
      (ms := ms) (s := s') (by simpa [merzljakovBlock_eq] using h')
    exact ⟨k :: ms₁, ms₂, rfl, by simp [merzljakovWord_cons, ← h₁], h₂⟩

/-- The occurrences of the block `b a^m b` in a Merzljakov word over distinct letters `a ≠ b` are
exactly the splittings of its exponent list at an entry `m`: the part of the word before the
occurrence, followed by `b`, is the Merzljakov word of the exponents before that entry, and `b`
followed by the part after the occurrence is the Merzljakov word of the exponents after it. -/
theorem append_merzljakovBlock_append_eq_merzljakovWord_iff (hab : a ≠ b) :
    s ++ merzljakovBlock a b m ++ t = merzljakovWord a b ms ↔
      ∃ ms₁ ms₂, ms = ms₁ ++ m :: ms₂ ∧ s ++ [(b, true)] = merzljakovWord a b ms₁ ∧
        (b, true) :: t = merzljakovWord a b ms₂ := by
  refine ⟨exists_of_append_merzljakovBlock_append_eq hab, ?_⟩
  rintro ⟨ms₁, ms₂, rfl, h₁, h₂⟩
  simp [merzljakovWord_append_cons, ← h₁, ← h₂, merzljakovBlock_eq]

/-- Each block `b a^m b` with `m` among the exponents occurs in the Merzljakov word. -/
theorem merzljakovBlock_isInfix_merzljakovWord (a b : α) (hm : m ∈ ms) :
    merzljakovBlock a b m <:+: merzljakovWord a b ms := by
  induction ms with
  | nil => simp at hm
  | cons k ms ih =>
    obtain ⟨tl, htl⟩ : ∃ tl, merzljakovWord a b ms = (b, true) :: tl := ⟨_, rfl⟩
    rcases mem_cons.1 hm with rfl | hm
    · exact ⟨[], tl, by simp [merzljakovWord_cons, merzljakovBlock_eq, htl]⟩
    · exact (ih hm).trans ⟨(b, true) :: replicate k (a, true), [], by simp [merzljakovWord_cons]⟩

/-- Over distinct letters `a ≠ b`, the block `b a^m b` occurs in a Merzljakov word exactly when
`m` is one of its exponents. -/
@[simp]
theorem merzljakovBlock_isInfix_merzljakovWord_iff (hab : a ≠ b) :
    merzljakovBlock a b m <:+: merzljakovWord a b ms ↔ m ∈ ms := by
  refine ⟨?_, merzljakovBlock_isInfix_merzljakovWord a b⟩
  rintro ⟨s, t, h⟩
  obtain ⟨ms₁, ms₂, rfl, -, -⟩ := (append_merzljakovBlock_append_eq_merzljakovWord_iff hab).1 h
  simp

/-- In a Merzljakov word over distinct letters `a ≠ b` with pairwise distinct exponents, two
occurrences of a block `b a^m b` begin at the same position. -/
theorem eq_of_append_merzljakovBlock_append_eq_merzljakovWord (hab : a ≠ b) (hms : ms.Nodup)
    {s' t' : List (α × Bool)} (h : s ++ merzljakovBlock a b m ++ t = merzljakovWord a b ms)
    (h' : s' ++ merzljakovBlock a b m ++ t' = merzljakovWord a b ms) : s = s' := by
  obtain ⟨ms₁, ms₂, rfl, h₁, -⟩ := (append_merzljakovBlock_append_eq_merzljakovWord_iff hab).1 h
  obtain ⟨ms₁', ms₂', e, h₁', -⟩ := (append_merzljakovBlock_append_eq_merzljakovWord_iff hab).1 h'
  have hm : m ∉ ms₁ ∧ m ∉ ms₂ := by
    simpa [nodup_middle, nodup_cons, not_or] using (nodup_middle.1 hms).notMem
  obtain ⟨rfl, -, -⟩ := (append_cons_inj_of_notMem hm.1 hm.2).1 e
  exact append_cancel_right (h₁.trans h₁'.symm)

/-- In a Merzljakov word over distinct letters `a ≠ b` with pairwise distinct exponents, each
block `b a^m b` with `m` among the exponents occurs exactly once. -/
theorem existsUnique_append_merzljakovBlock_append_eq (hab : a ≠ b) (hms : ms.Nodup)
    (hm : m ∈ ms) :
    ∃! p : List (α × Bool) × List (α × Bool),
      p.1 ++ merzljakovBlock a b m ++ p.2 = merzljakovWord a b ms := by
  obtain ⟨s, t, h⟩ := merzljakovBlock_isInfix_merzljakovWord a b hm
  refine ⟨(s, t), h, ?_⟩
  rintro ⟨s', t'⟩ h'
  obtain rfl := eq_of_append_merzljakovBlock_append_eq_merzljakovWord hab hms h h'
  simpa using (append_cancel_left (h'.trans h.symm))

/-- No block `b a^m b` occurs in the formal inverse of a Merzljakov word. -/
@[simp]
theorem not_merzljakovBlock_isInfix_invRev_merzljakovWord (a b : α) (m : ℕ) (ms : List ℕ) :
    ¬ merzljakovBlock a b m <:+: invRev (merzljakovWord a b ms) := by
  intro h
  have hb : (b, true) ∈ invRev (merzljakovWord a b ms) := h.subset (by simp [merzljakovBlock_eq])
  obtain ⟨x, hx, hxb⟩ : ∃ x ∈ merzljakovWord a b ms, (x.1, !x.2) = (b, true) := by
    simpa [invRev] using hb
  simp [snd_eq_true_of_mem_merzljakovWord hx] at hxb

/-- The formal inverse of a block `b a^m b` does not occur in a Merzljakov word. -/
@[simp]
theorem not_invRev_merzljakovBlock_isInfix_merzljakovWord (a b : α) (m : ℕ) (ms : List ℕ) :
    ¬ invRev (merzljakovBlock a b m) <:+: merzljakovWord a b ms := by
  rw [← invRev_isInfix_invRev, invRev_invRev]
  exact not_merzljakovBlock_isInfix_invRev_merzljakovWord a b m ms

end Occurrences

section Factorisations

private theorem exists_merzljakovBlock_isInfix_of_append_eq_flatten {s : List (α × Bool)} :
    ∀ (L : List (List (α × Bool))) {ms : List ℕ} {p : List (α × Bool)},
      p ++ merzljakovWord a b ms ++ s = L.flatten → L.length ≤ ms.length →
      ∃ m ∈ ms, ∃ u ∈ L, merzljakovBlock a b m <:+: u
  | [], ms, p, h, _ => by
    have := congrArg length h
    simp at this
  | u :: L, [], _, _, hL => by simp at hL
  | u :: L, k :: ms, p, h, hL => by
    obtain ⟨tl, htl⟩ : ∃ tl, merzljakovWord a b ms = (b, true) :: tl := ⟨_, rfl⟩
    have h' : (p ++ (b, true) :: replicate k (a, true)) ++ (merzljakovWord a b ms ++ s) =
        u ++ L.flatten := by simpa [merzljakovWord_cons] using h
    have ih (q : List (α × Bool)) (hq : q ++ merzljakovWord a b ms ++ s = L.flatten) :
        ∃ m ∈ k :: ms, ∃ v ∈ u :: L, merzljakovBlock a b m <:+: v := by
      obtain ⟨m, hm, v, hv, hmv⟩ :=
        exists_merzljakovBlock_isInfix_of_append_eq_flatten L hq (by simpa using hL)
      exact ⟨m, mem_cons_of_mem _ hm, v, mem_cons_of_mem _ hv, hmv⟩
    -- Either the piece `u` ends inside `p b a^k`, or it reaches beyond it. In the first case the
    -- remaining pieces contain the Merzljakov word of the remaining exponents; in the second
    -- case `u` contains the block `b a^k b`.
    obtain ⟨c, hc, hc'⟩ | ⟨c, -, hc'⟩ := append_eq_append_iff.1 h'
    · cases c with
      | nil => exact ih [] (by simpa using hc')
      | cons x c =>
        obtain rfl : (b, true) = x := by simpa [htl] using congrArg head? hc'
        exact ⟨k, mem_cons_self, u, mem_cons_self, p, c, by simp [hc, merzljakovBlock_eq]⟩
    · exact ih c (by simpa using hc'.symm)

/-- If a Merzljakov word with `n` exponents occurs in the concatenation of at most `n` words,
then one of these words contains a whole block `b a^m b` of the Merzljakov word: the `n` blocks
overlap only in single letters, so each of the fewer than `n` cuts between consecutive words
destroys at most one block. -/
theorem exists_merzljakovBlock_isInfix_of_isInfix_flatten {L : List (List (α × Bool))}
    (h : merzljakovWord a b ms <:+: L.flatten) (hL : L.length ≤ ms.length) :
    ∃ m ∈ ms, ∃ u ∈ L, merzljakovBlock a b m <:+: u := by
  obtain ⟨p, s, h⟩ := h
  exact exists_merzljakovBlock_isInfix_of_append_eq_flatten L h hL

end Factorisations

/-- For finitely many given words and every `n` there are `n` strictly increasing exponents such
that no block `b a^m b` of the corresponding Merzljakov word occurs in a given word: it suffices
to take the exponents at least as large as the lengths of the given words. -/
theorem exists_sortedLT_forall_not_merzljakovBlock_isInfix (a b : α) (n : ℕ)
    {S : Set (List (α × Bool))} (hS : S.Finite) :
    ∃ ms : List ℕ, ms.length = n ∧ ms.SortedLT ∧
      ∀ m ∈ ms, ∀ w ∈ S, ¬ merzljakovBlock a b m <:+: w := by
  obtain ⟨N, hN⟩ := (hS.image length).bddAbove
  refine ⟨range' N n, by simp, sortedLT_range' _ _ one_ne_zero, fun m hm w hw h ↦ ?_⟩
  have h₁ := h.length_le
  have h₂ : w.length ≤ N := hN (Set.mem_image_of_mem _ hw)
  have h₃ : N ≤ m := (mem_range'_1.1 hm).1
  rw [length_merzljakovBlock] at h₁
  omega

end FreeGroup

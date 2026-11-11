/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.MerzljakovWord

/-!
# Merzljakov tuples

Merzljakov's theorem concerns a sentence `∀ x₀ ∃ y₀ … ∀ x_{k-1} ∃ y_{k-1} (s = 1)` which holds in
a free group `F(A)`. Its proof substitutes for the universally quantified variables a tuple of
*Merzljakov words* `g i = b a^{m₁} b ⋯ a^{m_n} b`, chosen one after the other together with
witnesses `h i` for the existentially quantified variables, in such a way that no block `b a^m b`
of `g i` occurs in an earlier word `g j` or in an earlier witness `h j`; here `a ≠ b` are two
letters of `A`. A block of `g i` can then be recognised in the equality `s(g, h) = 1`: it comes
from an occurrence of `x i`, and from nothing that was chosen before `g i`.

This file defines the conditions on such a tuple and proves that tuples satisfying them exist.
The witnesses are the values `h = f g` of Skolem functions `f` of the sentence: a function from
tuples to tuples such that `f x i` depends only on the `x j` with `j ≤ i`.

Besides the blocks themselves, their formal inverses are excluded from the earlier witnesses as
well; this is not among the conditions stated in the reference, but its argument uses it, since
a witness is an arbitrary element of the free group and may contain the inverse of a block.

## Main definitions

* `FreeGroup.IsMerzljakovTuple a b ms h`: Merzljakov's conditions on the exponent lists `ms i` of
  the words `g i`, relative to the witnesses `h i`.

## Main results

* `FreeGroup.exists_isMerzljakovTuple`: for all Skolem functions respecting the order of the
  quantifiers there is a tuple of Merzljakov words, each with a prescribed number of blocks,
  which satisfies Merzljakov's conditions relative to the values of the Skolem functions.
* `FreeGroup.IsMerzljakovTuple.not_merzljakovBlock_isInfix_merzljakovWord`: over distinct letters
  `a ≠ b`, no block of a word of a Merzljakov tuple occurs in another word of the tuple.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), 1–203, Section 4.4, proof of Merzljakov's Theorem, conditions 1)–3).
* Yu. I. Merzljakov, *Positive formulae on free groups*, Algebra i Logika 5 (1966), 25–42.
-/

public section

namespace FreeGroup

open List Function

variable {α : Type*} {k : ℕ} {a b : α}

/-- Merzljakov's conditions on a tuple of exponent lists `ms`, relative to elements
`h₀, …, h_{k-1}` of the free group: the exponents of each list are pairwise distinct, lists with
different indices are disjoint, and for `j < i` no block `b a^m b` with `m` in `ms i`, and no
formal inverse of such a block, occurs in the reduced word of `h j`.

When `a ≠ b`, disjointness of the lists `ms i` and `ms j` says that no block of the Merzljakov
word with exponents `ms i` occurs in the one with exponents `ms j`; see
`FreeGroup.IsMerzljakovTuple.not_merzljakovBlock_isInfix_merzljakovWord`. -/
@[mk_iff]
structure IsMerzljakovTuple (a b : α) (ms : Fin k → List ℕ) (h : Fin k → FreeGroup α) : Prop where
  /-- The exponents of each word are pairwise distinct. -/
  nodup (i : Fin k) : (ms i).Nodup
  /-- Words with different indices have no exponent in common. -/
  disjoint {i j : Fin k} (hij : j < i) : (ms i).Disjoint (ms j)
  /-- No block of a word occurs in an earlier witness. -/
  not_isInfix {i j : Fin k} (hij : j < i) {m : ℕ} (hm : m ∈ ms i) {w : List (α × Bool)}
    (hw : IsReduced w) (hwh : mk w = h j) : ¬ merzljakovBlock a b m <:+: w
  /-- No formal inverse of a block of a word occurs in an earlier witness. -/
  not_invRev_isInfix {i j : Fin k} (hij : j < i) {m : ℕ} (hm : m ∈ ms i) {w : List (α × Bool)}
    (hw : IsReduced w) (hwh : mk w = h j) : ¬ invRev (merzljakovBlock a b m) <:+: w

namespace IsMerzljakovTuple

variable {ms : Fin k → List ℕ} {h : Fin k → FreeGroup α}

/-- Two words of a Merzljakov tuple with different indices have no exponent in common. -/
theorem disjoint_of_ne (hms : IsMerzljakovTuple a b ms h) {i j : Fin k} (hij : i ≠ j) :
    (ms i).Disjoint (ms j) :=
  hij.lt_or_gt.elim (fun hlt ↦ (hms.disjoint hlt).symm) hms.disjoint

/-- Over distinct letters `a ≠ b`, no block `b a^m b` of a word of a Merzljakov tuple occurs in
another word of the tuple. -/
theorem not_merzljakovBlock_isInfix_merzljakovWord (hms : IsMerzljakovTuple a b ms h) (hab : a ≠ b)
    {i j : Fin k} (hij : i ≠ j) {m : ℕ} (hm : m ∈ ms i) :
    ¬ merzljakovBlock a b m <:+: merzljakovWord a b (ms j) :=
  fun hmj ↦ hms.disjoint_of_ne hij hm ((merzljakovBlock_isInfix_merzljakovWord_iff hab).1 hmj)

end IsMerzljakovTuple

/-- For given exponent lists `ms j` and elements `h j` of the free group there are `N` pairwise
distinct exponents which occur in no `ms j` and whose blocks and inverse blocks occur in no
reduced word of an `h j`. -/
private theorem exists_nodup_forall_not_isInfix (a b : α) (N : ℕ) (ms : Fin k → List ℕ)
    (h : Fin k → FreeGroup α) :
    ∃ l : List ℕ, l.length = N ∧ l.Nodup ∧ ∀ m ∈ l, ∀ j, m ∉ ms j ∧
      ∀ w, IsReduced w → mk w = h j →
        ¬ merzljakovBlock a b m <:+: w ∧ ¬ invRev (merzljakovBlock a b m) <:+: w := by
  have hfin (j : Fin k) : {w : List (α × Bool) | IsReduced w ∧ mk w = h j}.Finite :=
    Set.Subsingleton.finite fun w hw w' hw' ↦ hw.1.eq_of_mk_eq hw'.1 (hw.2.trans hw'.2.symm)
  obtain ⟨l, hl, hsort, hav⟩ := exists_sortedLT_forall_not_merzljakovBlock_isInfix a b N
    (S := ⋃ j, {merzljakovWord a b (ms j)} ∪ ({w | IsReduced w ∧ mk w = h j} ∪
      invRev '' {w | IsReduced w ∧ mk w = h j}))
    (Set.finite_iUnion fun j ↦ (Set.finite_singleton _).union ((hfin j).union ((hfin j).image _)))
  refine ⟨l, hl, hsort.nodup, fun m hm j ↦ ⟨fun hmj ↦ ?_, fun w hw hwh ↦ ⟨fun hinf ↦ ?_,
    fun hinf ↦ ?_⟩⟩⟩
  · exact hav m hm _ (Set.mem_iUnion.2 ⟨j, .inl rfl⟩)
      (merzljakovBlock_isInfix_merzljakovWord a b hmj)
  · exact hav m hm w (Set.mem_iUnion.2 ⟨j, .inr (.inl ⟨hw, hwh⟩)⟩) hinf
  · exact hav m hm (invRev w) (Set.mem_iUnion.2 ⟨j, .inr (.inr ⟨w, ⟨hw, hwh⟩, rfl⟩)⟩)
      (by rwa [← invRev_isInfix_invRev, invRev_invRev])

/-- The first `n` words of a Merzljakov tuple can be chosen: the conditions relating the word
with index `i` to the earlier words and witnesses hold for all `i < n`. -/
private theorem exists_forall_lt_isMerzljakovTuple (a b : α) (N : ℕ)
    (f : (Fin k → FreeGroup α) → Fin k → FreeGroup α)
    (hf : ∀ i x x', (∀ j ≤ i, x j = x' j) → f x i = f x' i) {n : ℕ} (hn : n ≤ k) :
    ∃ ms : Fin k → List ℕ, (∀ i, (ms i).length = N) ∧ (∀ i, (ms i).Nodup) ∧
      ∀ i j : Fin k, j < i → i < n → ∀ m ∈ ms i, m ∉ ms j ∧
        ∀ w, IsReduced w → mk w = f (fun i ↦ mk (merzljakovWord a b (ms i))) j →
          ¬ merzljakovBlock a b m <:+: w ∧ ¬ invRev (merzljakovBlock a b m) <:+: w := by
  induction n with
  | zero => exact ⟨fun _ ↦ range N, by simp, fun _ ↦ nodup_range, by simp⟩
  | succ n ih =>
    obtain ⟨ms, hlen, hnodup, hms⟩ := ih (Nat.le_of_succ_le hn)
    obtain ⟨l, hl, hl', hav⟩ := exists_nodup_forall_not_isInfix a b N ms
      (f fun i ↦ mk (merzljakovWord a b (ms i)))
    -- Replacing the word with index `n` does not change the witnesses with smaller indices.
    have hf' (j : Fin k) (hj : j < ⟨n, hn⟩) :
        f (fun i ↦ mk (merzljakovWord a b (update ms ⟨n, hn⟩ l i))) j =
          f (fun i ↦ mk (merzljakovWord a b (ms i))) j :=
      hf j _ _ fun j' hj' ↦ by simp [update_of_ne (hj'.trans_lt hj).ne]
    refine ⟨update ms ⟨n, hn⟩ l,
      (forall_update_iff ms fun _ x ↦ x.length = N).2 ⟨hl, fun i _ ↦ hlen i⟩,
      (forall_update_iff ms fun _ x ↦ x.Nodup).2 ⟨hl', fun i _ ↦ hnodup i⟩, fun i j hji hi ↦ ?_⟩
    · have hj : j < ⟨n, hn⟩ := hji.trans_le (Fin.le_def.2 (Nat.le_of_lt_succ hi))
      rw [update_of_ne hj.ne, hf' j hj]
      obtain rfl | hi' := eq_or_ne i ⟨n, hn⟩
      · rw [update_self]
        exact fun m hm ↦ hav m hm j
      · rw [update_of_ne hi']
        exact hms i j hji (lt_of_le_of_ne (Nat.le_of_lt_succ hi) (Fin.val_ne_of_ne hi'))

/-- For Skolem functions `f` respecting the order of the quantifiers and every `N`, there are
exponent lists of length `N` whose Merzljakov words `g i`, together with the witnesses `f g i`,
satisfy Merzljakov's conditions. -/
theorem exists_isMerzljakovTuple (a b : α) (N : ℕ) (f : (Fin k → FreeGroup α) → Fin k → FreeGroup α)
    (hf : ∀ i x x', (∀ j ≤ i, x j = x' j) → f x i = f x' i) :
    ∃ ms : Fin k → List ℕ, (∀ i, (ms i).length = N) ∧
      IsMerzljakovTuple a b ms (f fun i ↦ mk (merzljakovWord a b (ms i))) := by
  obtain ⟨ms, hlen, hnodup, hms⟩ := exists_forall_lt_isMerzljakovTuple a b N f hf le_rfl
  exact ⟨ms, hlen, hnodup, fun {i} _ hij _ hm hmj ↦ (hms i _ hij i.2 _ hm).1 hmj,
    fun {i} _ hij _ hm _ hw hwh ↦ ((hms i _ hij i.2 _ hm).2 _ hw hwh).1,
    fun {i} _ hij _ hm _ hw hwh ↦ ((hms i _ hij i.2 _ hm).2 _ hw hwh).2⟩

/-- For the sentence `∀ x₀ ∃ y₀ … ∀ x_{k-1} ∃ y_{k-1} (y₀ = x₀ ∧ … ∧ y_{k-1} = x_{k-1})` the
witnesses are the Merzljakov words themselves: there are Merzljakov words `g i`, each with `N`
blocks, such that no block of `g i` and no inverse of such a block occurs in `g j` for `j < i`. -/
example (a b : α) (N : ℕ) :
    ∃ ms : Fin k → List ℕ, (∀ i, (ms i).length = N) ∧
      IsMerzljakovTuple a b ms fun i ↦ mk (merzljakovWord a b (ms i)) :=
  exists_isMerzljakovTuple a b N id fun i _ _ h ↦ h i le_rfl

end FreeGroup

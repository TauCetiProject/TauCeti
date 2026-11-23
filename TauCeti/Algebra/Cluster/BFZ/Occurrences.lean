/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.BFZ.Word
public import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin

/-!
# Occurrence coordinates for signed BFZ words

For each simple index, enumerate its positions in increasing order, including its single
negative-prefix position. The sign of a letter does not affect its occurrence number.
Consecutive occurrence numbers give precisely the BFZ successor; the last occurrence has
terminal successor. Thus an occurrence is exchangeable exactly when it lies in the actual
word and is not last. This supplies the per-colour vertex coordinates for assembling the
one-letter factors of a BFZ word.

## References

* A. Berenstein, S. Fomin and A. Zelevinsky, *Cluster algebras III: Upper bounds and double
  Bruhat cells*, Duke Mathematical Journal 126 (2005), §2.2, preceding Definition 2.2.
-/

public section

namespace List

variable {r : ℕ}

/-- Positions of one absolute simple index, counting both signs and the negative prefix. -/
def bfzOccurrencePositions (w : List (Fin r × Bool)) (i : Fin r) :
    Finset (Fin (r + w.length)) :=
  Finset.univ.filter fun k ↦ (bfzLetter w k).1 = i

/-- Occurrence membership depends only on the absolute simple index. -/
@[simp]
theorem mem_bfzOccurrencePositions (w : List (Fin r × Bool)) (i : Fin r)
    (k : Fin (r + w.length)) :
    k ∈ bfzOccurrencePositions w i ↔ (bfzLetter w k).1 = i := by
  simp only [bfzOccurrencePositions, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Every simple index has its negative-prefix occurrence, even in an empty word. -/
theorem bfzOccurrencePositions_nonempty (w : List (Fin r × Bool)) (i : Fin r) :
    (bfzOccurrencePositions w i).Nonempty := by
  refine ⟨i.rev.castAdd w.length, ?_⟩
  simp

/-- The canonical increasing enumeration of positions of a fixed absolute simple index. -/
def bfzOccurrence (w : List (Fin r × Bool)) (i : Fin r) :
    Fin (bfzOccurrencePositions w i).card ↪o Fin (r + w.length) :=
  (bfzOccurrencePositions w i).orderEmbOfFin rfl

/-- Enumerated occurrences have the specified simple index. -/
@[simp]
theorem bfzLetter_bfzOccurrence_fst (w : List (Fin r × Bool)) (i : Fin r)
    (n : Fin (bfzOccurrencePositions w i).card) :
    (bfzLetter w (bfzOccurrence w i n)).1 = i := by
  exact (mem_bfzOccurrencePositions w i _).mp
    (Finset.orderEmbOfFin_mem _ rfl n)

/-- The occurrence enumeration covers exactly the positions of its simple index. -/
@[simp]
theorem range_bfzOccurrence (w : List (Fin r × Bool)) (i : Fin r) :
    Set.range (bfzOccurrence w i) = {k | (bfzLetter w k).1 = i} := by
  rw [bfzOccurrence, Finset.range_orderEmbOfFin]
  ext k
  exact mem_bfzOccurrencePositions w i k

/-- The occurrence number counts exactly the equal-colour positions strictly to its left. -/
theorem card_bfzOccurrencePositions_filter_lt (w : List (Fin r × Bool)) (i : Fin r)
    (n : Fin (bfzOccurrencePositions w i).card) :
    ((bfzOccurrencePositions w i).filter (fun k ↦ k < bfzOccurrence w i n)).card = n := by
  have he : (Finset.Iio n).map (bfzOccurrence w i).toEmbedding =
      (bfzOccurrencePositions w i).filter (fun k ↦ k < bfzOccurrence w i n) := by
    ext k
    simp only [Finset.mem_map, Finset.mem_Iio, Finset.mem_filter,
      mem_bfzOccurrencePositions]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨bfzLetter_bfzOccurrence_fst w i m, (bfzOccurrence w i).strictMono hm⟩
    · rintro ⟨hk, hkn⟩
      obtain ⟨m, rfl⟩ := show k ∈ Set.range (bfzOccurrence w i) by
        rw [range_bfzOccurrence]
        exact hk
      exact ⟨m, (bfzOccurrence w i).lt_iff_lt.mp hkn, rfl⟩
  rw [← he, Finset.card_map, Fin.card_Iio]

/-- An occurrence is specified by its colour and the number of equal-colour positions before it. -/
theorem bfzOccurrence_eq_iff (w : List (Fin r × Bool)) (i : Fin r)
    (n : Fin (bfzOccurrencePositions w i).card) (k : Fin (r + w.length)) :
    bfzOccurrence w i n = k ↔ (bfzLetter w k).1 = i ∧
      ((bfzOccurrencePositions w i).filter (fun j ↦ j < k)).card = n := by
  constructor
  · rintro rfl
    exact ⟨bfzLetter_bfzOccurrence_fst w i n, card_bfzOccurrencePositions_filter_lt w i n⟩
  · rintro ⟨hk, hn⟩
    obtain ⟨m, rfl⟩ := show k ∈ Set.range (bfzOccurrence w i) by
      rw [range_bfzOccurrence]
      exact hk
    have hm : (m : ℕ) = n := (card_bfzOccurrencePositions_filter_lt w i m).symm.trans hn
    exact congrArg (bfzOccurrence w i) (Fin.ext hm).symm

/-- Successive occurrence numbers are successive BFZ positions of that simple index. -/
theorem bfzSuccessor_bfzOccurrence_succ (w : List (Fin r × Bool)) (i : Fin r)
    (n : Fin (bfzOccurrencePositions w i).card)
    (hn : (n : ℕ) + 1 < (bfzOccurrencePositions w i).card) :
    bfzSuccessor w (bfzOccurrence w i n) =
      bfzOccurrence w i ⟨(n : ℕ) + 1, hn⟩ := by
  rw [bfzSuccessor_eq_iff]
  refine ⟨(bfzOccurrence w i).strictMono
    (show n < (⟨(n : ℕ) + 1, hn⟩ : Fin (bfzOccurrencePositions w i).card) from
      Nat.lt_succ_self _), by simp, ?_⟩
  intro k hnk hk
  have hki : (bfzLetter w k).1 = i := hk.trans (bfzLetter_bfzOccurrence_fst w i n)
  obtain ⟨m, rfl⟩ := show k ∈ Set.range (bfzOccurrence w i) by
    rw [range_bfzOccurrence]
    exact hki
  apply (bfzOccurrence w i).monotone
  have hnm : n < m := (bfzOccurrence w i).lt_iff_lt.mp hnk
  change (n : ℕ) + 1 ≤ (m : ℕ)
  exact hnm

/-- An enumerated occurrence is terminal exactly when its occurrence number is last. -/
theorem bfzSuccessor_bfzOccurrence_eq_top_iff (w : List (Fin r × Bool)) (i : Fin r)
    (n : Fin (bfzOccurrencePositions w i).card) :
    bfzSuccessor w (bfzOccurrence w i n) = ⊤ ↔
      (n : ℕ) + 1 = (bfzOccurrencePositions w i).card := by
  constructor
  · intro h
    by_contra hn
    have hlt : (n : ℕ) + 1 < (bfzOccurrencePositions w i).card := by omega
    have hs := bfzSuccessor_bfzOccurrence_succ w i n hlt
    rw [h] at hs
    exact WithTop.top_ne_coe hs
  · intro hn
    rw [bfzSuccessor_eq_top_iff]
    intro k hnk hk
    have hki : (bfzLetter w k).1 = i := hk.trans (bfzLetter_bfzOccurrence_fst w i n)
    obtain ⟨m, rfl⟩ := show k ∈ Set.range (bfzOccurrence w i) by
      rw [range_bfzOccurrence]
      exact hki
    have hnm : n < m := (bfzOccurrence w i).lt_iff_lt.mp hnk
    have _hm := m.isLt
    omega

/-- An occurrence is exchangeable exactly when it is in the actual word and is not last. -/
theorem isBfzExchangeable_bfzOccurrence_iff (w : List (Fin r × Bool)) (i : Fin r)
    (n : Fin (bfzOccurrencePositions w i).card) :
    IsBfzExchangeable w (bfzOccurrence w i n) ↔
      r ≤ (bfzOccurrence w i n : ℕ) ∧
        (n : ℕ) + 1 < (bfzOccurrencePositions w i).card := by
  rw [isBfzExchangeable_iff]
  have hs : (∃ k, bfzOccurrence w i n < k ∧
      (bfzLetter w k).1 = (bfzLetter w (bfzOccurrence w i n)).1) ↔
      bfzSuccessor w (bfzOccurrence w i n) ≠ ⊤ := by
    rw [ne_eq, bfzSuccessor_eq_top_iff]
    simp only [not_forall, not_not, exists_prop]
  rw [hs, ne_eq, bfzSuccessor_bfzOccurrence_eq_top_iff]
  have hn := n.isLt
  omega

end List

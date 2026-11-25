/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.BFZ.Word
public import TauCeti.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Fin

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

/-- The occurrences consist of the word's letters of that colour and its one prefix position. -/
@[simp]
theorem card_bfzOccurrencePositions (w : List (Fin r × Bool)) (i : Fin r) :
    (bfzOccurrencePositions w i).card = (w.map Prod.fst).count i + 1 := by
  have hw : (w.map Prod.fst).count i =
      (Finset.univ.filter fun k : Fin w.length ↦ (w.get k).1 = i).card := by
    simpa only [List.get_eq_getElem, List.ofFn_getElem_eq_map] using
      List.count_ofFn (fun k : Fin w.length ↦ (w.get k).1) i
  have hp : (Finset.univ.filter fun k : Fin r ↦ k.rev = i) = {i.rev} := by
    ext k
    simp [Fin.rev_eq_iff]
  rw [bfzOccurrencePositions, Finset.card_filter, Fin.sum_univ_add]
  simp only [bfzLetter_castAdd, bfzLetter_natAdd, ← Finset.card_filter]
  rw [hp, Finset.card_singleton, ← hw, Nat.add_comm]

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

/-- Every position of a given colour is some enumerated occurrence of that colour. -/
theorem exists_bfzOccurrence_eq_of_bfzLetter_fst_eq (w : List (Fin r × Bool)) (i : Fin r)
    {k : Fin (r + w.length)} (hk : (bfzLetter w k).1 = i) :
    ∃ n, bfzOccurrence w i n = k := by
  have h : k ∈ Set.range (bfzOccurrence w i) := by
    simpa only [range_bfzOccurrence, Set.mem_ofPred_eq] using hk
  exact Set.mem_range.mp h

/-- An occurrence is specified by its colour and the number of equal-colour positions before it. -/
theorem bfzOccurrence_eq_iff (w : List (Fin r × Bool)) (i : Fin r)
    (n : Fin (bfzOccurrencePositions w i).card) (k : Fin (r + w.length)) :
    bfzOccurrence w i n = k ↔ (bfzLetter w k).1 = i ∧
      ((bfzOccurrencePositions w i).filter (fun j ↦ j < k)).card = n := by
  constructor
  · rintro rfl
    exact ⟨bfzLetter_bfzOccurrence_fst w i n,
      Finset.card_filter_lt_orderEmbOfFin (bfzOccurrencePositions w i) rfl n⟩
  · rintro ⟨hk, hn⟩
    obtain ⟨m, rfl⟩ :=
      exists_bfzOccurrence_eq_of_bfzLetter_fst_eq w i hk
    have hCount : ((bfzOccurrencePositions w i).filter (fun j ↦ j < bfzOccurrence w i m)).card =
        (m : ℕ) := Finset.card_filter_lt_orderEmbOfFin (bfzOccurrencePositions w i) rfl m
    have hm : (m : ℕ) = n := hCount.symm.trans hn
    exact congrArg (bfzOccurrence w i) (Fin.ext hm).symm

/-- Occurrence zero is the distinguished negative-prefix position, independently of the
proof of the cardinality bound. -/
@[simp]
theorem bfzOccurrence_zero (w : List (Fin r × Bool)) (i : Fin r)
    (h : 0 < (bfzOccurrencePositions w i).card) :
    bfzOccurrence w i ⟨0, h⟩ = i.rev.castAdd w.length := by
  apply (bfzOccurrence_eq_iff w i ⟨0, h⟩ _).mpr
  refine ⟨by simp, ?_⟩
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k hk hlt
  have hklt : (k : ℕ) < r :=
    (Fin.lt_def.mp hlt).trans (by simpa only [Fin.val_castAdd] using i.rev.isLt)
  exact (ne_of_lt hlt) ((bfzLetter_fst_eq_iff_of_lt w i hklt).mp
    ((mem_bfzOccurrencePositions w i k).mp hk))

/-- Successive occurrence numbers are successive BFZ positions of that simple index. -/
theorem bfzSuccessor_bfzOccurrence_succ (w : List (Fin r × Bool)) (i : Fin r)
    (n : Fin (bfzOccurrencePositions w i).card)
    (hn : (n : ℕ) + 1 < (bfzOccurrencePositions w i).card) :
    bfzSuccessor w (bfzOccurrence w i n) =
      bfzOccurrence w i ⟨(n : ℕ) + 1, hn⟩ := by
  rw [bfzSuccessor_eq_iff]
  refine ⟨(bfzOccurrence w i).strictMono
    (Fin.lt_def.mpr (Nat.lt_succ_self _)), by simp, ?_⟩
  intro k hnk hk
  have hki : (bfzLetter w k).1 = i := hk.trans (bfzLetter_bfzOccurrence_fst w i n)
  obtain ⟨m, rfl⟩ :=
    exists_bfzOccurrence_eq_of_bfzLetter_fst_eq w i hki
  apply (bfzOccurrence w i).monotone
  have hnm : n < m := (bfzOccurrence w i).lt_iff_lt.mp hnk
  simpa only [Fin.le_def, Fin.val_mk] using Nat.succ_le_of_lt (Fin.lt_def.mp hnm)

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
    obtain ⟨m, rfl⟩ :=
      exists_bfzOccurrence_eq_of_bfzLetter_fst_eq w i hki
    have hnm : n < m := (bfzOccurrence w i).lt_iff_lt.mp hnk
    have _hm := m.isLt
    omega

/-- An occurrence is exchangeable exactly when it is in the actual word and is not last. -/
theorem isBfzExchangeable_bfzOccurrence_iff (w : List (Fin r × Bool)) (i : Fin r)
    (n : Fin (bfzOccurrencePositions w i).card) :
    IsBfzExchangeable w (bfzOccurrence w i n) ↔
      r ≤ (bfzOccurrence w i n : ℕ) ∧
        (n : ℕ) + 1 < (bfzOccurrencePositions w i).card := by
  rw [isBfzExchangeable_def, ne_eq, bfzSuccessor_bfzOccurrence_eq_top_iff]
  have hn := n.isLt
  omega

end List

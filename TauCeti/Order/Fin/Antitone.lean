/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Sub.Unbundled.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fin.SuccPred

/-!
# Antitone functions on `Fin`

For every set `S` of adjacent positions `i.castSucc, i.succ` in `Fin (n + 1)` there is a
decreasing integer function on `Fin (n + 1)` whose adjacent values agree exactly at the positions
in `S`: start at `0` and subtract one at each step not in `S`. Such functions label the standard
block-triangular subgroups of `GLₙ₊₁` by the adjacent coordinates lying in a common block.

Also records the telescoping representation of any antitone sequence on `Fin r` into a canonically
ordered subtraction monoid (e.g. `ℕ`) as a sum of upper-tail weights.

## Main results

* `Fin.exists_antitone_castSucc_eq_succ_iff_mem`: a decreasing `w : Fin (n + 1) → ℤ` with
  `w i.castSucc = w i.succ` exactly for `i ∈ S`.
* `Fin.antitone_eq_sum_filter_le`: every antitone function `c : Fin r → M` equals the upper-tail
  sum `∑ k ∈ Finset.univ.filter (i ≤ ·), w k` of adjacent differences.
-/

public section

namespace Fin

/-- For every set `S` of adjacent positions there is a decreasing integer weight on
`Fin (n + 1)` whose adjacent values are equal exactly at `S`: subtract one at each step not in
`S`. -/
theorem exists_antitone_castSucc_eq_succ_iff_mem {n : ℕ} (S : Set (Fin n)) :
    ∃ w : Fin (n + 1) → ℤ, Antitone w ∧ ∀ i : Fin n, w i.castSucc = w i.succ ↔ i ∈ S := by
  classical
  let c (i : Fin (n + 1)) : Finset (Fin n) := Finset.univ.filter fun j ↦ (j : ℕ) < i ∧ j ∉ S
  have hc {i i' : Fin (n + 1)} (h : i ≤ i') : c i ⊆ c i' := fun j hj ↦ by
    simp only [c, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨hj.1.trans_le (Fin.le_iff_val_le_val.mp h), hj.2⟩
  refine ⟨fun i ↦ -((c i).card : ℤ), fun i i' h ↦ by simpa using Finset.card_le_card (hc h),
    fun i ↦ ?_⟩
  simp only [neg_inj, Int.natCast_inj]
  constructor
  · -- If `i ∉ S`, then `i` is counted at `i.succ` but not at `i.castSucc`.
    intro h
    by_contra hi
    have hlt : c i.castSucc ⊂ c i.succ :=
      (Finset.ssubset_iff_of_subset (hc (Fin.castSucc_le_succ i))).mpr ⟨i, by simp [c, hi]⟩
    exact (Finset.card_lt_card hlt).ne h
  · intro hi
    congr 1
    ext j
    simp only [c, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_succ, Fin.val_castSucc]
    refine ⟨fun ⟨_, hjS⟩ ↦ ⟨by omega, hjS⟩, fun ⟨_, hjS⟩ ↦ ⟨?_, hjS⟩⟩
    exact lt_of_le_of_ne (by omega) fun h ↦ hjS (Fin.ext h ▸ hi)

/-- Telescoping an antitone function on `Fin r` into a monoid with ordered subtraction as a sum of
upper-tail weights. -/
theorem antitone_eq_sum_filter_le {M : Type*} [AddCommMonoid M] [PartialOrder M]
    [ExistsAddOfLE M] [AddLeftMono M] [Sub M] [OrderedSub M] {r : ℕ}
    (c : Fin r → M) (hc : Antitone c) :
    ∃ w : Fin r → M, ∀ i : Fin r,
      c i = ∑ k ∈ Finset.univ.filter (fun k : Fin r => i ≤ k), w k := by
  refine ⟨fun k => if h : (k : ℕ) + 1 < r then c k - c ⟨k + 1, h⟩ else c k, fun i => ?_⟩
  suffices ∀ n (i : Fin r), r - 1 - (i : ℕ) = n →
      c i = ∑ k ∈ Finset.univ.filter (fun k : Fin r => i ≤ k),
        if h : (k : ℕ) + 1 < r then c k - c ⟨k + 1, h⟩ else c k from
    this (r - 1 - (i : ℕ)) i rfl
  intro n
  induction n with
  | zero =>
    intro i hi
    have hfilt : Finset.univ.filter (fun k : Fin r => i ≤ k) = {i} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.le_def,
        Fin.ext_iff]
      omega
    have hlast : ¬ (i : ℕ) + 1 < r := by omega
    rw [hfilt, Finset.sum_singleton]
    simp [hlast]
  | succ m ih =>
    intro i hi
    have hlt : (i : ℕ) + 1 < r := by omega
    let i' : Fin r := ⟨i + 1, hlt⟩
    have hfilt : Finset.univ.filter (fun k : Fin r => i ≤ k) =
        insert i (Finset.univ.filter (fun k : Fin r => i' ≤ k)) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.le_def,
        Fin.ext_iff, i']
      omega
    rw [hfilt, Finset.sum_insert (by simp [Fin.le_def, i'])]
    simp only [hlt, ↓reduceDIte]
    rw [← ih i' (by simp only [i']; omega)]
    exact (tsub_add_cancel_of_le (hc (Fin.le_def.mpr (by simp)))).symm

end Fin

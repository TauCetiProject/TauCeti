/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Set.Finite.Basic

/-!
# Columns of the natural-number pairing function

For the Cantor-like pairing `Nat.pair : ℕ → ℕ → ℕ`, the `e`-th **column** `e.pairColumn` is the
infinite set `{n | n.unpair.2 = e} = {Nat.pair x e | x : ℕ}`, corresponding to Soare's `ω^{[e]}`.
Distinct columns are disjoint and their union is `Set.univ`, so priority constructions can assign
each requirement `e` witnesses from `e.pairColumn` without conflict between requirements.

Because `Nat.pair b e` lies in `e.pairColumn` and is at least `b`, the least member of
`e.pairColumn` at or above `b` can be found by a bounded search up to `Nat.pair b e`. This file
defines `Nat.leastInPairColumn e b` by that bounded search and characterizes it as the least
element of `e.pairColumn ∩ Set.Ici b`.

## Main definitions

* `Nat.pairColumn`: the `e`-th pairing column `{n | n.unpair.2 = e}`.
* `Nat.leastInPairColumn`: the least member of `e.pairColumn` at or above a given bound.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapters I.4 and VII.2.
-/

public section

namespace Nat

open Function

/-- `Nat.pair` is strictly increasing in its first argument. -/
theorem strictMono_pair_left (b : ℕ) : StrictMono (pair · b) :=
  fun _ _ => pair_lt_pair_left b

/-- `Nat.pair` is strictly increasing in its second argument. -/
theorem strictMono_pair_right (a : ℕ) : StrictMono (pair a) :=
  fun _ _ => pair_lt_pair_right a

/-- The `e`-th column `{n | n.unpair.2 = e}` of `Nat.pair`, consisting of all `Nat.pair x e`. -/
def pairColumn (e : ℕ) : Set ℕ :=
  {n | n.unpair.2 = e}

/-- Membership in `e.pairColumn` means having second `Nat.unpair` coordinate `e`. -/
@[simp]
theorem mem_pairColumn {e n : ℕ} : n ∈ e.pairColumn ↔ n.unpair.2 = e :=
  Iff.rfl

/-- Membership in `e.pairColumn` is decidable. -/
instance instDecidablePredMemPairColumn (e : ℕ) : DecidablePred (· ∈ e.pairColumn) :=
  fun n => inferInstanceAs (Decidable (n.unpair.2 = e))

/-- `Nat.pair x e` belongs to the `e`-th column. -/
theorem pair_mem_pairColumn (x e : ℕ) : pair x e ∈ e.pairColumn := by
  simp [mem_pairColumn]

/-- The `e`-th column is the range of `x ↦ Nat.pair x e`. -/
theorem pairColumn_eq_range_pair (e : ℕ) : e.pairColumn = Set.range (pair · e) := by
  ext n
  refine ⟨fun h => ⟨n.unpair.1, ?_⟩, ?_⟩
  · simp [← mem_pairColumn.mp h]
  · rintro ⟨x, rfl⟩
    exact pair_mem_pairColumn x e

/-- Every member of `e.pairColumn` is at least `Nat.pair 0 e`. -/
theorem pair_zero_le_of_mem_pairColumn {e n : ℕ} (h : n ∈ e.pairColumn) : pair 0 e ≤ n := by
  obtain rfl := mem_pairColumn.mp h
  exact ((strictMono_pair_left _).monotone (Nat.zero_le _)).trans_eq (pair_unpair n)

/-- Every member of `e.pairColumn` is at least `e`. -/
theorem le_of_mem_pairColumn {e n : ℕ} (h : n ∈ e.pairColumn) : e ≤ n :=
  mem_pairColumn.mp h ▸ unpair_right_le n

/-- Distinct columns are disjoint. -/
theorem disjoint_pairColumn {d e : ℕ} (h : d ≠ e) : Disjoint d.pairColumn e.pairColumn :=
  Set.disjoint_left.mpr fun _ hd he => h (hd.symm.trans he)

/-- The family of pairing columns is pairwise disjoint. -/
theorem pairwise_disjoint_pairColumn : Pairwise (Disjoint on pairColumn) :=
  fun _ _ => disjoint_pairColumn

/-- Every natural number belongs to its own second-coordinate column. -/
@[simp]
theorem iUnion_pairColumn : ⋃ e : ℕ, e.pairColumn = Set.univ :=
  Set.eq_univ_iff_forall.mpr fun n : ℕ => Set.mem_iUnion.mpr ⟨n.unpair.2, rfl⟩

/-- Every pairing column is infinite. -/
theorem infinite_pairColumn (e : ℕ) : e.pairColumn.Infinite := by
  rw [pairColumn_eq_range_pair]
  exact Set.infinite_range_of_injective (strictMono_pair_left e).injective

/-- The least member of `e.pairColumn` that is at least `b`, computed by searching up to
`Nat.pair b e`. -/
def leastInPairColumn (e b : ℕ) : ℕ :=
  ((List.range (pair b e + 1)).find? fun x => decide (b ≤ x ∧ x.unpair.2 = e)).getD (pair b e)

/-- Unfolding `Nat.leastInPairColumn` as a bounded search over `List.range (pair b e + 1)`. -/
theorem leastInPairColumn_def (e b : ℕ) :
    e.leastInPairColumn b =
      ((List.range (pair b e + 1)).find? fun x => decide (b ≤ x ∧ x.unpair.2 = e)).getD
        (pair b e) :=
  (rfl)

private theorem find?_leastInPairColumn_isSome (e b : ℕ) :
    ∃ m, ((List.range (pair b e + 1)).find? fun x => decide (b ≤ x ∧ x.unpair.2 = e)) = some m := by
  refine Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨pair b e, ?_, ?_⟩)
  · exact List.mem_range.mpr (lt_succ_self _)
  · simp [left_le_pair]

private theorem leastInPairColumn_spec (e b : ℕ) :
    b ≤ e.leastInPairColumn b ∧ e.leastInPairColumn b ∈ e.pairColumn ∧
      e.leastInPairColumn b ≤ pair b e ∧
      ∀ n < e.leastInPairColumn b, b ≤ n → n ∉ e.pairColumn := by
  obtain ⟨m, hm⟩ := find?_leastInPairColumn_isSome e b
  have hdef : e.leastInPairColumn b = m := by rw [leastInPairColumn, hm]; rfl
  rw [hdef]
  obtain ⟨hdec, hlt, hmin⟩ := List.find?_range_eq_some.mp hm
  obtain ⟨hbm, hme⟩ := of_decide_eq_true hdec
  refine ⟨hbm, hme, Nat.lt_succ_iff.mp (List.mem_range.mp hlt), fun n hnm hbn hne => ?_⟩
  have := hmin n hnm
  simp [hbn, mem_pairColumn.mp hne] at this

/-- `e.leastInPairColumn b` is at least `b`. -/
theorem le_leastInPairColumn (e b : ℕ) : b ≤ e.leastInPairColumn b :=
  (leastInPairColumn_spec e b).1

/-- `e.leastInPairColumn b` belongs to `e.pairColumn`. -/
theorem leastInPairColumn_mem_pairColumn (e b : ℕ) : e.leastInPairColumn b ∈ e.pairColumn :=
  (leastInPairColumn_spec e b).2.1

/-- The second `Nat.unpair` coordinate of `e.leastInPairColumn b` is `e`. -/
@[simp]
theorem unpair_leastInPairColumn_snd (e b : ℕ) : (e.leastInPairColumn b).unpair.2 = e :=
  leastInPairColumn_mem_pairColumn e b

/-- `e.leastInPairColumn b` is at most `Nat.pair b e`. -/
theorem leastInPairColumn_le_pair (e b : ℕ) : e.leastInPairColumn b ≤ pair b e :=
  (leastInPairColumn_spec e b).2.2.1

/-- `e.leastInPairColumn b` is minimal among members of `e.pairColumn` at or above `b`. -/
theorem leastInPairColumn_le {e b n : ℕ} (hb : b ≤ n) (hn : n ∈ e.pairColumn) :
    e.leastInPairColumn b ≤ n := by
  by_contra hlt
  exact (leastInPairColumn_spec e b).2.2.2 n (Nat.lt_of_not_ge hlt) hb hn

/-- Characterization of `e.leastInPairColumn b` as the least member of `e.pairColumn` at or above
`b`. -/
theorem leastInPairColumn_eq_iff {e b m : ℕ} :
    e.leastInPairColumn b = m ↔
      b ≤ m ∧ m ∈ e.pairColumn ∧ ∀ n < m, b ≤ n → n ∉ e.pairColumn := by
  constructor
  · rintro rfl
    exact ⟨le_leastInPairColumn e b, leastInPairColumn_mem_pairColumn e b,
      (leastInPairColumn_spec e b).2.2.2⟩
  · rintro ⟨hbm, hme, hmin⟩
    refine le_antisymm (leastInPairColumn_le hbm hme) (not_lt.mp fun hlt => ?_)
    exact hmin _ hlt (le_leastInPairColumn e b) (leastInPairColumn_mem_pairColumn e b)

/-- The least member of `e.pairColumn` overall is `Nat.pair 0 e`. -/
@[simp]
theorem leastInPairColumn_zero (e : ℕ) : e.leastInPairColumn 0 = pair 0 e :=
  le_antisymm (leastInPairColumn_le_pair e 0)
    (pair_zero_le_of_mem_pairColumn (leastInPairColumn_mem_pairColumn e 0))

/-- Raising the lower bound raises `e.leastInPairColumn`. -/
theorem monotone_leastInPairColumn (e : ℕ) : Monotone e.leastInPairColumn :=
  fun _ _ hab => leastInPairColumn_le (hab.trans (le_leastInPairColumn e _))
    (leastInPairColumn_mem_pairColumn e _)

/-- Searching from `b + 1` yields a column member strictly above `b`. -/
theorem lt_leastInPairColumn_succ (e b : ℕ) : b < e.leastInPairColumn (b + 1) :=
  Nat.lt_of_succ_le (le_leastInPairColumn e (b + 1))

end Nat

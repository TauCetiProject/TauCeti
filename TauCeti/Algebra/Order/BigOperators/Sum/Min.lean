/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Nat.Find

/-!
# Finite sums of truncations of natural numbers

For a finite family `c` of natural numbers, the truncated sums `∑ l, min k (c l)` count the boxes
in the first `k` columns of the Young diagram with rows `c l`. Their second differences count
the members of the family in a range: for `p < q`, the combination of the truncated sums at
`p + 1`, `q - 1`, `p` and `q` is the number of members strictly between `p` and `q`.

## Main results

* `Finset.sum_min_add_sum_min_eq`: the second-difference identity for truncated sums.
* `Finset.exists_ne_forall_sum_min_lt`: if the column counts of a family `b` are at most those
  of a family `a` with the same sum, and strictly smaller for some `k`, then two distinct
  members `a j ≤ a i` of `a` keep the inequality strict for all `a j ≤ k ≤ a i`. Moving a box
  between these two rows is the key step in generating dominance of partitions by box moves.
-/

public section

namespace Finset

variable {α ι κ : Type*}

/-- For `p < q`, the second differences of the truncated sums `∑ l, min k (c l)` at `p` and `q`
count the members of the family `c` strictly between `p` and `q`. -/
theorem sum_min_add_sum_min_eq (u : Finset α) (c : α → ℕ) {p q : ℕ} (hpq : p < q) :
    ∑ l ∈ u, min (p + 1) (c l) + ∑ l ∈ u, min (q - 1) (c l) =
      ∑ l ∈ u, min p (c l) + ∑ l ∈ u, min q (c l) + #{l ∈ u | p < c l ∧ c l < q} := by
  rw [card_filter, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun l _ => by split_ifs <;> omega

/-- A pair of rows realising a strict inequality of column counts. Let `a` and `b` be finite
families of natural numbers with the same sum, such that for every `k` the column count
`∑ min k (b l)` of `b` is at most the column count `∑ min k (a l)` of `a`, strictly for some `k`.
Then `a` has two distinct members `a j ≤ a i` such that the inequality is strict for every `k`
with `a j ≤ k ≤ a i`. Moving one box from row `j` to row `i` lowers the column count of `a`
by one exactly for `a j ≤ k ≤ a i`, so the result still has column counts at least those
of `b`. -/
theorem exists_ne_forall_sum_min_lt {s : Finset ι} {t : Finset κ} {a : ι → ℕ} {b : κ → ℕ}
    (hsum : ∑ l ∈ t, b l = ∑ l ∈ s, a l)
    (hle : ∀ k, ∑ l ∈ t, min k (b l) ≤ ∑ l ∈ s, min k (a l))
    (hlt : ∃ k, ∑ l ∈ t, min k (b l) < ∑ l ∈ s, min k (a l)) :
    ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ a j ≤ a i ∧
      ∀ k, a j ≤ k → k ≤ a i → ∑ l ∈ t, min k (b l) < ∑ l ∈ s, min k (a l) := by
  classical
  obtain ⟨k₀, hk₀⟩ := hlt
  -- The column counts agree from the largest member of either family on.
  have hbig : ∀ k, s.sup a ⊔ t.sup b ≤ k →
      ∑ l ∈ t, min k (b l) = ∑ l ∈ s, min k (a l) := by
    intro k hk
    rw [sum_congr rfl fun l hl => min_eq_right ((le_sup hl).trans (le_sup_right.trans hk)),
      sum_congr rfl fun l hl => min_eq_right ((le_sup hl).trans (le_sup_left.trans hk)), hsum]
  -- `p < k₀ < q` are the nearest arguments around `k₀` where the column counts agree.
  have hex : ∃ k, k₀ ≤ k ∧ ∑ l ∈ t, min k (b l) = ∑ l ∈ s, min k (a l) :=
    ⟨max k₀ (s.sup a ⊔ t.sup b), le_max_left _ _, hbig _ (le_max_right _ _)⟩
  let p := Nat.findGreatest (fun k => ∑ l ∈ t, min k (b l) = ∑ l ∈ s, min k (a l)) k₀
  let q := Nat.find hex
  have hp : ∑ l ∈ t, min p (b l) = ∑ l ∈ s, min p (a l) :=
    Nat.findGreatest_spec (P := fun k => ∑ l ∈ t, min k (b l) = ∑ l ∈ s, min k (a l))
      (Nat.zero_le k₀) (by simp)
  have hq : ∑ l ∈ t, min q (b l) = ∑ l ∈ s, min q (a l) := (Nat.find_spec hex).2
  have hpk₀ : p < k₀ := lt_of_le_of_ne (Nat.findGreatest_le k₀) fun h => by
    rw [h] at hp
    exact hk₀.ne hp
  have hk₀q : k₀ < q := lt_of_le_of_ne (Nat.find_spec hex).1 fun h => by
    rw [← h] at hq
    exact hk₀.ne hq
  -- Strictly between `p` and `q` the inequality is strict.
  have hrun : ∀ k, p < k → k < q → ∑ l ∈ t, min k (b l) < ∑ l ∈ s, min k (a l) := by
    intro k hpk hkq
    refine (hle k).lt_of_ne fun heq => ?_
    rcases le_total k k₀ with hk | hk
    · exact Nat.findGreatest_is_greatest hpk hk heq
    · exact Nat.find_min hex hkq ⟨hk, heq⟩
  -- Comparing second differences at `p` and `q` gives two members of `a` strictly between them.
  have h₁ := hrun (p + 1) (Nat.lt_succ_self p) (by omega)
  have h₂ := hrun (q - 1) (by omega) (by omega)
  have hs := sum_min_add_sum_min_eq s a (hpk₀.trans hk₀q)
  have ht := sum_min_add_sum_min_eq t b (hpk₀.trans hk₀q)
  have htwo : 1 < #{l ∈ s | p < a l ∧ a l < q} := by omega
  obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp htwo
  rw [mem_filter] at hx hy
  have hint (i j : ι) (hi : p < a i ∧ a i < q) (hj : p < a j ∧ a j < q) :
      ∀ k, a j ≤ k → k ≤ a i → ∑ l ∈ t, min k (b l) < ∑ l ∈ s, min k (a l) :=
    fun k hjk hki => hrun k (by omega) (by omega)
  rcases le_total (a y) (a x) with hyx | hxy'
  · exact ⟨x, hx.1, y, hy.1, hxy, hyx, hint x y hx.2 hy.2⟩
  · exact ⟨y, hy.1, x, hx.1, hxy.symm, hxy', hint y x hy.2 hx.2⟩

end Finset

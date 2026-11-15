/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Data.Nat.Choose.Vandermonde
import TauCeti.Algebra.Order.Antidiag.Pi

/-!
# Vandermonde's identity for finitely many groups

Choosing `n` objects from a disjoint union of groups of sizes `K i`, for `i ∈ s`, amounts to
choosing `k i` objects from each group, for some function `k` whose values sum to `n`.  Counting
both ways gives the multivariate Vandermonde identity

```text
  ∑ k ∈ s.piAntidiag n, ∏ i ∈ s, choose (K i) (k i) = choose (∑ i ∈ s, K i) n.
```

Restricting to the choices with a prescribed number `m` of objects from one group `i` leaves
`choose (K i) m` choices there, times the Vandermonde count for the remaining groups. These
identities normalize the multivariate hypergeometric distribution and compute its coordinate
marginals.  Grouping the categories along a map `f` and prescribing the number of objects drawn
from each group gives a product of Vandermonde counts, one for each group; this is the
aggregation property of the multivariate hypergeometric distribution.

## Main results

* `Finset.sum_piAntidiag_prod_choose`: the multivariate Vandermonde identity, generalizing
  Mathlib's `Nat.add_choose_eq`.
* `Finset.sum_filter_piAntidiag_prod_choose`: the same count with one coordinate prescribed.
* `Finset.sum_filter_piAntidiag_prod_choose_fiberwise`: the same count with the totals over the
  fibres of a map prescribed.
-/

public section

namespace Finset

variable {ι : Type*} [DecidableEq ι]

/-- **Vandermonde's identity** for finitely many groups: the ways of choosing `n` objects from
groups of sizes `K i`, `i ∈ s`, sorted by how many come from each group. -/
theorem sum_piAntidiag_prod_choose (s : Finset ι) (K : ι → ℕ) (n : ℕ) :
    ∑ k ∈ s.piAntidiag n, ∏ i ∈ s, (K i).choose (k i) = (∑ i ∈ s, K i).choose n := by
  induction s using Finset.cons_induction generalizing n with
  | empty => cases n <;> simp
  | cons a s has ih =>
    rw [piAntidiag_cons, sum_disjiUnion, sum_cons, Nat.add_choose_eq]
    refine sum_congr rfl fun p _ ↦ ?_
    rw [sum_map, ← ih, mul_sum]
    refine sum_congr rfl fun g hg ↦ ?_
    have hga := eq_zero_of_notMem_of_mem_piAntidiag has hg
    rw [prod_cons]
    congr 1
    · simp [hga]
    · refine prod_congr rfl fun i hi ↦ ?_
      have hia : i ≠ a := ne_of_mem_of_not_mem hi has
      simp [hia]

/-- The ways of choosing `n` objects from groups of sizes `K j`, `j ∈ s`, with exactly `m`
objects from the group `i ∈ s`: there are `choose (K i) m` choices in that group, times the
Vandermonde count for the other groups. -/
theorem sum_filter_piAntidiag_prod_choose {s : Finset ι} {i : ι} (hi : i ∈ s) (K : ι → ℕ)
    (n m : ℕ) :
    ∑ k ∈ s.piAntidiag n with k i = m, ∏ j ∈ s, (K j).choose (k j) =
      if m ≤ n then (K i).choose m * (∑ j ∈ s.erase i, K j).choose (n - m) else 0 := by
  have hi' : i ∉ s.erase i := notMem_erase i s
  have hs : (s.erase i).cons i hi' = s := by simp [hi]
  conv_lhs => rw [sum_filter, ← hs, piAntidiag_cons, sum_disjiUnion]
  simp only [sum_map, addRightEmbedding_apply, Pi.add_apply, ↓reduceIte]
  -- Only the summand with `i`-coordinate `m` survives; it factors by Vandermonde's identity.
  have hterm : ∀ p ∈ antidiagonal n, ∀ g ∈ (s.erase i).piAntidiag p.2,
      (if g i + p.1 = m then ∏ j ∈ (s.erase i).cons i hi',
          (K j).choose (g j + if j = i then p.1 else 0) else 0) =
        if p.1 = m then (K i).choose m * ∏ j ∈ s.erase i, (K j).choose (g j) else 0 := by
    intro p _ g hg
    have hgi := eq_zero_of_notMem_of_mem_piAntidiag hi' hg
    rw [hgi, zero_add]
    split_ifs with hp
    · rw [prod_cons]
      congr 1
      · simp [hgi, hp]
      · refine prod_congr rfl fun j hj ↦ ?_
        simp [(mem_erase.mp hj).1]
    · rfl
  rw [sum_congr rfl fun p hp ↦ sum_congr rfl (hterm p hp)]
  split_ifs with hmn
  · rw [sum_eq_single (m, n - m)]
    · simp [← mul_sum, sum_piAntidiag_prod_choose]
    · rintro ⟨a, b⟩ hab hne
      have ha : a ≠ m := fun ham ↦ hne (by
        rw [mem_antidiagonal] at hab
        ext <;> simp <;> omega)
      simp [ha]
    · intro h
      exact absurd (by simp [mem_antidiagonal, Nat.add_sub_of_le hmn]) h
  · refine sum_eq_zero fun p hp ↦ ?_
    have ha : p.1 ≠ m := by
      rw [mem_antidiagonal] at hp
      omega
    simp [ha]

/-- **Vandermonde's identity** grouped along a map `f : ι → κ`: the ways of choosing objects from
groups of sizes `K i` so that, for every `j`, exactly `m j` objects come from the groups in the
fibre of `f` over `j`.  Merging the groups of each fibre into one group of size
`∑ i with f i = j, K i` counts these choices as a product of binomial coefficients. -/
theorem sum_filter_piAntidiag_prod_choose_fiberwise {κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (f : ι → κ) (K : ι → ℕ) (m : κ → ℕ) :
    ∑ k ∈ (univ : Finset ι).piAntidiag (∑ j, m j) with ∀ j, ∑ i with f i = j, k i = m j,
        ∏ i, (K i).choose (k i) =
      ∏ j, (∑ i with f i = j, K i).choose (m j) := by
  rw [prod_congr rfl fun j _ ↦ (sum_piAntidiag_prod_choose _ K (m j)).symm, prod_univ_sum]
  -- A count vector is the same as a family of count vectors, one on each fibre of `f`.
  refine sum_nbij' (fun k j i ↦ if f i = j then k i else 0) (fun F i ↦ F (f i) i)
    ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [mem_filter, mem_piAntidiag, mem_univ, implies_true, and_true] at hk
    simp only [Fintype.mem_piFinset, mem_piAntidiag, mem_filter, mem_univ, true_and]
    refine fun j ↦ ⟨?_, fun i hi ↦ by_contra fun h ↦ hi (by simp [h])⟩
    rw [← hk.2 j]
    exact sum_congr rfl fun i hi ↦ by simp [(mem_filter.mp hi).2]
  · intro F hF
    simp only [Fintype.mem_piFinset, mem_piAntidiag, mem_filter, mem_univ, true_and] at hF
    have hfib : ∀ j, ∑ i with f i = j, F (f i) i = m j := fun j ↦ by
      rw [← (hF j).1]
      exact sum_congr rfl fun i hi ↦ by rw [(mem_filter.mp hi).2]
    simp only [mem_filter, mem_piAntidiag, mem_univ, implies_true, and_true]
    exact ⟨by rw [← sum_fiberwise univ f]; exact sum_congr rfl fun j _ ↦ hfib j, hfib⟩
  · intro k _
    simp
  · intro F hF
    simp only [Fintype.mem_piFinset, mem_piAntidiag, mem_filter, mem_univ, true_and] at hF
    funext j i
    split_ifs with h
    · simp [h]
    · exact (not_imp_comm.mp ((hF j).2 i) h).symm
  · intro k _
    rw [← prod_fiberwise univ f]
    exact prod_congr rfl fun j _ ↦ prod_congr rfl fun i hi ↦ by simp [(mem_filter.mp hi).2]

end Finset

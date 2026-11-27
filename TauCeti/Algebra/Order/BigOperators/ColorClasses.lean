/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Weights of sets colored by classes of related elements

Let `w` be a weight on a type `α`, `r` a relation on `α`, and `c : α → κ` a coloring that takes
at most `N` values and whose color classes consist of pairwise `r`-related elements. If every
finite set of pairwise related elements has weight at most `t`, then every finite set has weight
at most `N • t`: split it into its color classes. In a complete canonically ordered monoid
such as `ℝ≥0∞` the same bound holds for the sum over all of `α`.

The coloring used in practice sends `a` to the residue classes modulo a subgroup `H` of finite
index of the `#ι` coordinates of a vector `v a : ι → G`; it has at most `H.index ^ #ι` colors.

No sign condition on `w` is needed for finite sums: the hypothesis on the empty set gives
`0 ≤ t`.

## Main results

* `Finset.sum_le_nsmul_of_encard_range_le`: if `c` takes at most `N` values, its color classes
  are pairwise related, and every finite pairwise related set has weight at most `t`, then
  `∑ a ∈ s, w a ≤ N • t` for every finset `s`.
* `TauCeti.tsum_le_nsmul_of_encard_range_le`: the same bound for `∑' a, w a` in a complete
  canonically ordered additive monoid.
* `Subgroup.sum_le_index_pow_nsmul`, `Subgroup.tsum_le_index_pow_nsmul`: the bounds
  `H.index ^ Nat.card ι • t` when elements whose vectors agree modulo `H` in every coordinate are
  related; `AddSubgroup.sum_le_index_pow_nsmul`, `AddSubgroup.tsum_le_index_pow_nsmul` are the
  same bounds for an additive subgroup, such as a sublattice of a lattice of vectors.

## References

* The folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207, `New.Filling.tsum_le_of_encard_range_le` and
  `New.Filling.tsum_le_relIndex_pow_mul`: the statements formalized here.
-/

public section

open Finset

variable {α κ M : Type*} {r : α → α → Prop} {w : α → M} {t : M}

section Finset

variable [AddCommMonoid M] [Preorder M] [AddLeftMono M]

/-- If a coloring `c` takes at most `N` values, any two distinct elements of the same color are
related by `r`, and every finite set of pairwise `r`-related elements has weight at most `t`,
then every finite set `s` has weight at most `N • t`. -/
theorem Finset.sum_le_nsmul_of_encard_range_le (s : Finset α) {c : α → κ} {N : ℕ}
    (hN : (Set.range c).encard ≤ N) (hc : ∀ ⦃a b⦄, c a = c b → a ≠ b → r a b)
    (ht : ∀ s : Finset α, (s : Set α).Pairwise r → ∑ a ∈ s, w a ≤ t) :
    ∑ a ∈ s, w a ≤ N • t := by
  classical
  have ht₀ : 0 ≤ t := by simpa using ht ∅ (by simp)
  have hcard : #(s.image c) ≤ N := by
    have h : ((s.image c : Finset κ) : Set κ).encard ≤ N :=
      (Set.encard_le_encard (by simp)).trans hN
    rwa [Set.encard_coe_eq_coe_finsetCard, Nat.cast_le] at h
  rw [← sum_fiberwise_of_maps_to fun a ha ↦ mem_image_of_mem c ha]
  refine (sum_le_card_nsmul _ _ t fun k _ ↦ ht _ ?_).trans (nsmul_le_nsmul_left ht₀ hcard)
  intro a ha b hb hab
  simp only [coe_filter, Set.mem_ofPred_eq] at ha hb
  exact hc (ha.2.trans hb.2.symm) hab

/-- If elements `a ≠ b` whose vectors `v a, v b : ι → G` agree modulo a subgroup `H` of finite
index in every coordinate are related by `r`, and every finite set of pairwise `r`-related
elements has weight at most `t`, then every finite set has weight at most
`H.index ^ Nat.card ι • t`. -/
@[to_additive AddSubgroup.sum_le_index_pow_nsmul /-- If elements `a ≠ b` whose vectors
`v a, v b : ι → G` agree modulo an additive subgroup `H` of finite index in every coordinate are
related by `r`, and every finite set of pairwise `r`-related elements has weight at most `t`, then
every finite set has weight at most `H.index ^ Nat.card ι • t`. -/]
theorem Subgroup.sum_le_index_pow_nsmul {ι G : Type*} [Finite ι] [Group G] (H : Subgroup G)
    [H.FiniteIndex] {v : α → ι → G} (hv : ∀ ⦃a b⦄, (∀ i, (v a i : G ⧸ H) = v b i) → a ≠ b → r a b)
    (ht : ∀ s : Finset α, (s : Set α).Pairwise r → ∑ a ∈ s, w a ≤ t) (s : Finset α) :
    ∑ a ∈ s, w a ≤ (H.index ^ Nat.card ι) • t := by
  refine s.sum_le_nsmul_of_encard_range_le (c := fun a i ↦ (v a i : G ⧸ H)) ?_
    (fun a b hab ↦ hv (congrFun hab)) ht
  refine Set.encard_le_card.trans_eq ?_
  rw [ENat.card_eq_coe_natCard, Nat.card_fun, Subgroup.index_eq_card]

end Finset

section CompleteLattice

variable [AddCommMonoid M] [CompleteLattice M] [CanonicallyOrderedAdd M] [TopologicalSpace M]
  [SupConvergenceClass M] [T2Space M]

/-- If a coloring `c` takes at most `N` values, any two distinct elements of the same color are
related by `r`, and every finite set of pairwise `r`-related elements has weight at most `t`,
then the sum of the weights over all of `α` is at most `N • t`. -/
theorem TauCeti.tsum_le_nsmul_of_encard_range_le {c : α → κ} {N : ℕ}
    (hN : (Set.range c).encard ≤ N) (hc : ∀ ⦃a b⦄, c a = c b → a ≠ b → r a b)
    (ht : ∀ s : Finset α, (s : Set α).Pairwise r → ∑ a ∈ s, w a ≤ t) :
    ∑' a, w a ≤ N • t := by
  rw [tsum_eq_iSup_sum]
  exact iSup_le fun s ↦ s.sum_le_nsmul_of_encard_range_le hN hc ht

/-- If elements `a ≠ b` whose vectors `v a, v b : ι → G` agree modulo a subgroup `H` of finite
index in every coordinate are related by `r`, and every finite set of pairwise `r`-related
elements has weight at most `t`, then the sum of the weights over all of `α` is at most
`H.index ^ Nat.card ι • t`. -/
@[to_additive AddSubgroup.tsum_le_index_pow_nsmul /-- If elements `a ≠ b` whose vectors
`v a, v b : ι → G` agree modulo an additive subgroup `H` of finite index in every coordinate are
related by `r`, and every finite set of pairwise `r`-related elements has weight at most `t`, then
the sum of the weights over all of `α` is at most `H.index ^ Nat.card ι • t`. -/]
theorem Subgroup.tsum_le_index_pow_nsmul {ι G : Type*} [Finite ι] [Group G] (H : Subgroup G)
    [H.FiniteIndex] {v : α → ι → G} (hv : ∀ ⦃a b⦄, (∀ i, (v a i : G ⧸ H) = v b i) → a ≠ b → r a b)
    (ht : ∀ s : Finset α, (s : Set α).Pairwise r → ∑ a ∈ s, w a ≤ t) :
    ∑' a, w a ≤ (H.index ^ Nat.card ι) • t := by
  rw [tsum_eq_iSup_sum]
  exact iSup_le (H.sum_le_index_pow_nsmul hv ht)

end CompleteLattice

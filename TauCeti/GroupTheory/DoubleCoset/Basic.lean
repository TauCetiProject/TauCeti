/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.GroupTheory.DoubleCoset

/-!
# Double cosets: the left-coset decomposition

A double coset `HaK` decomposes as the union of the left cosets `(h * a) • K`, where `h`
ranges over representatives of the quotient of `H` by the stabiliser `H ∩ aKa⁻¹`. The
decomposition indexes the left cosets inside a double coset and underlies the finiteness of
Hecke coset decompositions in `TauCeti.NumberTheory.HeckeRing.Basic`.

This file also records how membership in a double coset `HaK` interacts with left
multiplication by `H` and with the quotient `G ⧸ K`.

## Main results

* `DoubleCoset.doubleCoset_eq_iUnion_leftCosets`: `HaK` is the union of the left cosets
  `(h * a) • K`, `h` running over representatives of `H ⧸ (aKa⁻¹).subgroupOf H`.
* `DoubleCoset.mul_mem_doubleCoset_iff`: membership in `HaK` is invariant under left
  multiplication by `H`.
* `DoubleCoset.mem_doubleCoset_of_quotient_eq`: recognising `HxK` from an equation in `G ⧸ K`.

The left-coset decomposition `DoubleCoset.doubleCoset_eq_iUnion_leftCosets` is vendored from
mathlib4 PR [#41253](https://github.com/leanprover-community/mathlib4/pull/41253)
(Chris Birkbeck).
-/

public section

open scoped Pointwise

variable {G : Type*} [Group G]

namespace DoubleCoset

/-- A double coset `HaK` is the union of the left cosets `(h * a) • K` where `h` ranges over
representatives of the quotient of `H` by the stabiliser `H ∩ aKa⁻¹`, with no repeated cosets;
compare `DoubleCoset.doubleCoset_union_leftCoset`, which is indexed by all of `H`. -/
lemma doubleCoset_eq_iUnion_leftCosets (H K : Subgroup G) (a : G) :
    doubleCoset a H K =
      ⋃ i : H ⧸ (ConjAct.toConjAct a • K).subgroupOf H, ((i.out : G) * a) • (K : Set G) := by
  rw [← doubleCoset_union_leftCoset]
  refine le_antisymm (Set.iUnion_subset fun h ↦ ?_)
    (Set.iUnion_subset fun i ↦ Set.subset_iUnion_of_subset i.out le_rfl)
  obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul ((ConjAct.toConjAct a • K).subgroupOf H) h
  refine Set.subset_iUnion_of_subset (QuotientGroup.mk h) (le_of_eq ?_)
  rw [hn, leftCoset_eq_iff]
  simpa [mul_assoc, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def] using
    Subgroup.mem_subgroupOf.mp n.2

/-- **Membership in a double coset is invariant under left multiplication by the left
subgroup.** -/
-- Not `@[simp]`: the `simpNF` linter rejects it, because the left-hand side
-- `b * z ∈ doubleCoset a H K` is itself simplified by `simp` to a `MulAction.orbit`
-- membership, so the rewrite could never fire.
lemma mul_mem_doubleCoset_iff {H : Subgroup G} {K : Set G} {b : G} (hb : b ∈ H) {a z : G} :
    b * z ∈ doubleCoset a (H : Set G) K ↔ z ∈ doubleCoset a (H : Set G) K := by
  have key {c z : G} (hc : c ∈ H) (hz : z ∈ doubleCoset a (H : Set G) K) :
      c * z ∈ doubleCoset a (H : Set G) K := by
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_doubleCoset.mp hz
    exact mem_doubleCoset.mpr ⟨c * x, H.mul_mem hc hx, y, hy, by simp only [mul_assoc]⟩
  exact ⟨fun h ↦ by simpa using key (H.inv_mem hb) h, key hb⟩

/-- **Translating an inverse along a left coset.** If `w` and `x` lie in the same left coset of
`H`, then `x⁻¹ d` belongs to the double coset `H g K` if and only if `w⁻¹ d` does. -/
lemma inv_mul_mem_doubleCoset_iff_of_mem {H : Subgroup G} {K : Set G} {w x d g : G}
    (h : x⁻¹ * w ∈ H) :
    x⁻¹ * d ∈ doubleCoset g (H : Set G) K ↔ w⁻¹ * d ∈ doubleCoset g (H : Set G) K := by
  simpa [mul_assoc] using (mul_mem_doubleCoset_iff (K := K) (a := g) (H.inv_mem h)
    (z := x⁻¹ * d)).symm

/-- **Recognising a double coset from a quotient equation.** If `w` agrees with `l x` modulo `K`
for some `l ∈ H`, then `w` lies in the double coset `H x K`. -/
lemma mem_doubleCoset_of_quotient_eq {H : Set G} {K : Subgroup G} {w x l : G} (hl : l ∈ H)
    (h : (w : G ⧸ K) = ((l * x : G) : G ⧸ K)) : w ∈ doubleCoset x H K :=
  mem_doubleCoset.mpr ⟨l, hl, (l * x)⁻¹ * w, QuotientGroup.eq.mp h.symm,
    (mul_inv_cancel_left _ _).symm⟩

end DoubleCoset

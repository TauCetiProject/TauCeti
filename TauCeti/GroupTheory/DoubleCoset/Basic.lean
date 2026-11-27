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

This file also records how membership in a double coset `HaK` interacts with multiplication by
`H` and `K` and with the quotient `G ⧸ K`.

## Main results

* `DoubleCoset.doubleCoset_eq_iUnion_leftCosets`: `HaK` is the union of the left cosets
  `(h * a) • K`, `h` running over representatives of `H ⧸ (aKa⁻¹).subgroupOf H`.
* `DoubleCoset.mul_mem_doubleCoset_iff`, `DoubleCoset.mul_mem_doubleCoset_iff_right`: membership
  in `HaK` is invariant under left multiplication by `H` and right multiplication by `K`.
* `DoubleCoset.mul_mul_mem_doubleCoset`: membership in `HaK` is closed under left multiplication
  by `H` and right multiplication by `K`, for arbitrary subsemigroups `H` and `K`.
* `DoubleCoset.mul_mem_doubleCoset_of_mem_right`: membership in `HaK` is closed under right
  multiplication by `K`, for an arbitrary set `H` and subsemigroup `K`.
* `DoubleCoset.mem_doubleCoset_of_quotient_eq`: recognising `HxK` from an equation in `G ⧸ K`.
* `Subgroup.mem_conjAct_smul_subgroupOf_iff`: `c ∈ H` lies in the stabiliser
  `(aKa⁻¹).subgroupOf H` exactly when `a⁻¹ c a ∈ K`.
* `DoubleCoset.doubleCoset_mul_subset_mul_doubleCoset`: the double coset `H (r w) K` of a product
  lies in the product `(H r L) (L w K)` of double cosets, for arbitrary sets `H`, `K` and any set
  `L` containing `1`, in any monoid.

The left-coset decomposition `DoubleCoset.doubleCoset_eq_iUnion_leftCosets` is vendored from
mathlib4 PR [#41253](https://github.com/leanprover-community/mathlib4/pull/41253)
(Chris Birkbeck).
-/

public section

open scoped Pointwise

variable {G : Type*} [Group G]

namespace Subgroup

/-- `H ∩ aKa⁻¹`, as a subgroup of `H`, consists of the `c ∈ H` with `a⁻¹ c a ∈ K`. -/
theorem mem_conjAct_smul_subgroupOf_iff {H K : Subgroup G} {a : G} {c : H} :
    c ∈ (ConjAct.toConjAct a • K).subgroupOf H ↔ a⁻¹ * c * a ∈ K := by
  simp [mem_subgroupOf, mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def]

end Subgroup

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
    Subgroup.mem_subgroupOf.mp n.property

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

/-- **Membership in a double coset is invariant under right multiplication by the right
subgroup.** -/
lemma mul_mem_doubleCoset_iff_right {H : Set G} {K : Subgroup G} {b : G} (hb : b ∈ K) {a z : G} :
    z * b ∈ doubleCoset a H (K : Set G) ↔ z ∈ doubleCoset a H (K : Set G) := by
  have key {c z : G} (hc : c ∈ K) (hz : z ∈ doubleCoset a H (K : Set G)) :
      z * c ∈ doubleCoset a H (K : Set G) := by
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_doubleCoset.mp hz
    exact mem_doubleCoset.mpr ⟨x, hx, y * c, K.mul_mem hy hc, by simp only [mul_assoc]⟩
  exact ⟨fun h ↦ by simpa using key (K.inv_mem hb) h, key hb⟩

/-- **Membership in a double coset is closed under two-sided multiplication** by the bounding
subsemigroups. -/
theorem mul_mul_mem_doubleCoset {M S₁ S₂ : Type*} [Semigroup M] [SetLike S₁ M]
    [MulMemClass S₁ M] [SetLike S₂ M] [MulMemClass S₂ M] {H : S₁} {K : S₂} {g z b₁ b₂ : M}
    (hb₁ : b₁ ∈ H) (hz : z ∈ doubleCoset g (H : Set M) (K : Set M)) (hb₂ : b₂ ∈ K) :
    b₁ * z * b₂ ∈ doubleCoset g (H : Set M) (K : Set M) := by
  obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := mem_doubleCoset.mp hz
  exact mem_doubleCoset.mpr
    ⟨b₁ * d₁, mul_mem hb₁ hd₁, d₂ * b₂, mul_mem hd₂ hb₂, by simp only [mul_assoc]⟩

/-- **Membership in a double coset is closed under right multiplication** by the right
subsemigroup: if `z ∈ HaK` and `b ∈ K`, then `z * b ∈ HaK`. -/
theorem mul_mem_doubleCoset_of_mem_right {M S : Type*} [Semigroup M] [SetLike S M]
    [MulMemClass S M] {H : Set M} {K : S} {a z b : M} (hz : z ∈ doubleCoset a H (K : Set M))
    (hb : b ∈ K) : z * b ∈ doubleCoset a H (K : Set M) := by
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_doubleCoset.mp hz
  exact mem_doubleCoset.mpr ⟨x, hx, y * b, mul_mem hy hb, by simp only [mul_assoc]⟩

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

/-- The double coset of a product occurs in the product of the corresponding double cosets, along
any set `C` containing `1`. -/
theorem doubleCoset_mul_subset_mul_doubleCoset {M : Type*} [Monoid M] (B C D : Set M) (hC : 1 ∈ C)
    (r w : M) :
    doubleCoset (r * w) B D ⊆ doubleCoset r B C * doubleCoset w C D := by
  rintro x hx
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_doubleCoset.mp hx
  refine ⟨b₁ * r, ?_, w * b₂, ?_, ?_⟩
  · exact mem_doubleCoset.mpr ⟨b₁, hb₁, 1, hC, by simp⟩
  · exact mem_doubleCoset.mpr ⟨1, hC, b₂, hb₂, by simp⟩
  · simp only [mul_assoc]

end DoubleCoset

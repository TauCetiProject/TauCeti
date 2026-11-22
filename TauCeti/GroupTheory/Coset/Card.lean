/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Index

/-!
# Counting the left cosets that a union of cosets meets

Let `W` be a subgroup of a group `G` and `K ⊆ G` a union of left cosets of `W`, that is
`k * w ∈ K` for `k ∈ K` and `w ∈ W`. The left cosets of `W` meeting `K` are those contained in
`K`, so `K` is recovered from its image in `G ⧸ W`. This file counts that image along a refinement
`W' ≤ W`: each coset of `W` is the union of `[W : W']` cosets of `W'`. In particular a subgroup
`U ≥ W` meets exactly `[U : W]` left cosets of `W`. These counts compute volumes of compact open
sets in a locally profinite group, which are finite unions of cosets of a compact open subgroup.

## Main results

* `Subgroup.mk_mem_image_iff_of_forall_mul_mem`: for a union `K` of left cosets of `W`, the coset
  of `g` lies in the image of `K` exactly when `g ∈ K`.
* `Subgroup.ncard_image_mk_of_le`: for `W' ≤ W`, a union of left cosets of `W` meets `[W : W']`
  times as many left cosets of `W'` as of `W`.
* `Subgroup.ncard_image_mk_eq_relIndex`: a subgroup `U ≥ W` meets `[U : W]` left cosets of `W`.
-/

public section

open Set

namespace Subgroup

variable {G : Type*} [Group G] {W : Subgroup G} {K : Set G}

/-- For a union `K` of left cosets of `W`, the coset of `g` meets `K` only when `g ∈ K`. -/
@[to_additive /-- For a union `K` of cosets of `W`, the coset of `g` meets `K` only when
`g ∈ K`. -/]
theorem mk_mem_image_iff_of_forall_mul_mem (hKW : ∀ k ∈ K, ∀ w ∈ W, k * w ∈ K) {g : G} :
    (g : G ⧸ W) ∈ ((↑) : G → G ⧸ W) '' K ↔ g ∈ K := by
  refine ⟨fun ⟨k, hk, hkg⟩ ↦ ?_, fun hg ↦ ⟨g, hg, rfl⟩⟩
  simpa using hKW k hk _ (QuotientGroup.eq.1 hkg)

/-- **Counting cosets along a refinement.** If `K` is a union of left cosets of `W` and `W' ≤ W`,
then `K` meets `[W : W']` times as many left cosets of `W'` as of `W`. -/
@[to_additive /-- If `K` is a union of cosets of `W` and `W' ≤ W`, then `K` meets `[W : W']`
times as many cosets of `W'` as of `W`. -/]
theorem ncard_image_mk_of_le (hKW : ∀ k ∈ K, ∀ w ∈ W, k * w ∈ K) {W' : Subgroup G}
    (h : W' ≤ W) :
    (((↑) : G → G ⧸ W') '' K).ncard = (((↑) : G → G ⧸ W) '' K).ncard * W'.relIndex W := by
  let e := quotientEquivProdOfLE h
  -- The first coordinate of the tower equivalence is the projection `G ⧸ W' → G ⧸ W`.
  have he (g : G) : (e (g : G ⧸ W')).1 = (g : G ⧸ W) := by
    simp [e, quotientEquivProdOfLE_apply]
  have himage : e '' (((↑) : G → G ⧸ W') '' K) = (((↑) : G → G ⧸ W) '' K) ×ˢ univ := by
    ext ⟨q, r⟩
    constructor
    · rintro ⟨_, ⟨k, hk, rfl⟩, hkqr⟩
      exact ⟨⟨k, hk, by rw [← he, hkqr]⟩, trivial⟩
    · rintro ⟨hq, -⟩
      obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e.symm (q, r))
      have hgq : (g : G ⧸ W) = q := by rw [← he, hg, e.apply_symm_apply]
      refine ⟨g, ⟨g, (mk_mem_image_iff_of_forall_mul_mem hKW).1 (hgq ▸ hq), rfl⟩, ?_⟩
      rw [hg, e.apply_symm_apply]
  rw [← ncard_image_of_injective _ e.injective, himage, ncard_prod, ncard_univ,
    ← index_eq_card, relIndex]

/-- A subgroup `U` containing `W` meets exactly `[U : W]` left cosets of `W`. -/
@[to_additive /-- An additive subgroup `U` containing `W` meets exactly `[U : W]` cosets of
`W`. -/]
theorem ncard_image_mk_eq_relIndex {U : Subgroup G} (h : W ≤ U) :
    (((↑) : G → G ⧸ W) '' U).ncard = W.relIndex U := by
  have hU : ∀ k ∈ (U : Set G), ∀ w ∈ U, k * w ∈ (U : Set G) := fun _ hk _ hw ↦ U.mul_mem hk hw
  have hone : ((↑) : G → G ⧸ U) '' U = {((1 : G) : G ⧸ U)} := by
    ext q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [mk_mem_image_iff_of_forall_mul_mem hU, mem_singleton_iff, eq_comm, QuotientGroup.eq,
      inv_one, one_mul, SetLike.mem_coe]
  rw [ncard_image_mk_of_le hU h, hone, ncard_singleton, one_mul]

end Subgroup

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import TauCeti.Topology.Algebra.RestrictedProduct.Away.Decomposition

/-!
# Level open subgroups of a restricted product

For a family of topological groups `G i` with reference subgroups `B i` and a finite set `S` of
indices such that `B i` is open for `i ∉ S`, the level subgroup

`U_S = {x : Πʳ i, [G i, B i] | ∀ i ∉ S, x i ∈ B i}`

is an open subgroup of the restricted product (`TauCeti.levelOpenSubgroup`), obtained as the
preimage of `integralSubgroup` under `restrictAway`. Restricting `awayDecomposition` to `U_S` and
identifying the integral tail via `RestrictedProduct.structureMap` yields the canonical topological
group isomorphism `(∀ i : S, G i) × (∀ j : {i // i ∉ S}, B j.1) ≃ₜ* U_S`
(`TauCeti.levelOpenSubgroupEquiv`). These open subgroups exhaust the restricted product as `S`
ranges over finite subsets of `ι` and provide the product charts on which finite and infinite
product measures are transported to the restricted product.

Every definition and theorem is also provided for additive groups (`TauCeti.levelOpenAddSubgroup`,
`TauCeti.levelOpenAddSubgroupEquiv`, …).

## Main results

* `TauCeti.levelOpenSubgroup`, `TauCeti.levelOpenAddSubgroup`: the open subgroup of elements lying
  in `B i` for all `i ∉ S`.
* `TauCeti.levelOpenSubgroupEquiv`, `TauCeti.levelOpenAddSubgroupEquiv`: the topological group
  isomorphism `(∀ i : S, G i) × (∀ j : {i // i ∉ S}, B j.1) ≃ₜ* levelOpenSubgroup B S hB`.
* `TauCeti.preimage_coe_comp_levelOpenSubgroupEquiv_box`: the preimage of a coordinate box under
  the level isomorphism is a product of a finite box and a tail box.

## References

* N. Bourbaki, *General Topology*.
* A. Weil, *Basic Number Theory*.
-/

public section

namespace TauCeti

open Filter Topology
open scoped RestrictedProduct

universe u v w

variable {ι : Type u} {G : ι → Type v} {H : ι → Type w}
variable [∀ i, Group (G i)] [∀ i, SetLike (H i) (G i)] [∀ i, SubgroupClass (H i) (G i)]
variable [∀ i, TopologicalSpace (G i)]

/-- For a finite set `S` of indices, the open subgroup `{x | ∀ i ∉ S, x i ∈ B i}` of
`Πʳ i, [G i, B i]` consisting of elements integral outside `S`. Only the reference subgroups
outside `S` need be open. -/
@[to_additive /-- For a finite set `S` of indices, the open additive subgroup
`{x | ∀ i ∉ S, x i ∈ B i}` of `Πʳ i, [G i, B i]` consisting of elements integral outside `S`. Only
the reference subgroups outside `S` need be open. -/]
def levelOpenSubgroup (B : ∀ i, H i) (S : Finset ι)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i))) :
    OpenSubgroup (Πʳ i, [G i, B i]) :=
  let U : ∀ i, Subgroup (G i) := fun i ↦ Subgroup.ofClass (B i)
  { toSubgroup :=
      (integralSubgroup fun j : {i // i ∉ (S : Set ι)} ↦ U j.1).comap (restrictAway (S : Set ι) U)
    isOpen' :=
      (isOpen_integralSubgroup (fun j : {i // i ∉ (S : Set ι)} ↦ U j.1)
        fun j ↦ hB j.1 j.2).preimage (continuous_restrictAway (S : Set ι) U) }

/-- Membership in `levelOpenSubgroup B S hB` means integrality at every index outside `S`. -/
@[to_additive (attr := simp) /-- Membership in `levelOpenAddSubgroup B S hB` means integrality at
every index outside `S`. -/]
theorem mem_levelOpenSubgroup (B : ∀ i, H i) (S : Finset ι)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i))) (x : Πʳ i, [G i, B i]) :
    x ∈ levelOpenSubgroup B S hB ↔ ∀ i ∉ S, x i ∈ B i := by
  let U : ∀ i, Subgroup (G i) := fun i ↦ Subgroup.ofClass (B i)
  let x' : RestrictedProductGroup U := x
  change restrictAway (S : Set ι) U x' ∈
      integralSubgroup (fun j : {i // i ∉ (S : Set ι)} ↦ U j.1) ↔ _
  rw [mem_integralSubgroup]
  simp only [restrictAway_apply, Subtype.forall, Finset.mem_coe]
  rfl

/-- The underlying set of `levelOpenSubgroup B S hB` is `{x | ∀ i ∉ S, x i ∈ B i}`. -/
@[to_additive (attr := simp) /-- The underlying set of `levelOpenAddSubgroup B S hB` is
`{x | ∀ i ∉ S, x i ∈ B i}`. -/]
theorem coe_levelOpenSubgroup (B : ∀ i, H i) (S : Finset ι)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i))) :
    (levelOpenSubgroup B S hB : Set (Πʳ i, [G i, B i])) = {x | ∀ i ∉ S, x i ∈ B i} :=
  Set.ext fun x ↦ mem_levelOpenSubgroup B S hB x

/-- Enlarging the finite set `S` enlarges the level open subgroup. -/
@[to_additive /-- Enlarging the finite set `S` enlarges the level open additive subgroup. -/]
theorem levelOpenSubgroup_mono (B : ∀ i, H i) {S T : Finset ι} (hST : S ⊆ T)
    (hBS : ∀ i ∉ S, IsOpen (B i : Set (G i)))
    (hBT : ∀ i ∉ T, IsOpen (B i : Set (G i)) := fun i hi ↦ hBS i fun h ↦ hi (hST h)) :
    levelOpenSubgroup B S hBS ≤ levelOpenSubgroup B T hBT :=
  fun x hx ↦ (mem_levelOpenSubgroup B T hBT x).mpr fun i hi ↦
    (mem_levelOpenSubgroup B S hBS x).mp hx i fun h ↦ hi (hST h)

/-- At `S = ∅`, the level open subgroup consists of the everywhere-integral elements. -/
@[to_additive /-- At `S = ∅`, the level open additive subgroup consists of the everywhere-integral
elements. -/]
theorem coe_levelOpenSubgroup_empty (B : ∀ i, H i)
    (hB : ∀ i ∉ (∅ : Finset ι), IsOpen (B i : Set (G i))) :
    (levelOpenSubgroup B ∅ hB : Set (Πʳ i, [G i, B i])) = {x | ∀ i, x i ∈ B i} := by
  ext x
  simp

/-- The topological group isomorphism identifying the product
`(∀ i : S, G i) × (∀ j : {i // i ∉ S}, B j.1)` with the level open subgroup
`levelOpenSubgroup B S hB`. -/
@[to_additive /-- The topological additive group isomorphism identifying the product
`(∀ i : S, G i) × (∀ j : {i // i ∉ S}, B j.1)` with the level open additive subgroup
`levelOpenAddSubgroup B S hB`. -/]
noncomputable def levelOpenSubgroupEquiv (B : ∀ i, H i) (S : Finset ι)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i))) :
    ((∀ i : S, G i) × (∀ j : {i // i ∉ S}, B j.1)) ≃ₜ* levelOpenSubgroup B S hB :=
  let U : ∀ i, Subgroup (G i) := fun i ↦ Subgroup.ofClass (B i)
  let d := awayDecomposition (S : Set ι) S.finite_toSet U
  let ι_tail : (∀ j : {i // i ∉ S}, B j.1) → RestrictedProductGroupAway (S : Set ι) U :=
    RestrictedProduct.structureMap (fun j : {i // i ∉ (S : Set ι)} ↦ G j.1)
      (fun j ↦ (U j.1 : Set (G j.1))) cofinite
  { toFun p := ⟨d.symm (p.1, ι_tail p.2), (mem_levelOpenSubgroup B S hB _).mpr fun i hi ↦ by
      have h := awayDecomposition_symm_apply_of_notMem (S : Set ι) S.finite_toSet U
        (p.1, ι_tail p.2) i hi
      exact h.symm ▸ (p.2 ⟨i, hi⟩).2⟩
    invFun u := ((d u.1).1, fun j ↦
      ⟨(d u.1).2 j, by
        have h := awayDecomposition_snd (S : Set ι) S.finite_toSet U u.1 j
        exact h.symm ▸ (mem_levelOpenSubgroup B S hB u.1).mp u.2 j.1 j.2⟩)
    left_inv p := by
      ext i
      · exact congrFun (congrArg Prod.fst (d.apply_symm_apply (p.1, ι_tail p.2))) i
      · change ((d (d.symm (p.1, ι_tail p.2))).2 i : G i.1) = (p.2 i : G i.1)
        rw [MulEquiv.apply_symm_apply]
        rfl
    right_inv u := by
      apply Subtype.ext
      apply d.injective
      rw [MulEquiv.apply_symm_apply]
      ext i <;> rfl
    map_mul' p q := by
      apply Subtype.ext
      have htail : ι_tail (p.2 * q.2) = ι_tail p.2 * ι_tail q.2 := by
        ext j
        rfl
      exact (congrArg d.symm (Prod.ext rfl htail)).trans
        (map_mul d.symm (p.1, ι_tail p.2) (q.1, ι_tail q.2))
    continuous_toFun :=
      Continuous.subtype_mk
        ((continuous_awayDecomposition_symm (S : Set ι) S.finite_toSet U hB).comp
          (continuous_fst.prodMk
            (RestrictedProduct.isEmbedding_structureMap.continuous.comp continuous_snd))) _
    continuous_invFun := by
      have hc : Continuous fun u : levelOpenSubgroup B S hB ↦ d u.1 :=
        (continuous_awayDecomposition (S : Set ι) S.finite_toSet U).comp continuous_subtype_val
      refine (continuous_fst.comp hc).prodMk ?_
      refine (RestrictedProduct.isEmbedding_structureMap (𝓕 := cofinite)).continuous_iff.mpr ?_
      exact (continuous_snd.comp hc).congr fun u ↦ by
        ext j
        rfl }

/-- On an index `i ∈ S`, `levelOpenSubgroupEquiv` reads from the first factor. -/
@[to_additive (attr := simp) /-- On an index `i ∈ S`, `levelOpenAddSubgroupEquiv` reads from the
first factor. -/]
theorem levelOpenSubgroupEquiv_apply_of_mem (B : ∀ i, H i) (S : Finset ι)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i)))
    (p : (∀ i : S, G i) × (∀ j : {i // i ∉ S}, B j.1)) {i : ι} (hi : i ∈ S) :
    (levelOpenSubgroupEquiv B S hB p : Πʳ j, [G j, B j]) i = p.1 ⟨i, hi⟩ :=
  awayDecomposition_symm_apply_of_mem (S : Set ι) S.finite_toSet
    (fun j ↦ Subgroup.ofClass (B j)) _ i hi

/-- On an index `i ∉ S`, `levelOpenSubgroupEquiv` reads from the second factor. -/
@[to_additive (attr := simp) /-- On an index `i ∉ S`, `levelOpenAddSubgroupEquiv` reads from the
second factor. -/]
theorem levelOpenSubgroupEquiv_apply_of_notMem (B : ∀ i, H i) (S : Finset ι)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i)))
    (p : (∀ i : S, G i) × (∀ j : {i // i ∉ S}, B j.1)) {i : ι} (hi : i ∉ S) :
    (levelOpenSubgroupEquiv B S hB p : Πʳ j, [G j, B j]) i = (p.2 ⟨i, hi⟩ : G i) :=
  awayDecomposition_symm_apply_of_notMem (S : Set ι) S.finite_toSet
    (fun j ↦ Subgroup.ofClass (B j)) _ i hi

/-- The first coordinate of `(levelOpenSubgroupEquiv B S hB).symm` evaluates on `S`. -/
@[to_additive (attr := simp) /-- The first coordinate of `(levelOpenAddSubgroupEquiv B S hB).symm`
evaluates on `S`. -/]
theorem levelOpenSubgroupEquiv_symm_fst (B : ∀ i, H i) (S : Finset ι)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i))) (u : levelOpenSubgroup B S hB) (i : S) :
    ((levelOpenSubgroupEquiv B S hB).symm u).1 i = (u : Πʳ j, [G j, B j]) i.1 :=
  awayDecomposition_fst (S : Set ι) S.finite_toSet (fun j ↦ Subgroup.ofClass (B j)) u.1 i

/-- The second coordinate of `(levelOpenSubgroupEquiv B S hB).symm` evaluates outside `S`. -/
@[to_additive (attr := simp) /-- The second coordinate of `(levelOpenAddSubgroupEquiv B S hB).symm`
evaluates outside `S`. -/]
theorem levelOpenSubgroupEquiv_symm_snd (B : ∀ i, H i) (S : Finset ι)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i))) (u : levelOpenSubgroup B S hB) (j : {i // i ∉ S}) :
    (((levelOpenSubgroupEquiv B S hB).symm u).2 j : G j.1) = (u : Πʳ k, [G k, B k]) j.1 :=
  awayDecomposition_snd (S : Set ι) S.finite_toSet (fun k ↦ Subgroup.ofClass (B k)) u.1 j

/-- The preimage of a coordinate box `{x | ∀ i, x i ∈ C i}` under the inclusion of a level open
subgroup composed with `levelOpenSubgroupEquiv` is the product of the finite box over `S` and the
tail box outside `S`. -/
@[to_additive /-- The preimage of a coordinate box `{x | ∀ i, x i ∈ C i}` under the inclusion of a
level open additive subgroup composed with `levelOpenAddSubgroupEquiv` is the product of the finite
box over `S` and the tail box outside `S`. -/]
theorem preimage_coe_comp_levelOpenSubgroupEquiv_box (B : ∀ i, H i) (S : Finset ι)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i))) (C : ∀ i, Set (G i)) :
    (((↑) : levelOpenSubgroup B S hB → Πʳ i, [G i, B i]) ∘ levelOpenSubgroupEquiv B S hB) ⁻¹'
      {x | ∀ i, x i ∈ C i} =
      (Set.univ.pi fun i : S ↦ C i.1) ×ˢ
        (Set.univ.pi fun j : {i // i ∉ S} ↦ ((↑) : B j.1 → G j.1) ⁻¹' C j.1) := by
  ext ⟨x, y⟩
  simp only [Set.mem_preimage, Function.comp_apply, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_pi,
    Set.mem_univ, forall_const]
  constructor
  · intro h
    refine ⟨fun i ↦ ?_, fun j ↦ ?_⟩
    · simpa only [levelOpenSubgroupEquiv_apply_of_mem B S hB (x, y) i.2] using h i.1
    · simpa only [levelOpenSubgroupEquiv_apply_of_notMem B S hB (x, y) j.2] using h j.1
  · rintro ⟨hx, hy⟩ i
    by_cases hi : i ∈ S
    · simpa only [levelOpenSubgroupEquiv_apply_of_mem B S hB (x, y) hi] using hx ⟨i, hi⟩
    · simpa only [levelOpenSubgroupEquiv_apply_of_notMem B S hB (x, y) hi] using hy ⟨i, hi⟩

end TauCeti

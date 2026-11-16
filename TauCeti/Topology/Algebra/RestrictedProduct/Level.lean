/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
-- Proof-only: box openness and principal-stage continuity into a restricted product.
import TauCeti.Topology.Algebra.RestrictedProduct.ContinuousRng
import TauCeti.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# Level open subgroups of a restricted product

For a family of topological groups `G i` with reference subgroups `B i` and a finite set `S` of
indices such that `B i` is open for `i ∉ S`, the level subgroup

`U_S = {x : Πʳ i, [G i, B i] | ∀ i ∉ S, x i ∈ B i}`

is an open subgroup of the restricted product (`TauCeti.levelOpenSubgroup`), and is canonically
isomorphic as a topological group to the product `(∀ i : S, G i) × (∀ j : {i // i ∉ S}, B j.1)`
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
    OpenSubgroup (Πʳ i, [G i, B i]) where
  carrier := {x | ∀ i ∉ S, x i ∈ B i}
  mul_mem' hx hy i hi := mul_mem (hx i hi) (hy i hi)
  one_mem' i _ := one_mem (B i)
  inv_mem' hx i hi := inv_mem (hx i hi)
  isOpen' := by
    classical
    let C : ∀ i, Set (G i) := fun i ↦ if i ∈ S then Set.univ else (B i : Set (G i))
    have hC : ∀ i, IsOpen (C i) := fun i ↦ by
      by_cases hi : i ∈ S
      · simp [C, hi]
      · simpa [C, hi] using hB i hi
    have hBC : ∀ᶠ i in cofinite, (B i : Set (G i)) ⊆ C i := by
      filter_upwards [S.finite_toSet.compl_mem_cofinite] with i hi
      have hi' : i ∉ S := hi
      simp [C, hi']
    convert isOpen_restrictedProduct_box hC hBC using 1
    ext x
    simp [C]

/-- Membership in `levelOpenSubgroup B S hB` means integrality at every index outside `S`. -/
@[to_additive (attr := simp) /-- Membership in `levelOpenAddSubgroup B S hB` means integrality at
every index outside `S`. -/]
theorem mem_levelOpenSubgroup (B : ∀ i, H i) (S : Finset ι)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i))) (x : Πʳ i, [G i, B i]) :
    x ∈ levelOpenSubgroup B S hB ↔ ∀ i ∉ S, x i ∈ B i := by
  rfl

/-- The underlying set of `levelOpenSubgroup B S hB` is `{x | ∀ i ∉ S, x i ∈ B i}`. -/
@[to_additive (attr := simp) /-- The underlying set of `levelOpenAddSubgroup B S hB` is
`{x | ∀ i ∉ S, x i ∈ B i}`. -/]
theorem coe_levelOpenSubgroup (B : ∀ i, H i) (S : Finset ι)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i))) :
    (levelOpenSubgroup B S hB : Set (Πʳ i, [G i, B i])) = {x | ∀ i ∉ S, x i ∈ B i} := by
  rfl

/-- Enlarging the finite set `S` enlarges the level open subgroup. -/
@[to_additive /-- Enlarging the finite set `S` enlarges the level open additive subgroup. -/]
theorem levelOpenSubgroup_mono (B : ∀ i, H i) {S T : Finset ι} (hST : S ⊆ T)
    (hBS : ∀ i ∉ S, IsOpen (B i : Set (G i)))
    (hBT : ∀ i ∉ T, IsOpen (B i : Set (G i)) := fun i hi ↦ hBS i fun h ↦ hi (hST h)) :
    levelOpenSubgroup B S hBS ≤ levelOpenSubgroup B T hBT :=
  fun _ hx i hi ↦ hx i fun h ↦ hi (hST h)

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
  letI := Classical.decEq ι
  let toRP (p : (∀ i : S, G i) × (∀ j : {i // i ∉ S}, B j.1)) : Πʳ i, [G i, B i] :=
    RestrictedProduct.mk (fun i ↦ if hi : i ∈ S then p.1 ⟨i, hi⟩ else (p.2 ⟨i, hi⟩ : G i))
      (Filter.eventually_cofinite.mpr <| S.finite_toSet.subset fun i hi ↦ by
        by_contra hiS
        have hiS' : i ∉ S := hiS
        exact hi (by simp only [dite_eq_right hiS']; exact (p.2 ⟨i, hiS'⟩).2))
  { toFun p := ⟨toRP p, fun i hi ↦ by
      simp only [toRP, RestrictedProduct.mk_apply, dite_eq_right hi]
      exact (p.2 ⟨i, hi⟩).2⟩
    invFun u := (fun i ↦ u.1 i.1, fun j ↦ ⟨u.1 j.1, u.2 j.1 j.2⟩)
    left_inv p := by
      ext i
      · simp [toRP, i.2]
      · simp [toRP, i.2]
    right_inv u := by
      ext i
      simp [toRP]
    map_mul' p q := by
      ext i
      by_cases hi : i ∈ S
      · simp [toRP, hi]
      · simp [toRP, hi]
    continuous_toFun := by
      refine Continuous.subtype_mk ?_ _
      have hS : (cofinite : Filter ι) ≤ 𝓟 (S : Set ι)ᶜ :=
        le_principal_iff.mpr S.finite_toSet.compl_mem_cofinite
      rw [continuous_restrictedProduct_iff_of_forall_mem hS fun p i hi ↦ by
        have hi' : i ∉ S := hi
        simp only [toRP, RestrictedProduct.mk_apply, dite_eq_right hi']
        exact (p.2 ⟨i, hi'⟩).2]
      refine continuous_pi fun i ↦ ?_
      by_cases hi : i ∈ S
      · simpa only [toRP, RestrictedProduct.mk_apply, dite_eq_left hi, Function.comp_def] using
          (continuous_apply (⟨i, hi⟩ : S)).comp continuous_fst
      · simpa only [toRP, RestrictedProduct.mk_apply, dite_eq_right hi, Function.comp_def] using
          continuous_subtype_val.comp ((continuous_apply (⟨i, hi⟩ : {j // j ∉ S})).comp
            continuous_snd)
    continuous_invFun :=
      (continuous_pi fun i ↦ (RestrictedProduct.continuous_eval i.1).comp
        continuous_subtype_val).prodMk
        (continuous_pi fun j ↦ ((RestrictedProduct.continuous_eval j.1).comp
          continuous_subtype_val).subtype_mk _) }

/-- On an index `i ∈ S`, `levelOpenSubgroupEquiv` reads from the first factor. -/
@[to_additive (attr := simp) /-- On an index `i ∈ S`, `levelOpenAddSubgroupEquiv` reads from the
first factor. -/]
theorem levelOpenSubgroupEquiv_apply_of_mem (B : ∀ i, H i) (S : Finset ι)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i)))
    (p : (∀ i : S, G i) × (∀ j : {i // i ∉ S}, B j.1)) {i : ι} (hi : i ∈ S) :
    (levelOpenSubgroupEquiv B S hB p : Πʳ j, [G j, B j]) i = p.1 ⟨i, hi⟩ := by
  classical
  simp [levelOpenSubgroupEquiv, hi]

/-- On an index `i ∉ S`, `levelOpenSubgroupEquiv` reads from the second factor. -/
@[to_additive (attr := simp) /-- On an index `i ∉ S`, `levelOpenAddSubgroupEquiv` reads from the
second factor. -/]
theorem levelOpenSubgroupEquiv_apply_of_notMem (B : ∀ i, H i) (S : Finset ι)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i)))
    (p : (∀ i : S, G i) × (∀ j : {i // i ∉ S}, B j.1)) {i : ι} (hi : i ∉ S) :
    (levelOpenSubgroupEquiv B S hB p : Πʳ j, [G j, B j]) i = (p.2 ⟨i, hi⟩ : G i) := by
  classical
  simp [levelOpenSubgroupEquiv, hi]

/-- The first coordinate of `(levelOpenSubgroupEquiv B S hB).symm` evaluates on `S`. -/
@[to_additive (attr := simp) /-- The first coordinate of `(levelOpenAddSubgroupEquiv B S hB).symm`
evaluates on `S`. -/]
theorem levelOpenSubgroupEquiv_symm_fst (B : ∀ i, H i) (S : Finset ι)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i))) (u : levelOpenSubgroup B S hB) (i : S) :
    ((levelOpenSubgroupEquiv B S hB).symm u).1 i = (u : Πʳ j, [G j, B j]) i.1 := by
  rfl

/-- The second coordinate of `(levelOpenSubgroupEquiv B S hB).symm` evaluates outside `S`. -/
@[to_additive (attr := simp) /-- The second coordinate of `(levelOpenAddSubgroupEquiv B S hB).symm`
evaluates outside `S`. -/]
theorem levelOpenSubgroupEquiv_symm_snd (B : ∀ i, H i) (S : Finset ι)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i))) (u : levelOpenSubgroup B S hB) (j : {i // i ∉ S}) :
    (((levelOpenSubgroupEquiv B S hB).symm u).2 j : G j.1) = (u : Πʳ k, [G k, B k]) j.1 := by
  rfl

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

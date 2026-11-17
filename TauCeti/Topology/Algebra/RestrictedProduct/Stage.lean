/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# Principal stage open subgroups of restricted products

For a family of topological groups `G i` with open reference subgroups `B i` (more generally,
any `SetLike` family satisfying `SubgroupClass`), and any subset `T : Set ι` of indices, the
elements of `Πʳ i, [G i, B i]` lying in `B i` for all `i ∉ T` form an open subgroup
`TauCeti.stageSubgroup B hB T`.

When `T : Finset ι` is finite, `TauCeti.stageEquiv B hB T` identifies this open subgroup as a
topological group with the product `(∀ i : T, G i) × (∀ j : {i // i ∉ T}, B j.1)`. Unlike
`TauCeti.awayDecomposition`, which splits the entire restricted product into `S` and a restricted
product away from `S` for `Subgroup`, this stage decomposition cuts out the finite-index open
subgroup directly and works for any `SubgroupClass` family (such as `Subgroup`, `OpenSubgroup`,
or `ValuationSubring` in `FiniteAdeleRing`).

All definitions and results carry `@[to_additive]` counterparts (`addStageSubgroup`,
`addStageEquiv`, …).

## Main definitions

* `TauCeti.stageSubgroup`: the open subgroup `{x : Πʳ i, [G i, B i] | ∀ i ∉ T, x i ∈ B i}`.
* `TauCeti.stageEquiv`: for finite `T : Finset ι`, the topological group isomorphism
  `stageSubgroup B hB (T : Set ι) ≃ₜ* (∀ i : T, G i) × (∀ j : {i // i ∉ T}, B j.1)`.

## Main results

* `TauCeti.mem_stageSubgroup`, `TauCeti.stageSubgroup_mono`, `TauCeti.iUnion_stageSubgroup`:
  membership, monotonicity, and exhaustion of `Πʳ i, [G i, B i]` by the finite stages.
* `TauCeti.stageEquiv_fst`, `TauCeti.stageEquiv_snd`, `TauCeti.stageEquiv_symm_apply_of_mem`,
  `TauCeti.stageEquiv_symm_apply_of_notMem`: coordinate formulas for the isomorphism.
* `TauCeti.stageEquiv_symm_preimage_box`, `TauCeti.stageEquiv_symm_preimage_box_of_eq`,
  `TauCeti.stageEquiv_symm_image_box_of_eq`: identification of a box `{x | ∀ i, x i ∈ C i}` under
  the stage isomorphism.

## References

* N. Bourbaki, *General Topology*.
* A. Weil, *Basic Number Theory*.
-/

public section

noncomputable section

open Filter Set Topology
open scoped RestrictedProduct

namespace TauCeti

variable {ι : Type*} {G S : ι → Type*} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
variable [∀ i, SetLike (S i) (G i)] [∀ i, SubgroupClass (S i) (G i)]

/-- The open subgroup of `Πʳ i, [G i, B i]` consisting of elements whose coordinate at every
index outside `T` lies in the reference subgroup `B i`. -/
@[to_additive addStageSubgroup /-- The open additive subgroup of `Πʳ i, [G i, B i]` consisting of
elements whose coordinate at every index outside `T` lies in the reference subgroup `B i`. -/]
def stageSubgroup (B : ∀ i, S i) (hB : ∀ i, IsOpen (B i : Set (G i))) (T : Set ι) :
    OpenSubgroup (Πʳ i, [G i, B i]) where
  carrier := {x | ∀ i, i ∉ T → x i ∈ B i}
  one_mem' i _ := one_mem (B i)
  mul_mem' hx hy i hi := mul_mem (hx i hi) (hy i hi)
  inv_mem' hx i hi := inv_mem (hx i hi)
  isOpen' := RestrictedProduct.isOpen_forall_imp_mem hB

/-- Membership in `stageSubgroup B hB T` means every coordinate outside `T` lies in `B i`. -/
@[to_additive (attr := simp) mem_addStageSubgroup /-- Membership in `addStageSubgroup B hB T`
means every coordinate outside `T` lies in `B i`. -/]
theorem mem_stageSubgroup {B : ∀ i, S i} {hB : ∀ i, IsOpen (B i : Set (G i))} {T : Set ι}
    {x : Πʳ i, [G i, B i]} :
    x ∈ stageSubgroup B hB T ↔ ∀ i ∉ T, x i ∈ B i :=
  Iff.rfl

/-- The stage subgroups are monotone in `T`. -/
@[to_additive addStageSubgroup_mono /-- The additive stage subgroups are monotone in `T`. -/]
theorem stageSubgroup_mono {B : ∀ i, S i} {hB : ∀ i, IsOpen (B i : Set (G i))}
    {T₁ T₂ : Set ι} (h : T₁ ⊆ T₂) :
    stageSubgroup B hB T₁ ≤ stageSubgroup B hB T₂ :=
  fun _ hx i hi ↦ hx i fun hi₁ ↦ hi (h hi₁)

/-- The stage subgroup for `T = ∅` is the set of elements lying in `B i` at every index. -/
@[to_additive coe_addStageSubgroup_empty /-- The additive stage subgroup for `T = ∅` is the set of
elements lying in `B i` at every index. -/]
theorem coe_stageSubgroup_empty (B : ∀ i, S i) (hB : ∀ i, IsOpen (B i : Set (G i))) :
    (stageSubgroup B hB (∅ : Set ι) : Set (Πʳ i, [G i, B i])) = {x | ∀ i, x i ∈ B i} := by
  ext x
  simp

/-- Every element of a restricted product lies in some finite stage subgroup. -/
@[to_additive exists_mem_addStageSubgroup /-- Every element of a restricted product lies in some
finite additive stage subgroup. -/]
theorem exists_mem_stageSubgroup (B : ∀ i, S i) (hB : ∀ i, IsOpen (B i : Set (G i)))
    (x : Πʳ i, [G i, B i]) :
    ∃ T : Finset ι, x ∈ stageSubgroup B hB (T : Set ι) := by
  classical
  have hfin : {i | x i ∉ B i}.Finite := mem_cofinite.mp x.2
  refine ⟨hfin.toFinset, fun i hi ↦ ?_⟩
  by_contra hxi
  exact hi (Finset.mem_coe.mpr (hfin.mem_toFinset.mpr hxi))

/-- The finite stage subgroups exhaust the restricted product. -/
@[to_additive iUnion_addStageSubgroup /-- The finite additive stage subgroups exhaust the
restricted product. -/]
theorem iUnion_stageSubgroup (B : ∀ i, S i) (hB : ∀ i, IsOpen (B i : Set (G i))) :
    ⋃ T : Finset ι, (stageSubgroup B hB (T : Set ι) : Set (Πʳ i, [G i, B i])) = Set.univ :=
  eq_univ_of_forall fun x ↦ mem_iUnion.mpr (exists_mem_stageSubgroup B hB x)

open Classical in
/-- For a finite set `T : Finset ι`, the topological group isomorphism between the open stage
subgroup `stageSubgroup B hB (T : Set ι)` and `(∀ i : T, G i) × (∀ j : {i // i ∉ T}, B j.1)`. -/
@[to_additive addStageEquiv /-- For a finite set `T : Finset ι`, the topological additive group
isomorphism between the open stage subgroup `addStageSubgroup B hB (T : Set ι)` and
`(∀ i : T, G i) × (∀ j : {i // i ∉ T}, B j.1)`. -/]
def stageEquiv (B : ∀ i, S i) (hB : ∀ i, IsOpen (B i : Set (G i))) (T : Finset ι) :
    stageSubgroup B hB (T : Set ι) ≃ₜ*
      (∀ i : T, G i) × (∀ j : {i // i ∉ (T : Set ι)}, B j.1) :=
  { toFun := fun x ↦ (fun i ↦ x.1 i.1, fun j ↦ ⟨x.1 j.1, x.2 j.1 j.2⟩)
    invFun := fun p ↦
      ⟨⟨fun i ↦ if hi : i ∈ (T : Set ι) then p.1 ⟨i, hi⟩ else (p.2 ⟨i, hi⟩ : G i),
        Filter.eventually_cofinite.mpr (T.finite_toSet.subset fun i hi ↦ by
          by_contra hiT
          exact hi (by simp [hiT]))⟩,
        fun i hi ↦ by simp [Finset.mem_coe.not.mp hi]⟩
    left_inv := fun x ↦ by
      ext i
      simp
    right_inv := fun p ↦ by
      ext i
      · simp [i.2]
      · simp [Finset.mem_coe.not.mp i.2]
    map_mul' := fun x y ↦ by
      ext i <;> rfl
    continuous_toFun := by
      refine Continuous.prodMk ?_ ?_
      · exact continuous_pi fun i ↦
          (RestrictedProduct.continuous_eval i.1).comp continuous_subtype_val
      · exact continuous_pi fun j ↦
          ((RestrictedProduct.continuous_eval j.1).comp continuous_subtype_val).subtype_mk _
    continuous_invFun := by
      have hT : (cofinite : Filter ι) ≤ 𝓟 (T : Set ι)ᶜ :=
        le_principal_iff.mpr T.finite_toSet.compl_mem_cofinite
      let g : (∀ i : T, G i) × (∀ j : {i // i ∉ (T : Set ι)}, B j.1) →
          Πʳ i, [G i, B i]_[𝓟 (T : Set ι)ᶜ] := fun p ↦
        ⟨fun i ↦ if hi : i ∈ (T : Set ι) then p.1 ⟨i, hi⟩ else (p.2 ⟨i, hi⟩ : G i),
          eventually_principal.mpr fun i hi ↦ by simp [Finset.mem_coe.not.mp hi]⟩
      have hg : Continuous g := by
        rw [RestrictedProduct.continuous_rng_of_principal_iff_forall]
        intro i
        by_cases hi : i ∈ (T : Set ι)
        · have hfun : ((fun x : Πʳ i, [G i, B i]_[𝓟 (T : Set ι)ᶜ] ↦ x i) ∘ g) =
              fun p ↦ p.1 ⟨i, hi⟩ := by
            ext p
            exact dite_eq_left hi
          rw [hfun]
          exact (continuous_apply (⟨i, hi⟩ : T)).comp continuous_fst
        · have hfun : ((fun x : Πʳ i, [G i, B i]_[𝓟 (T : Set ι)ᶜ] ↦ x i) ∘ g) =
              fun p ↦ (p.2 ⟨i, hi⟩ : G i) := by
            ext p
            exact dite_eq_right hi
          rw [hfun]
          exact continuous_subtype_val.comp
            ((continuous_apply (⟨i, hi⟩ : {i // i ∉ (T : Set ι)})).comp continuous_snd)
      exact ((RestrictedProduct.continuous_inclusion hT).comp hg).subtype_mk _ }

/-- The first component of `stageEquiv` evaluates coordinates inside `T`. -/
@[to_additive (attr := simp) addStageEquiv_fst /-- The first component of `addStageEquiv` evaluates
coordinates inside `T`. -/]
theorem stageEquiv_fst (B : ∀ i, S i) (hB : ∀ i, IsOpen (B i : Set (G i))) (T : Finset ι)
    (x : stageSubgroup B hB (T : Set ι)) (i : T) :
    (stageEquiv B hB T x).1 i = x.1 i.1 :=
  (rfl)

/-- The second component of `stageEquiv` evaluates coordinates outside `T` inside `B j`. -/
@[to_additive (attr := simp) addStageEquiv_snd /-- The second component of `addStageEquiv` evaluates
coordinates outside `T` inside `B j`. -/]
theorem stageEquiv_snd (B : ∀ i, S i) (hB : ∀ i, IsOpen (B i : Set (G i))) (T : Finset ι)
    (x : stageSubgroup B hB (T : Set ι)) (j : {i // i ∉ (T : Set ι)}) :
    ((stageEquiv B hB T x).2 j : G j.1) = x.1 j.1 :=
  (rfl)

/-- At an index `i ∈ T`, the inverse of `stageEquiv` reads off the first component. -/
@[to_additive (attr := simp) addStageEquiv_symm_apply_of_mem /-- At an index `i ∈ T`, the inverse
of `addStageEquiv` reads off the first component. -/]
theorem stageEquiv_symm_apply_of_mem (B : ∀ i, S i) (hB : ∀ i, IsOpen (B i : Set (G i)))
    (T : Finset ι) (p : (∀ i : T, G i) × (∀ j : {i // i ∉ (T : Set ι)}, B j.1))
    {i : ι} (hi : i ∈ T) :
    ((stageEquiv B hB T).symm p : Πʳ i, [G i, B i]) i = p.1 ⟨i, hi⟩ := by
  have h := stageEquiv_fst B hB T ((stageEquiv B hB T).symm p) ⟨i, hi⟩
  simpa only [ContinuousMulEquiv.apply_symm_apply] using h.symm

/-- At an index `i ∉ T`, the inverse of `stageEquiv` reads off the second component. -/
@[to_additive (attr := simp) addStageEquiv_symm_apply_of_notMem /-- At an index `i ∉ T`, the
inverse of `addStageEquiv` reads off the second component. -/]
theorem stageEquiv_symm_apply_of_notMem (B : ∀ i, S i) (hB : ∀ i, IsOpen (B i : Set (G i)))
    (T : Finset ι) (p : (∀ i : T, G i) × (∀ j : {i // i ∉ (T : Set ι)}, B j.1))
    {i : ι} (hi : i ∉ T) :
    ((stageEquiv B hB T).symm p : Πʳ i, [G i, B i]) i = p.2 ⟨i, hi⟩ := by
  have h := stageEquiv_snd B hB T ((stageEquiv B hB T).symm p) ⟨i, hi⟩
  simpa only [ContinuousMulEquiv.apply_symm_apply] using h.symm

/-- For any family of subsets `C i ⊆ G i`, pulling the ambient box `{x | ∀ i, x i ∈ C i}` back
along `stageEquiv.symm` yields the product of the `T`-box and the `Tᶜ`-box. -/
@[to_additive addStageEquiv_symm_preimage_box /-- For any family of subsets `C i ⊆ G i`, pulling
the ambient box `{x | ∀ i, x i ∈ C i}` back along `addStageEquiv.symm` yields the product of the
`T`-box and the `Tᶜ`-box. -/]
theorem stageEquiv_symm_preimage_box (B : ∀ i, S i) (hB : ∀ i, IsOpen (B i : Set (G i)))
    (T : Finset ι) (C : ∀ i, Set (G i)) :
    (((↑) : stageSubgroup B hB (T : Set ι) → Πʳ i, [G i, B i]) ∘ (stageEquiv B hB T).symm) ⁻¹'
        {x | ∀ i, x i ∈ C i} =
      (Set.univ.pi fun i : T ↦ C i.1) ×ˢ
        (Set.univ.pi fun j : {i // i ∉ (T : Set ι)} ↦ ((↑) : B j.1 → G j.1) ⁻¹' C j.1) := by
  ext p
  simp only [mem_preimage, Function.comp_apply, Set.mem_ofPred_eq, mem_prod, Set.mem_pi, mem_univ,
    forall_const]
  constructor
  · intro h
    refine ⟨fun i ↦ ?_, fun j ↦ ?_⟩
    · simpa only [stageEquiv_symm_apply_of_mem B hB T p i.2] using h i.1
    · simpa only [stageEquiv_symm_apply_of_notMem B hB T p j.2] using h j.1
  · rintro ⟨h₁, h₂⟩ i
    by_cases hi : i ∈ T
    · rw [stageEquiv_symm_apply_of_mem B hB T p hi]
      exact h₁ ⟨i, hi⟩
    · rw [stageEquiv_symm_apply_of_notMem B hB T p hi]
      exact h₂ ⟨i, hi⟩

/-- When `C i = B i` for all `i ∉ T`, the `Tᶜ`-factor in `stageEquiv_symm_preimage_box` is
`Set.univ`. -/
@[to_additive addStageEquiv_symm_preimage_box_of_eq /-- When `C i = B i` for all `i ∉ T`, the
`Tᶜ`-factor in `addStageEquiv_symm_preimage_box` is `Set.univ`. -/]
theorem stageEquiv_symm_preimage_box_of_eq (B : ∀ i, S i) (hB : ∀ i, IsOpen (B i : Set (G i)))
    (T : Finset ι) {C : ∀ i, Set (G i)} (hC : ∀ i ∉ T, C i = B i) :
    (((↑) : stageSubgroup B hB (T : Set ι) → Πʳ i, [G i, B i]) ∘ (stageEquiv B hB T).symm) ⁻¹'
        {x | ∀ i, x i ∈ C i} =
      (Set.univ.pi fun i : T ↦ C i.1) ×ˢ Set.univ := by
  rw [stageEquiv_symm_preimage_box]
  congr 1
  ext p
  simp only [Set.mem_pi, mem_univ, mem_preimage, forall_const, iff_true]
  intro j
  rw [hC j.1 j.2]
  exact (p j).2

/-- When `C i = B i` for all `i ∉ T`, the ambient box `{x | ∀ i, x i ∈ C i}` is the image of
`(Set.univ.pi fun i : T ↦ C i.1) ×ˢ Set.univ` under `Subtype.val ∘ (stageEquiv B hB T).symm`. -/
@[to_additive addStageEquiv_symm_image_box_of_eq /-- When `C i = B i` for all `i ∉ T`, the ambient
box `{x | ∀ i, x i ∈ C i}` is the image of `(Set.univ.pi fun i : T ↦ C i.1) ×ˢ Set.univ` under
`Subtype.val ∘ (addStageEquiv B hB T).symm`. -/]
theorem stageEquiv_symm_image_box_of_eq (B : ∀ i, S i) (hB : ∀ i, IsOpen (B i : Set (G i)))
    (T : Finset ι) {C : ∀ i, Set (G i)} (hC : ∀ i ∉ T, C i = B i) :
    (((↑) : stageSubgroup B hB (T : Set ι) → Πʳ i, [G i, B i]) ∘ (stageEquiv B hB T).symm) ''
        ((Set.univ.pi fun i : T ↦ C i.1) ×ˢ Set.univ) =
      {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ C i} := by
  ext x
  constructor
  · rintro ⟨p, ⟨hp, _⟩, rfl⟩ i
    by_cases hi : i ∈ T
    · dsimp only [Function.comp_apply]
      rw [stageEquiv_symm_apply_of_mem B hB T p hi]
      exact hp ⟨i, hi⟩ trivial
    · dsimp only [Function.comp_apply]
      rw [stageEquiv_symm_apply_of_notMem B hB T p hi, hC i hi]
      exact (p.2 ⟨i, hi⟩).2
  · intro hx
    have hxU : x ∈ stageSubgroup B hB (T : Set ι) :=
      (mem_stageSubgroup (B := B)).mpr fun i hi ↦ by
        rw [← SetLike.mem_coe, ← hC i hi]
        exact hx i
    refine ⟨stageEquiv B hB T ⟨x, hxU⟩, ⟨fun i _ ↦ ?_, trivial⟩, by simp⟩
    simpa only [stageEquiv_fst] using hx i.1

end TauCeti

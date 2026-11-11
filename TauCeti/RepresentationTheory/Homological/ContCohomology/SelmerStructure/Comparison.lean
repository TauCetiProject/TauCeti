/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.SelmerStructure.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
import TauCeti.GroupTheory.Index.Exact

/-!
# Changing the local conditions of a Selmer group

Fix the localisation data of a Selmer structure, and two systems of local conditions
`A i ≤ B i`. If they agree outside a set `S`, localisation gives an exact sequence

`0 → Sel_A → Sel_B → ∏ i ∈ S, B i / A i`.

The last arrow need not be surjective: its image records which local classes arise globally.
The quotient `Sel_B / Sel_A` is identified with this image. For finite `S`, its order therefore
divides the product of the local indices `[B i : A i]`. In particular, finiteness of `Sel_A`
and of these local quotients implies finiteness of `Sel_B`.

This is the elementary exact-sequence part of a comparison of Selmer orders. Identifying the
cokernel with a dual Selmer obstruction requires arithmetic duality, not just localisation.

## Main definitions

* `TauCeti.ContCohomology.SelmerStructure.withLocalConditions`: replace the local conditions
  without changing the localisation data.
* `TauCeti.ContCohomology.SelmerStructure.localConditionComparison`: localisation of `Sel_B`
  modulo the smaller local conditions, at a specified set of indices.

## Main results

* `TauCeti.ContCohomology.SelmerStructure.exact_inclusion_localConditionComparison`: exactness
  of the change-of-local-conditions sequence.
* `TauCeti.ContCohomology.SelmerStructure.relIndex_selmerGroup_eq_card_range`: the relative
  Selmer index is the order of the localisation image.
* `TauCeti.ContCohomology.SelmerStructure.relIndex_selmerGroup_dvd_prod`: divisibility of the
  relative Selmer index by the product of the local indices.

## References

* K. Rubin, *Euler Systems*, Annals of Mathematics Studies 147, Princeton University Press,
  2000, I.1, for Selmer structures and comparison of local conditions.
* J. S. Milne, *Arithmetic Duality Theorems*, second edition, I.4, for the arithmetic duality
  extending this comparison sequence.
-/

public section

noncomputable section

namespace TauCeti.ContCohomology.SelmerStructure

variable {G : Type*} [Monoid G] [TopologicalSpace G]
  {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  {ι : Type*} {H : ι → Type*} [∀ i, Monoid (H i)] [∀ i, TopologicalSpace (H i)]
  {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, TopologicalSpace (N i)]
  [∀ i, IsTopologicalAddGroup (N i)] [∀ i, DistribMulAction (H i) (N i)]
  [∀ i, ContinuousSMul (H i) (N i)]
  (𝓕 : SelmerStructure G M H N)
  (A B : ∀ i, AddSubgroup (H1 (H i) (N i)))

/-- Replace only the local conditions of a Selmer structure. -/
def withLocalConditions : SelmerStructure G M H N :=
  { 𝓕 with localCondition := A }

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- The updated structure has the prescribed local conditions. -/
@[simp]
theorem withLocalConditions_localCondition (i : ι) :
    (𝓕.withLocalConditions A).localCondition i = A i :=
  (rfl)

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- Replacing the local conditions twice retains only the last system. -/
@[simp]
theorem withLocalConditions_withLocalConditions :
    (𝓕.withLocalConditions A).withLocalConditions B = 𝓕.withLocalConditions B :=
  (rfl)

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- Replacing the local conditions by the original ones changes nothing. -/
@[simp]
theorem withLocalConditions_self : 𝓕.withLocalConditions 𝓕.localCondition = 𝓕 :=
  (rfl)

/-- Updating local conditions leaves the localisation maps unchanged. -/
@[simp]
theorem withLocalConditions_localization (i : ι) :
    (𝓕.withLocalConditions A).localization i = 𝓕.localization i := by
  rw [localization_eq_explicitMap1, localization_eq_explicitMap1]
  rfl

/-- Enlarging every local condition enlarges the Selmer group. -/
theorem selmerGroup_withLocalConditions_mono (hAB : ∀ i, A i ≤ B i) :
    (𝓕.withLocalConditions A).selmerGroup ≤ (𝓕.withLocalConditions B).selmerGroup := by
  intro c hc
  simp only [mem_selmerGroup_iff, withLocalConditions_localization,
    withLocalConditions_localCondition] at hc ⊢
  exact fun i ↦ hAB i (hc i)

/-- Localise a class satisfying `B` at indices in `S`, and reduce modulo `A ∩ B` there.
For nested conditions this is the map to the product of the quotients `B i / A i`.
Neither nesting nor agreement outside `S` is required to define the map. -/
def localConditionComparison (S : Set ι) :
    (𝓕.withLocalConditions B).selmerGroup →+
      ∀ i : S, B i.1 ⧸ (A i.1).addSubgroupOf (B i.1) :=
  AddMonoidHom.pi fun i ↦
    (QuotientAddGroup.mk' ((A i.1).addSubgroupOf (B i.1))).comp
      (((𝓕.localization i.1).comp (𝓕.withLocalConditions B).selmerGroup.subtype).codRestrict
        (B i.1) fun c ↦ by
          simpa only [withLocalConditions_localization, withLocalConditions_localCondition,
            AddMonoidHom.comp_apply, AddSubgroup.subtype_apply]
            using (mem_selmerGroup_iff _).mp c.2 i.1)

/-- The coordinate of the comparison map is the localised class modulo the smaller local
condition. -/
@[simp]
theorem localConditionComparison_apply (S : Set ι)
    (c : (𝓕.withLocalConditions B).selmerGroup) (i : S) :
    𝓕.localConditionComparison A B S c i =
      QuotientAddGroup.mk (⟨𝓕.localization i.1 c,
        (by simpa only [withLocalConditions_localization, withLocalConditions_localCondition]
          using (mem_selmerGroup_iff _).mp c.2 i.1)⟩ : B i.1) :=
  (rfl)

/-- A comparison class vanishes precisely when its localisations at `S` satisfy `A`. -/
@[simp]
theorem localConditionComparison_eq_zero_iff (S : Set ι)
    (c : (𝓕.withLocalConditions B).selmerGroup) :
    𝓕.localConditionComparison A B S c = 0 ↔
      ∀ i ∈ S, 𝓕.localization i c ∈ A i := by
  simp only [funext_iff, localConditionComparison_apply, Pi.zero_apply,
    QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, Subtype.forall]

variable {A B} (S : Set ι)

/-- If `B ≤ A` outside `S`, the kernel of comparison is `Sel_A ∩ Sel_B`, viewed in `Sel_B`. -/
theorem ker_localConditionComparison (hout : ∀ i ∉ S, B i ≤ A i) :
    (𝓕.localConditionComparison A B S).ker =
      ((𝓕.withLocalConditions A).selmerGroup).addSubgroupOf
        (𝓕.withLocalConditions B).selmerGroup := by
  ext c
  simp only [AddMonoidHom.mem_ker, localConditionComparison_eq_zero_iff,
    AddSubgroup.mem_addSubgroupOf, mem_selmerGroup_iff, withLocalConditions_localization,
    withLocalConditions_localCondition]
  refine ⟨fun hc i ↦ ?_, fun hc i _ ↦ hc i⟩
  by_cases hi : i ∈ S
  · exact hc i hi
  · apply hout i hi
    simpa only [withLocalConditions_localization, withLocalConditions_localCondition]
      using (mem_selmerGroup_iff _).mp c.2 i

/-- The change-of-local-conditions sequence is exact at `Sel_B`. In particular this holds
when `A ≤ B` everywhere and the conditions agree outside `S`. -/
theorem exact_inclusion_localConditionComparison (hout : ∀ i ∉ S, B i ≤ A i)
    (hAB : ∀ i, A i ≤ B i) :
    Function.Exact
      (AddSubgroup.inclusion (𝓕.selmerGroup_withLocalConditions_mono A B hAB))
      (𝓕.localConditionComparison A B S) := by
  intro c
  rw [← AddMonoidHom.mem_ker, 𝓕.ker_localConditionComparison S hout,
    AddSubgroup.mem_addSubgroupOf]
  constructor
  · exact fun hc ↦ ⟨⟨c, hc⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact x.2

/-- Finite smaller Selmer group and finite local quotients imply finite larger Selmer group,
when only finitely many local conditions are changed. -/
theorem finite_selmerGroup_of_finite_localQuotients (hout : ∀ i ∉ S, B i ≤ A i)
    (hAB : ∀ i, A i ≤ B i) [Finite S]
    [Finite (𝓕.withLocalConditions A).selmerGroup]
    [∀ i : S, Finite (B i.1 ⧸ (A i.1).addSubgroupOf (B i.1))] :
    Finite (𝓕.withLocalConditions B).selmerGroup :=
  Function.Exact.finite
    (A₀ := (𝓕.withLocalConditions A).selmerGroup)
    (A₂ := ∀ i : S, B i.1 ⧸ (A i.1).addSubgroupOf (B i.1))
    (f₀ := AddSubgroup.inclusion (𝓕.selmerGroup_withLocalConditions_mono A B hAB))
    (f₁ := 𝓕.localConditionComparison A B S)
    (𝓕.exact_inclusion_localConditionComparison S hout hAB)

/-- The relative Selmer index is the order of the image in the local-condition quotients.
This `Nat.card` identity does not assume finiteness. -/
theorem relIndex_selmerGroup_eq_card_range (hout : ∀ i ∉ S, B i ≤ A i) :
    ((𝓕.withLocalConditions A).selmerGroup).relIndex
        (𝓕.withLocalConditions B).selmerGroup =
      Nat.card ((𝓕.localConditionComparison A B S).range
        (N := ∀ i : S, B i.1 ⧸ (A i.1).addSubgroupOf (B i.1))) := by
  have h := AddSubgroup.index_ker
    (G := (𝓕.withLocalConditions B).selmerGroup)
    (G' := ∀ i : S, B i.1 ⧸ (A i.1).addSubgroupOf (B i.1))
    (𝓕.localConditionComparison A B S)
  rw [𝓕.ker_localConditionComparison S hout] at h
  simpa only [AddSubgroup.relIndex] using h

/-- For finitely many changed local conditions, the relative Selmer index divides the product
of the local indices. This also holds with the `Nat.card` convention for infinite groups. -/
theorem relIndex_selmerGroup_dvd_prod (T : Finset ι)
    (hT : ∀ i ∉ T, B i ≤ A i) :
    ((𝓕.withLocalConditions A).selmerGroup).relIndex
        (𝓕.withLocalConditions B).selmerGroup ∣ ∏ i ∈ T, (A i).relIndex (B i) := by
  classical
  rw [𝓕.relIndex_selmerGroup_eq_card_range (T : Set ι) hT]
  have h := AddSubgroup.card_addSubgroup_dvd_card
    ((𝓕.localConditionComparison A B (T : Set ι)).range
      (N := ∀ i : (T : Set ι), B i.1 ⧸ (A i.1).addSubgroupOf (B i.1)))
  have hcard : Nat.card (∀ i : (T : Set ι),
      B i.1 ⧸ (A i.1).addSubgroupOf (B i.1)) = ∏ i ∈ T, (A i).relIndex (B i) := by
    rw [Nat.card_pi]
    simpa only [AddSubgroup.relIndex, AddSubgroup.index_eq_card] using
      (Finset.prod_subtype T (p := fun i ↦ i ∈ (T : Set ι)) (fun _ ↦ Iff.rfl)
        (fun i ↦ (A i).relIndex (B i))).symm
  rwa [hcard] at h

end TauCeti.ContCohomology.SelmerStructure

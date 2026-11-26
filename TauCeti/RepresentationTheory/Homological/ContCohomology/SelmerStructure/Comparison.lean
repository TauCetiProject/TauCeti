/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.SelmerStructure.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Exact.Basic
import Mathlib.GroupTheory.Index

/-!
# Changing the local conditions of a Selmer group

For two Selmer structures `𝓕` and `𝓖`, the comparison map localises `𝓖.selmerGroup` at
indices in a set `S` and reduces modulo `𝓕.localCondition`. Its target is the product of
`𝓖.localCondition i` modulo its intersection with `𝓕.localCondition i`.

If the localisation maps agree and `𝓖.localCondition i ≤ 𝓕.localCondition i` outside `S`,
the kernel is the intersection of the two Selmer groups, viewed inside `𝓖.selmerGroup`.
Consequently, the relative index of `𝓕.selmerGroup` in `𝓖.selmerGroup` equals the `Nat.card`
of the comparison image. If also `𝓕.localCondition i ≤ 𝓖.localCondition i` everywhere,
the inclusion of `𝓕.selmerGroup` followed by comparison is exact at `𝓖.selmerGroup`.

The comparison map need not be surjective: its image records which local classes arise globally.
For finite `S`, under the same localisation-agreement and outside-`S` containment hypotheses,
the relative Selmer index divides the product of the local relative indices. Finiteness of
`𝓕.selmerGroup` and of the local quotients then implies finiteness of `𝓖.selmerGroup`,
without a global nesting hypothesis.

This is the elementary exact-sequence part of a comparison of Selmer orders. Identifying the
cokernel with a dual Selmer obstruction requires arithmetic duality, not just localisation.

The two extreme changes at a set `T` of indices are relaxing (`𝓕^T`, no condition at `T`) and
tightening (`𝓕_T`, the zero condition at `T`), Rubin's `𝓕^Σ` and `𝓕_Σ`.

## Main definitions

* `TauCeti.ContCohomology.SelmerStructure.withLocalConditions`: replace the local conditions
  without changing the localisation data.
* `TauCeti.ContCohomology.SelmerStructure.localConditionComparison`: localisation of
  `𝓖.selmerGroup` modulo `𝓕.localCondition`, at a specified set of indices.
* `TauCeti.ContCohomology.SelmerStructure.relaxedAt`,
  `TauCeti.ContCohomology.SelmerStructure.strictAt`: the Selmer structures relaxed and strict at a
  set of indices.

## Main results

* `TauCeti.ContCohomology.SelmerStructure.mem_selmerGroup_relaxedAt_iff`,
  `TauCeti.ContCohomology.SelmerStructure.mem_selmerGroup_strictAt_iff`: membership in the relaxed
  and strict Selmer groups.
* `TauCeti.ContCohomology.SelmerStructure.exact_inclusion_localConditionComparison`: exactness
  of the change-of-local-conditions sequence.
* `TauCeti.ContCohomology.SelmerStructure.relIndex_selmerGroup_eq_card_range`: the relative
  Selmer index is the order of the localisation image.
* `TauCeti.ContCohomology.SelmerStructure.relIndex_selmerGroup_dvd_prod`: divisibility of the
  relative Selmer index by the product of the local indices.

## References

* K. Rubin, *Euler Systems*, Annals of Mathematics Studies 147, Princeton University Press,
  2000, I.5 and I.7, for Selmer structures and comparison of local conditions.
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
/-- Updating local conditions leaves the group homomorphisms unchanged. -/
@[simp]
theorem withLocalConditions_groupHom :
    (𝓕.withLocalConditions A).groupHom = 𝓕.groupHom :=
  (rfl)

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- Updating local conditions leaves the coefficient homomorphisms unchanged. -/
@[simp]
theorem withLocalConditions_coeffHom :
    (𝓕.withLocalConditions A).coeffHom = 𝓕.coeffHom :=
  (rfl)

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- The updated structure has the prescribed local conditions. -/
@[simp]
theorem withLocalConditions_localCondition :
    (𝓕.withLocalConditions A).localCondition = A :=
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
theorem withLocalConditions_localization :
    (𝓕.withLocalConditions A).localization = 𝓕.localization := by
  funext i
  -- The imported localisation body is opaque; its characterisation exposes the unchanged data.
  rw [localization_eq_explicitMap1, localization_eq_explicitMap1]
  rfl

/-! ### Relaxing and tightening the local conditions on a set of indices -/

section RelaxedStrict

variable (T : Set ι)

/-- The Selmer structure `𝓕^T` relaxed at the indices in `T`: the local condition at `i ∈ T` is
all of `H¹(H i, N i)`, and the other local conditions are those of `𝓕`. -/
def relaxedAt : SelmerStructure G M H N :=
  𝓕.withLocalConditions fun i ↦ 𝓕.localCondition i ⊔ ⨆ _ : i ∈ T, ⊤

/-- The Selmer structure `𝓕_T` strict at the indices in `T`: the local condition at `i ∈ T` is
zero, and the other local conditions are those of `𝓕`. -/
def strictAt : SelmerStructure G M H N :=
  𝓕.withLocalConditions fun i ↦ 𝓕.localCondition i ⊓ ⨅ _ : i ∈ T, ⊥

/-- Relaxing the local conditions leaves the localisation maps unchanged. -/
@[simp]
theorem relaxedAt_localization : (𝓕.relaxedAt T).localization = 𝓕.localization :=
  withLocalConditions_localization _ _

/-- Tightening the local conditions leaves the localisation maps unchanged. -/
@[simp]
theorem strictAt_localization : (𝓕.strictAt T).localization = 𝓕.localization :=
  withLocalConditions_localization _ _

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- At an index of `T`, the relaxed local condition is everything. -/
@[simp]
theorem relaxedAt_localCondition_of_mem {i : ι} (hi : i ∈ T) :
    (𝓕.relaxedAt T).localCondition i = ⊤ := by
  simp [relaxedAt, hi]

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- Outside `T`, relaxing leaves the local condition unchanged. -/
@[simp]
theorem relaxedAt_localCondition_of_notMem {i : ι} (hi : i ∉ T) :
    (𝓕.relaxedAt T).localCondition i = 𝓕.localCondition i := by
  simp [relaxedAt, hi]

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- At an index of `T`, the strict local condition is zero. -/
@[simp]
theorem strictAt_localCondition_of_mem {i : ι} (hi : i ∈ T) :
    (𝓕.strictAt T).localCondition i = ⊥ := by
  simp [strictAt, hi]

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- Outside `T`, tightening leaves the local condition unchanged. -/
@[simp]
theorem strictAt_localCondition_of_notMem {i : ι} (hi : i ∉ T) :
    (𝓕.strictAt T).localCondition i = 𝓕.localCondition i := by
  simp [strictAt, hi]

/-- A class lies in the Selmer group relaxed at `T` exactly when it satisfies the local
conditions of `𝓕` at every index outside `T`. -/
theorem mem_selmerGroup_relaxedAt_iff {c : H1 G M} :
    c ∈ (𝓕.relaxedAt T).selmerGroup ↔ ∀ i ∉ T, 𝓕.localization i c ∈ 𝓕.localCondition i := by
  rw [mem_selmerGroup_iff, relaxedAt_localization]
  refine ⟨fun h i hi ↦ ?_, fun h i ↦ ?_⟩
  · simpa [hi] using h i
  · by_cases hi : i ∈ T
    · simp [hi]
    · simpa [hi] using h i hi

/-- A class lies in the Selmer group strict at `T` exactly when it lies in `𝓕.selmerGroup` and
its localisations at the indices in `T` vanish. -/
theorem mem_selmerGroup_strictAt_iff {c : H1 G M} :
    c ∈ (𝓕.strictAt T).selmerGroup ↔ c ∈ 𝓕.selmerGroup ∧ ∀ i ∈ T, 𝓕.localization i c = 0 := by
  rw [mem_selmerGroup_iff, mem_selmerGroup_iff, strictAt_localization]
  refine ⟨fun h ↦ ⟨fun i ↦ ?_, fun i hi ↦ by simpa [hi] using h i⟩, fun h i ↦ ?_⟩
  · by_cases hi : i ∈ T
    · have h0 : 𝓕.localization i c = 0 := by simpa [hi] using h i
      exact h0 ▸ zero_mem _
    · simpa [hi] using h i
  · by_cases hi : i ∈ T
    · simp [hi, h.2 i hi]
    · simpa [hi] using h.1 i

/-- Relaxing the local conditions enlarges the Selmer group. -/
theorem selmerGroup_le_selmerGroup_relaxedAt : 𝓕.selmerGroup ≤ (𝓕.relaxedAt T).selmerGroup :=
  fun _ hc ↦ (𝓕.mem_selmerGroup_relaxedAt_iff T).mpr fun i _ ↦ (𝓕.mem_selmerGroup_iff.mp hc) i

/-- Tightening the local conditions shrinks the Selmer group. -/
theorem selmerGroup_strictAt_le_selmerGroup : (𝓕.strictAt T).selmerGroup ≤ 𝓕.selmerGroup :=
  fun _ hc ↦ ((𝓕.mem_selmerGroup_strictAt_iff T).mp hc).1

end RelaxedStrict

variable (𝓖 : SelmerStructure G M H N)

/-- Enlarging every local condition enlarges the Selmer group when localisation agrees. -/
theorem selmerGroup_le (hloc : ∀ i, 𝓕.localization i = 𝓖.localization i)
    (hle : ∀ i, 𝓕.localCondition i ≤ 𝓖.localCondition i) :
    𝓕.selmerGroup ≤ 𝓖.selmerGroup := by
  intro c hc
  rw [mem_selmerGroup_iff] at hc ⊢
  intro i
  rw [← hloc i]
  exact hle i (hc i)

/-- Localise a class in `𝓖.selmerGroup` at indices in `S`, and reduce each coordinate in
`𝓖.localCondition i` modulo its intersection with `𝓕.localCondition i`.
Neither nesting, agreement outside `S`, nor agreement of the localisation maps is required
to define the map. -/
def localConditionComparison (S : Set ι) :
    𝓖.selmerGroup →+
      ∀ i : S, 𝓖.localCondition i.val ⧸
        (𝓕.localCondition i.val).addSubgroupOf (𝓖.localCondition i.val) :=
  AddMonoidHom.pi fun i ↦
    (QuotientAddGroup.mk'
      ((𝓕.localCondition i.val).addSubgroupOf (𝓖.localCondition i.val))).comp
      (((𝓖.localization i.val).comp 𝓖.selmerGroup.subtype).codRestrict
        (𝓖.localCondition i.val) fun c ↦ 𝓖.localization_mem c i.val)

/-- The coordinate of the comparison map is the `𝓖`-localised class in `𝓖.localCondition i`
modulo its intersection with `𝓕.localCondition i`. -/
@[simp]
theorem localConditionComparison_apply (S : Set ι) (c : 𝓖.selmerGroup) (i : S) :
    𝓕.localConditionComparison 𝓖 S c i =
      QuotientAddGroup.mk
        (⟨𝓖.localization i.val c, 𝓖.localization_mem c i.val⟩ : 𝓖.localCondition i.val) :=
  (rfl)

/-- A comparison class vanishes precisely when its `𝓖`-localisations at `S` satisfy
`𝓕.localCondition`. -/
@[simp]
theorem localConditionComparison_eq_zero_iff (S : Set ι) (c : 𝓖.selmerGroup) :
    𝓕.localConditionComparison 𝓖 S c = 0 ↔
      ∀ i ∈ S, 𝓖.localization i c ∈ 𝓕.localCondition i := by
  simp only [funext_iff, localConditionComparison_apply, Pi.zero_apply,
    QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, Subtype.forall]

variable (S : Set ι)

/-- If the localisation maps agree and `𝓖.localCondition i ≤ 𝓕.localCondition i` outside
`S`, the kernel of comparison is `𝓕.selmerGroup ∩ 𝓖.selmerGroup`, viewed in `𝓖.selmerGroup`. -/
theorem ker_localConditionComparison (hloc : ∀ i, 𝓕.localization i = 𝓖.localization i)
    (hout : ∀ i ∉ S, 𝓖.localCondition i ≤ 𝓕.localCondition i) :
    (𝓕.localConditionComparison 𝓖 S).ker =
      𝓕.selmerGroup.addSubgroupOf 𝓖.selmerGroup := by
  ext c
  simp only [AddMonoidHom.mem_ker, localConditionComparison_eq_zero_iff,
    AddSubgroup.mem_addSubgroupOf, mem_selmerGroup_iff, hloc]
  refine ⟨fun hc i ↦ ?_, fun hc i _ ↦ hc i⟩
  by_cases hi : i ∈ S
  · exact hc i hi
  · exact hout i hi (𝓖.localization_mem c i)

/-- The inclusion of `𝓕.selmerGroup` followed by comparison is exact at `𝓖.selmerGroup`
when the localisation maps agree, `𝓕.localCondition i ≤ 𝓖.localCondition i` everywhere,
and `𝓖.localCondition i ≤ 𝓕.localCondition i` outside `S`. -/
theorem exact_inclusion_localConditionComparison
    (hloc : ∀ i, 𝓕.localization i = 𝓖.localization i)
    (hout : ∀ i ∉ S, 𝓖.localCondition i ≤ 𝓕.localCondition i)
    (hle : ∀ i, 𝓕.localCondition i ≤ 𝓖.localCondition i) :
    Function.Exact (AddSubgroup.inclusion (𝓕.selmerGroup_le 𝓖 hloc hle))
      (𝓕.localConditionComparison 𝓖 S) := by
  rw [AddMonoidHom.exact_iff (P := ∀ i : S, 𝓖.localCondition i.val ⧸
    (𝓕.localCondition i.val).addSubgroupOf (𝓖.localCondition i.val)),
    𝓕.ker_localConditionComparison 𝓖 S hloc hout, AddSubgroup.inclusion_range]

/-- Finiteness of `𝓕.selmerGroup` and of the local quotients over finite `S` implies
finiteness of `𝓖.selmerGroup` when the localisation maps agree and
`𝓖.localCondition i ≤ 𝓕.localCondition i` outside `S`.
No global nesting of the conditions is required. -/
theorem finite_selmerGroup_of_finite_quotient
    (hloc : ∀ i, 𝓕.localization i = 𝓖.localization i)
    (hout : ∀ i ∉ S, 𝓖.localCondition i ≤ 𝓕.localCondition i)
    [Finite S] [Finite 𝓕.selmerGroup]
    [∀ i : S, Finite (𝓖.localCondition i.val ⧸
      (𝓕.localCondition i.val).addSubgroupOf (𝓖.localCondition i.val))] :
    Finite 𝓖.selmerGroup := by
  apply (AddMonoidHom.finite_iff_finite_ker_range
    (G' := ∀ i : S, 𝓖.localCondition i.val ⧸
      (𝓕.localCondition i.val).addSubgroupOf (𝓖.localCondition i.val))
    (𝓕.localConditionComparison 𝓖 S)).mpr
  refine ⟨?_, inferInstance⟩
  rw [𝓕.ker_localConditionComparison 𝓖 S hloc hout]
  exact Finite.of_injective
    (fun c : 𝓕.selmerGroup.addSubgroupOf 𝓖.selmerGroup ↦
      (⟨c.val.val, c.property⟩ : 𝓕.selmerGroup))
    (fun _ _ h ↦ Subtype.ext (Subtype.ext
      (congrArg (fun c : 𝓕.selmerGroup ↦ (c : H1 G M)) h)))

/-- If the localisation maps agree and `𝓖.localCondition i ≤ 𝓕.localCondition i` outside
`S`, the relative index of `𝓕.selmerGroup` in `𝓖.selmerGroup` is the order of the comparison
image. This `Nat.card` identity does not assume finiteness or global nesting. -/
theorem relIndex_selmerGroup_eq_card_range
    (hloc : ∀ i, 𝓕.localization i = 𝓖.localization i)
    (hout : ∀ i ∉ S, 𝓖.localCondition i ≤ 𝓕.localCondition i) :
    𝓕.selmerGroup.relIndex 𝓖.selmerGroup =
      Nat.card ((𝓕.localConditionComparison 𝓖 S).range
        (N := ∀ i : S, 𝓖.localCondition i.val ⧸
          (𝓕.localCondition i.val).addSubgroupOf (𝓖.localCondition i.val))) := by
  have h := AddSubgroup.index_ker
    (G := 𝓖.selmerGroup)
    (G' := ∀ i : S, 𝓖.localCondition i.val ⧸
      (𝓕.localCondition i.val).addSubgroupOf (𝓖.localCondition i.val))
    (𝓕.localConditionComparison 𝓖 S)
  rw [𝓕.ker_localConditionComparison 𝓖 S hloc hout] at h
  simpa only [AddSubgroup.relIndex] using h

/-- If the localisation maps agree and `𝓖.localCondition i ≤ 𝓕.localCondition i` outside
`T`, the relative index of `𝓕.selmerGroup` in `𝓖.selmerGroup` divides the product over `T`
of the local relative indices. This also holds with the `Nat.card` convention for infinite
groups and does not require global nesting. -/
theorem relIndex_selmerGroup_dvd_prod (T : Finset ι)
    (hloc : ∀ i, 𝓕.localization i = 𝓖.localization i)
    (hT : ∀ i ∉ T, 𝓖.localCondition i ≤ 𝓕.localCondition i) :
    𝓕.selmerGroup.relIndex 𝓖.selmerGroup ∣
      ∏ i ∈ T, (𝓕.localCondition i).relIndex (𝓖.localCondition i) := by
  classical
  rw [𝓕.relIndex_selmerGroup_eq_card_range 𝓖 (T : Set ι) hloc hT]
  have h := AddSubgroup.card_addSubgroup_dvd_card
    ((𝓕.localConditionComparison 𝓖 (T : Set ι)).range
      (N := ∀ i : (T : Set ι), 𝓖.localCondition i.val ⧸
        (𝓕.localCondition i.val).addSubgroupOf (𝓖.localCondition i.val)))
  have hcard : Nat.card (∀ i : (T : Set ι), 𝓖.localCondition i.val ⧸
      (𝓕.localCondition i.val).addSubgroupOf (𝓖.localCondition i.val)) =
        ∏ i ∈ T, (𝓕.localCondition i).relIndex (𝓖.localCondition i) := by
    rw [Nat.card_pi]
    simpa only [AddSubgroup.relIndex, AddSubgroup.index_eq_card] using
      (Finset.prod_subtype T (p := fun i ↦ i ∈ (T : Set ι)) (fun _ ↦ Iff.rfl)
        (fun i ↦ (𝓕.localCondition i).relIndex (𝓖.localCondition i))).symm
  rwa [hcard] at h

end TauCeti.ContCohomology.SelmerStructure

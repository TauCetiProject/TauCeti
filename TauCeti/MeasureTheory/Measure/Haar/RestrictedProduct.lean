/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Probability.ProductMeasure
public import TauCeti.Topology.Algebra.RestrictedProduct.Level
-- Proof-only: Borel measurability of boxes, second countability, open-subgroup pullback Haar
-- measures, Haar instances for infinite product measures, and uniqueness of invariant measures.
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.MeasureTheory.Constructions.BorelSpace.RestrictedProduct
import TauCeti.MeasureTheory.Group.OpenSubgroup.Basic
import TauCeti.MeasureTheory.Measure.Haar.InfinitePi
import TauCeti.MeasureTheory.Measure.Subtype
import TauCeti.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# Restricted products of Haar measures

Let `ι` be a countable index type, `G i` be second-countable locally compact topological groups
with open reference subgroups `B i`, and `μ i` be left Haar measures on `G i` such that
`μ i (B i) = 1` for all but finitely many `i`. Because an open subgroup of finite Haar measure in
a locally compact topological group is automatically compact
(`TauCeti.isCompact_subgroup_of_isOpen_of_measure_ne_top`), cofinitely many `B i` are compact, so
the restricted product `Πʳ i, [G i, B i]` is a second-countable locally compact topological group.

This file constructs the canonical restricted product Haar measure `TauCeti.restrictedHaar μ hμ`
(and its additive counterpart `TauCeti.restrictedAddHaar μ hμ`) and establishes its characterizing
properties:

* `TauCeti.instIsHaarMeasureRestrictedHaar`: `restrictedHaar μ hμ` is a left Haar measure on
  `Πʳ i, [G i, B i]`.
* `TauCeti.restrictedHaar_comap_levelOpenSubgroup`: for every finite set `S : Finset ι` such that
  `μ i (B i) = 1` for all `i ∉ S`, pulling `restrictedHaar μ hμ` back to the level open subgroup
  `U_S = levelOpenSubgroup B S _` identifies it via `levelOpenSubgroupEquiv` with the product of
  the finite product measure `Measure.pi (fun i : S ↦ μ i.1)` and the infinite probability product
  measure `Measure.infinitePi (fun j : {i // i ∉ S} ↦ (μ j.1).comap (↑))`.
* `TauCeti.restrictedHaar_box`: for every family of Borel sets `C i ⊆ G i` with `C i = B i` for
  all but finitely many `i`,
  `restrictedHaar μ hμ {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i)`.
* `TauCeti.eq_restrictedHaar_of_box`: any σ-finite left-invariant measure on `Πʳ i, [G i, B i]`
  satisfying the box formula coincides with `restrictedHaar μ hμ`.
* `TauCeti.exists_unique_restrictedHaar`, `TauCeti.exists_unique_restrictedAddHaar`: existence and
  uniqueness of the restricted product Haar measure.
* `TauCeti.instIsMulRightInvariantRestrictedHaar`, `TauCeti.instIsInvInvariantRestrictedHaar`:
  right invariance and inversion invariance pass from the local Haar measures `μ i` to
  `restrictedHaar μ hμ` (with additive counterparts).

## Implementation

Rather than gluing outer measures across cosets of level subgroups, we construct `restrictedHaar`
by rescaling `Measure.haar` on the second-countable locally compact group `Πʳ i, [G i, B i]` so
that its pullback to the minimal level open subgroup `U_{S₀}` (where `S₀ = {i | μ i (B i) ≠ 1}`)
agrees with the product of `Measure.pi` on `S₀` and `Measure.infinitePi` outside `S₀`. Uniqueness
of σ-finite left-invariant measures up to a positive scalar on every level open subgroup `U_S`
(for `S ⊇ S₀`) then forces the pullback to `U_S` to agree with the level product measure for every
such `S`, from which the box formula, global uniqueness, right invariance, and inversion
invariance follow directly.

## References

* J. Tate, *Fourier analysis in number fields, and Hecke's zeta-functions*, in *Algebraic Number
  Theory* (Cassels–Fröhlich), §3.3.
* D. Ramakrishnan and R. J. Valenza, *Fourier Analysis on Number Fields*, Chapter 5.
* A. Weil, *Basic Number Theory*.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal RestrictedProduct

namespace TauCeti

universe u v w

/-! ### Local compactness from finite-measure open subgroups -/

section OpenSubgroupCompact

/-- If cofinitely many open reference subgroups `B i` have finite measure under local left-invariant
open-positive measures `μ i`, then the restricted product `Πʳ i, [G i, B i]` is locally compact. -/
@[to_additive /-- If cofinitely many open reference additive subgroups `B i` have finite measure
under local left-invariant open-positive measures `μ i`, then the restricted product
`Πʳ i, [G i, B i]` is locally compact. -/]
theorem locallyCompactSpace_restrictedProduct_of_measure_ne_top_of_group {ι : Type u}
    {G : ι → Type v} {H : ι → Type w} [∀ i, Group (G i)] [∀ i, SetLike (H i) (G i)]
    [∀ i, SubgroupClass (H i) (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    [∀ i, LocallyCompactSpace (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
    {B : ∀ i, H i} [hBo : Fact (∀ i, IsOpen (B i : Set (G i)))]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsOpenPosMeasure] [∀ i, (μ i).IsMulLeftInvariant]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) ≠ ∞) :
    LocallyCompactSpace (Πʳ i, [G i, B i]) :=
  RestrictedProduct.locallyCompactSpace_of_group G <|
    hμ.mono fun i hi ↦ isCompact_subgroup_of_isOpen_of_measure_ne_top (hBo.out i) hi

@[to_additive locallyCompactSpace_of_eventually_eq_one_of_addGroup]
private theorem locallyCompactSpace_of_eventually_eq_one {ι : Type u}
    {G : ι → Type v} {H : ι → Type w} [∀ i, Group (G i)] [∀ i, SetLike (H i) (G i)]
    [∀ i, SubgroupClass (H i) (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    [∀ i, LocallyCompactSpace (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
    {B : ∀ i, H i} [Fact (∀ i, IsOpen (B i : Set (G i)))]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsOpenPosMeasure] [∀ i, (μ i).IsMulLeftInvariant]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    LocallyCompactSpace (Πʳ i, [G i, B i]) :=
  locallyCompactSpace_restrictedProduct_of_measure_ne_top_of_group μ
    (hμ.mono fun _ hi ↦ hi ▸ ENNReal.one_ne_top)

end OpenSubgroupCompact

/-! ### Auxiliary finset, finprod, and test-box lemmas -/

section Auxiliary

/-- The finite set of indices where `μ i (B i) ≠ 1`. -/
private noncomputable def nonUnitFinset {ι : Type u} {G : ι → Type v} {H : ι → Type w}
    [∀ i, SetLike (H i) (G i)] [∀ i, MeasurableSpace (G i)] {B : ∀ i, H i}
    (μ : ∀ i, Measure (G i)) (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) : Finset ι :=
  (mem_cofinite.mp hμ).toFinset

private theorem apply_eq_one_of_notMem_nonUnitFinset {ι : Type u} {G : ι → Type v}
    {H : ι → Type w} [∀ i, SetLike (H i) (G i)] [∀ i, MeasurableSpace (G i)] {B : ∀ i, H i}
    (μ : ∀ i, Measure (G i)) (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1)
    (i : ι) (hi : i ∉ nonUnitFinset (B := B) μ hμ) :
    μ i (B i) = 1 := by
  simpa [nonUnitFinset, Set.Finite.mem_toFinset] using hi

private theorem nonUnitFinset_subset {ι : Type u} {G : ι → Type v} {H : ι → Type w}
    [∀ i, SetLike (H i) (G i)] [∀ i, MeasurableSpace (G i)] {B : ∀ i, H i}
    (μ : ∀ i, Measure (G i)) (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) {S : Finset ι}
    (hS : ∀ i ∉ S, μ i (B i) = 1) :
    nonUnitFinset (B := B) μ hμ ⊆ S := fun i hi ↦ by
  by_contra hiS
  have hne : μ i (B i) ≠ 1 := by simpa [nonUnitFinset, Set.Finite.mem_toFinset] using hi
  exact hne (hS i hiS)

/-- When `C i = B i` and `μ i (B i) = 1` outside `S`, the infinite product of local masses reduces
to the finite product over `S`. -/
private theorem finprod_measure_eq_prod {ι : Type u} {G : ι → Type v} {H : ι → Type w}
    [∀ i, SetLike (H i) (G i)] [∀ i, MeasurableSpace (G i)] {B : ∀ i, H i}
    (μ : ∀ i, Measure (G i)) (S : Finset ι) (hS : ∀ i ∉ S, μ i (B i) = 1)
    {C : ∀ i, Set (G i)} (hCS : ∀ i ∉ S, C i = (B i : Set (G i))) :
    ∏ᶠ i, μ i (C i) = ∏ i ∈ S, μ i (C i) :=
  finprod_eq_prod_of_mulSupport_subset (fun i ↦ μ i (C i)) fun i hi ↦ by
    by_contra hiS
    exact hi (by dsimp only; rw [hCS i hiS, hS i hiS])

/-- Existence of a measurable box agreeing with `B i` outside `S` whose finite product of local
masses is strictly positive and finite. -/
@[to_additive exists_add_test_box]
private theorem exists_test_box {ι : Type u} {G : ι → Type v} {H : ι → Type w}
    [∀ i, Group (G i)] [∀ i, SetLike (H i) (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, LocallyCompactSpace (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
    {B : ∀ i, H i} (hBo : ∀ i, IsOpen (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (S : Finset ι) (hS : ∀ i ∉ S, μ i (B i) = 1) :
    ∃ C : ∀ i, Set (G i), (∀ i, MeasurableSet (C i)) ∧
      (∀ i ∉ S, C i = (B i : Set (G i))) ∧
      (∏ᶠ i, μ i (C i) ≠ 0) ∧ (∏ᶠ i, μ i (C i) ≠ ∞) := by
  classical
  choose K hK_comp hK_nhds using fun i ↦ exists_compact_mem_nhds (1 : G i)
  let U : ∀ i, Set (G i) := fun i ↦ interior (K i)
  have hU_pos (i : ι) : 0 < μ i (U i) :=
    isOpen_interior.measure_pos (μ i) ⟨1, mem_interior_iff_mem_nhds.mpr (hK_nhds i)⟩
  have hU_top (i : ι) : μ i (U i) < ∞ :=
    (measure_mono interior_subset).trans_lt (hK_comp i).measure_lt_top
  let C : ∀ i, Set (G i) := fun i ↦ if i ∈ S then U i else (B i : Set (G i))
  have hCS : ∀ i ∉ S, C i = (B i : Set (G i)) := fun i hi ↦ by simp [C, hi]
  have hprod : ∏ᶠ i, μ i (C i) = ∏ i ∈ S, μ i (U i) :=
    (finprod_measure_eq_prod (B := B) μ S hS hCS).trans <|
      Finset.prod_congr rfl fun i hi ↦ by simp [C, hi]
  refine ⟨C, fun i ↦ ?_, hCS, ?_, ?_⟩
  · by_cases hi : i ∈ S
    · simpa [C, hi] using isOpen_interior.measurableSet
    · simpa [C, hi] using (hBo i).measurableSet
  · rw [hprod]
    exact (CanonicallyOrderedAdd.prod_pos.mpr fun i _ ↦ hU_pos i).ne'
  · rw [hprod]
    exact (ENNReal.prod_lt_top fun i _ ↦ hU_top i).ne

end Auxiliary

/-! ### Construction and characterization of restricted product Haar measures -/

section RestrictedHaar

variable {ι : Type u} {G : ι → Type v} {H : ι → Type w}
variable [∀ i, Group (G i)] [∀ i, SetLike (H i) (G i)] [∀ i, SubgroupClass (H i) (G i)]
variable [∀ i, TopologicalSpace (G i)] [∀ i, MeasurableSpace (G i)]
variable {B : ∀ i, H i} [hBo : Fact (∀ i, IsOpen (B i : Set (G i)))]
variable [MeasurableSpace (Πʳ i, [G i, B i])]

/-- The product measure on the level open subgroup `U_S` induced from `Measure.pi` on `S` and
`Measure.infinitePi` of the subspace measures on `B j` for `j ∉ S`. -/
@[to_additive levelAddProductMeasure]
private noncomputable def levelProductMeasure (μ : ∀ i, Measure (G i)) (S : Finset ι) :
    Measure (levelOpenSubgroup B S fun i _ ↦ hBo.out i) :=
  ((Measure.pi fun i : S ↦ μ i.1).prod
    (Measure.infinitePi fun j : {i // i ∉ S} ↦
      (μ j.1).comap ((↑) : B j.1 → G j.1))).map
    (levelOpenSubgroupEquiv B S fun i _ ↦ hBo.out i)

@[to_additive levelAddProductMeasure_def]
private theorem levelProductMeasure_def (μ : ∀ i, Measure (G i)) (S : Finset ι) :
    levelProductMeasure (B := B) μ S =
      ((Measure.pi fun i : S ↦ μ i.1).prod
        (Measure.infinitePi fun j : {i // i ∉ S} ↦
          (μ j.1).comap ((↑) : B j.1 → G j.1))).map
        (levelOpenSubgroupEquiv B S fun i _ ↦ hBo.out i) :=
  rfl

variable [Countable ι]
variable [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)]
variable [∀ i, SecondCountableTopology (G i)] [∀ i, BorelSpace (G i)]
variable [BorelSpace (Πʳ i, [G i, B i])]

/-- Whenever `μ i (B i) = 1` for all `i ∉ S`, the level product measure on `U_S` is a Haar
measure. -/
@[to_additive isAddHaarMeasure_levelAddProductMeasure]
private theorem isHaarMeasure_levelProductMeasure (μ : ∀ i, Measure (G i))
    [∀ i, (μ i).IsHaarMeasure] (S : Finset ι) (hS : ∀ i ∉ S, μ i (B i) = 1) :
    (levelProductMeasure (B := B) μ S).IsHaarMeasure := by
  have (j : {i // i ∉ S}) : IsTopologicalGroup (B j.1) :=
    isTopologicalGroup_induced (SubgroupClass.subtype (B j.1))
  have (j : {i // i ∉ S}) : SecondCountableTopology (B j.1) :=
    TopologicalSpace.secondCountableTopology_induced (B j.1) (G j.1) (↑)
  have (j : {i // i ∉ S}) : IsProbabilityMeasure ((μ j.1).comap ((↑) : B j.1 → G j.1)) :=
    (μ j.1).isProbabilityMeasure_comap_subtype_coe
      (hBo.out j.1).measurableSet.nullMeasurableSet (hS j.1 j.2)
  have (j : {i // i ∉ S}) : ((μ j.1).comap ((↑) : B j.1 → G j.1)).IsOpenPosMeasure :=
    Measure.IsOpenPosMeasure.comap (μ j.1) (hBo.out j.1).isOpenEmbedding_subtypeVal
  rw [levelProductMeasure_def]
  infer_instance

/-- Evaluating the level product measure on a Borel box `{x | ∀ i, x i ∈ C i}` with `C i = B i`
outside `S` yields `∏ᶠ i, μ i (C i)`. -/
@[to_additive levelAddProductMeasure_box]
private theorem levelProductMeasure_box (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (S : Finset ι) (hS : ∀ i ∉ S, μ i (B i) = 1) {C : ∀ i, Set (G i)}
    (hC : ∀ i, MeasurableSet (C i)) (hCS : ∀ i ∉ S, C i = (B i : Set (G i))) :
    levelProductMeasure (B := B) μ S
      (((↑) : levelOpenSubgroup B S (fun i _ ↦ hBo.out i) → Πʳ i, [G i, B i]) ⁻¹'
        {x | ∀ i, x i ∈ C i}) = ∏ᶠ i, μ i (C i) := by
  have (j : {i // i ∉ S}) : SecondCountableTopology (B j.1) :=
    TopologicalSpace.secondCountableTopology_induced (B j.1) (G j.1) (↑)
  have (j : {i // i ∉ S}) : IsProbabilityMeasure ((μ j.1).comap ((↑) : B j.1 → G j.1)) :=
    (μ j.1).isProbabilityMeasure_comap_subtype_coe
      (hBo.out j.1).measurableSet.nullMeasurableSet (hS j.1 j.2)
  have hE : MeasurableSet
      (((↑) : levelOpenSubgroup B S (fun i _ ↦ hBo.out i) → Πʳ i, [G i, B i]) ⁻¹'
        {x | ∀ i, x i ∈ C i}) :=
    measurable_subtype_coe (measurableSet_restrictedProduct_box hC)
  have he : Measurable (levelOpenSubgroupEquiv B S fun i _ ↦ hBo.out i) :=
    (levelOpenSubgroupEquiv B S fun i _ ↦ hBo.out i).continuous.measurable
  rw [levelProductMeasure_def, Measure.map_apply he hE, ← Set.preimage_comp,
    preimage_coe_comp_levelOpenSubgroupEquiv_box]
  have htail : (Set.univ.pi fun j : {i // i ∉ S} ↦ ((↑) : B j.1 → G j.1) ⁻¹' C j.1) = Set.univ := by
    ext y
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_preimage, forall_const, iff_true]
    intro j
    rw [hCS j.1 j.2]
    exact (y j).2
  rw [htail, Measure.prod_prod, Measure.pi_pi, measure_univ, mul_one,
    Finset.prod_coe_sort S fun i ↦ μ i (C i), finprod_measure_eq_prod (B := B) μ S hS hCS]

/-- **Restricted product of Haar measures.** Given local left Haar measures `μ i` on
second-countable locally compact groups `G i` with open subgroups `B i` such that `μ i (B i) = 1`
for all but finitely many `i`, `restrictedHaar μ hμ` is the unique left Haar measure on
`Πʳ i, [G i, B i]` whose mass on every Borel box `{x | ∀ i, x i ∈ C i}` with `C i = B i`
cofinitely is `∏ᶠ i, μ i (C i)`. -/
@[to_additive /-- **Restricted product of additive Haar measures.** Given local left additive Haar
measures `μ i` on second-countable locally compact additive groups `G i` with open additive
subgroups `B i` such that `μ i (B i) = 1` for all but finitely many `i`, `restrictedAddHaar μ hμ`
is the unique left additive Haar measure on `Πʳ i, [G i, B i]` whose mass on every Borel box
`{x | ∀ i, x i ∈ C i}` with `C i = B i` cofinitely is `∏ᶠ i, μ i (C i)`. -/]
noncomputable def restrictedHaar (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) : Measure (Πʳ i, [G i, B i]) :=
  have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    locallyCompactSpace_of_eventually_eq_one μ hμ
  let S₀ : Finset ι := nonUnitFinset (B := B) μ hμ
  let U₀ : OpenSubgroup (Πʳ i, [G i, B i]) := levelOpenSubgroup B S₀ fun i _ ↦ hBo.out i
  have : (levelProductMeasure (B := B) μ S₀).IsHaarMeasure :=
    isHaarMeasure_levelProductMeasure (B := B) μ S₀
      (apply_eq_one_of_notMem_nonUnitFinset (B := B) μ hμ)
  Measure.haarScalarFactor (levelProductMeasure (B := B) μ S₀)
      ((Measure.haar : Measure (Πʳ i, [G i, B i])).comap ((↑) : U₀ → Πʳ i, [G i, B i])) •
    (Measure.haar : Measure (Πʳ i, [G i, B i]))

@[to_additive]
private theorem restrictedHaar_eq_smul (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) [LocallyCompactSpace (Πʳ i, [G i, B i])]
    [(levelProductMeasure (B := B) μ (nonUnitFinset (B := B) μ hμ)).IsHaarMeasure] :
    restrictedHaar (B := B) μ hμ =
      Measure.haarScalarFactor (levelProductMeasure (B := B) μ (nonUnitFinset (B := B) μ hμ))
          ((Measure.haar : Measure (Πʳ i, [G i, B i])).comap
            ((↑) : levelOpenSubgroup B (nonUnitFinset (B := B) μ hμ) (fun i _ ↦ hBo.out i) →
              Πʳ i, [G i, B i])) •
        (Measure.haar : Measure (Πʳ i, [G i, B i])) :=
  rfl

/-- `restrictedHaar μ hμ` is a left Haar measure on `Πʳ i, [G i, B i]`. -/
@[to_additive /-- `restrictedAddHaar μ hμ` is a left additive Haar measure on
`Πʳ i, [G i, B i]`. -/]
instance instIsHaarMeasureRestrictedHaar (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    (restrictedHaar (B := B) μ hμ).IsHaarMeasure := by
  have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    locallyCompactSpace_of_eventually_eq_one μ hμ
  have : (levelProductMeasure (B := B) μ (nonUnitFinset (B := B) μ hμ)).IsHaarMeasure :=
    isHaarMeasure_levelProductMeasure (B := B) μ _
      (apply_eq_one_of_notMem_nonUnitFinset (B := B) μ hμ)
  rw [restrictedHaar_eq_smul (B := B) μ hμ]
  exact Measure.IsHaarMeasure.nnreal_smul Measure.haar
    (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne'

/-- On the minimal level open subgroup `U_{S₀}`, the pullback of `restrictedHaar` equals the level
product measure. -/
@[to_additive]
private theorem restrictedHaar_comap_minimal (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    (restrictedHaar (B := B) μ hμ).comap
        ((↑) : levelOpenSubgroup B (nonUnitFinset (B := B) μ hμ) (fun i _ ↦ hBo.out i) →
          Πʳ i, [G i, B i]) =
      levelProductMeasure (B := B) μ (nonUnitFinset (B := B) μ hμ) := by
  have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    locallyCompactSpace_of_eventually_eq_one μ hμ
  let U₀ : OpenSubgroup (Πʳ i, [G i, B i]) :=
    levelOpenSubgroup B (nonUnitFinset (B := B) μ hμ) fun i _ ↦ hBo.out i
  have : SecondCountableTopology U₀ :=
    TopologicalSpace.secondCountableTopology_induced U₀ (Πʳ i, [G i, B i]) (↑)
  have : (levelProductMeasure (B := B) μ (nonUnitFinset (B := B) μ hμ)).IsHaarMeasure :=
    isHaarMeasure_levelProductMeasure (B := B) μ _
      (apply_eq_one_of_notMem_nonUnitFinset (B := B) μ hμ)
  rw [restrictedHaar_eq_smul (B := B) μ hμ]
  exact (Measure.comap_smul (f := ((↑) : U₀ → Πʳ i, [G i, B i])) (μ := Measure.haar) _).trans
    (Measure.isMulLeftInvariant_eq_smul
      (levelProductMeasure (B := B) μ (nonUnitFinset (B := B) μ hμ))
      ((Measure.haar : Measure (Πʳ i, [G i, B i])).comap ((↑) : U₀ → Πʳ i, [G i, B i]))).symm

/-- **Level product decomposition.** For every finite set `S : Finset ι` such that `μ i (B i) = 1`
for all `i ∉ S`, pulling `restrictedHaar μ hμ` back to the level open subgroup
`levelOpenSubgroup B S _` identifies it via `levelOpenSubgroupEquiv` with the product of
`Measure.pi` on `S` and `Measure.infinitePi` of the normalized subspace measures outside `S`. -/
@[to_additive /-- **Level product decomposition.** For every finite set `S : Finset ι` such that
`μ i (B i) = 1` for all `i ∉ S`, pulling `restrictedAddHaar μ hμ` back to the level open additive
subgroup `levelOpenAddSubgroup B S _` identifies it via `levelOpenAddSubgroupEquiv` with the
product of `Measure.pi` on `S` and `Measure.infinitePi` of the normalized subspace measures outside
`S`. -/]
theorem restrictedHaar_comap_levelOpenSubgroup (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) (S : Finset ι) (hS : ∀ i ∉ S, μ i (B i) = 1) :
    (restrictedHaar (B := B) μ hμ).comap
        ((↑) : levelOpenSubgroup B S (fun i _ ↦ hBo.out i) → Πʳ i, [G i, B i]) =
      ((Measure.pi fun i : S ↦ μ i.1).prod
        (Measure.infinitePi fun j : {i // i ∉ S} ↦
          (μ j.1).comap ((↑) : B j.1 → G j.1))).map
        (levelOpenSubgroupEquiv B S fun i _ ↦ hBo.out i) := by
  have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    locallyCompactSpace_of_eventually_eq_one μ hμ
  let S₀ : Finset ι := nonUnitFinset (B := B) μ hμ
  have hS₀ : ∀ i ∉ S₀, μ i (B i) = 1 := apply_eq_one_of_notMem_nonUnitFinset (B := B) μ hμ
  have hS₀S : S₀ ⊆ S := nonUnitFinset_subset (B := B) μ hμ hS
  let U₀ : OpenSubgroup (Πʳ i, [G i, B i]) := levelOpenSubgroup B S₀ fun i _ ↦ hBo.out i
  let U : OpenSubgroup (Πʳ i, [G i, B i]) := levelOpenSubgroup B S fun i _ ↦ hBo.out i
  have : SecondCountableTopology U :=
    TopologicalSpace.secondCountableTopology_induced U (Πʳ i, [G i, B i]) (↑)
  let ν : Measure (Πʳ i, [G i, B i]) := restrictedHaar (B := B) μ hμ
  let m : Measure U := levelProductMeasure (B := B) μ S
  have : m.IsHaarMeasure := isHaarMeasure_levelProductMeasure (B := B) μ S hS
  -- Evaluate both `ν.comap ↑` and `m` on a positive finite-mass test box lying in `U₀ ⊆ U`.
  obtain ⟨C, hC, hCS₀, hpos, htop⟩ := exists_test_box (B := B) hBo.out μ S₀ hS₀
  have hCS : ∀ i ∉ S, C i = (B i : Set (G i)) := fun i hi ↦ hCS₀ i fun h ↦ hi (hS₀S h)
  let E : Set (Πʳ i, [G i, B i]) := {x | ∀ i, x i ∈ C i}
  have hEU₀ : E ⊆ (U₀ : Set (Πʳ i, [G i, B i])) := fun x hx ↦
    (mem_levelOpenSubgroup B S₀ (fun i _ ↦ hBo.out i) x).mpr fun i hi ↦ by
      simpa only [hCS₀ i hi, SetLike.mem_coe] using hx i
  have hEU : E ⊆ (U : Set (Πʳ i, [G i, B i])) :=
    hEU₀.trans (levelOpenSubgroup_mono B hS₀S (fun i _ ↦ hBo.out i) (fun i _ ↦ hBo.out i))
  have hUemb : MeasurableEmbedding ((↑) : U → Πʳ i, [G i, B i]) :=
    MeasurableEmbedding.subtype_coe U.isOpen.measurableSet
  have hU₀emb : MeasurableEmbedding ((↑) : U₀ → Πʳ i, [G i, B i]) :=
    MeasurableEmbedding.subtype_coe U₀.isOpen.measurableSet
  have hν_U : ν.comap ((↑) : U → Πʳ i, [G i, B i]) (((↑) : U → _) ⁻¹' E) = ν E := by
    rw [hUemb.comap_preimage, Subtype.range_coe_subtype, SetLike.setOfPred_mem_eq,
      Set.inter_eq_left.mpr hEU]
  have hν_U₀ : ν.comap ((↑) : U₀ → Πʳ i, [G i, B i]) (((↑) : U₀ → _) ⁻¹' E) = ν E := by
    rw [hU₀emb.comap_preimage, Subtype.range_coe_subtype, SetLike.setOfPred_mem_eq,
      Set.inter_eq_left.mpr hEU₀]
  have hν_eq : ν.comap ((↑) : U → Πʳ i, [G i, B i]) (((↑) : U → _) ⁻¹' E) = ∏ᶠ i, μ i (C i) := by
    rw [hν_U, ← hν_U₀, restrictedHaar_comap_minimal (B := B) μ hμ,
      levelProductMeasure_box (B := B) μ S₀ hS₀ hC hCS₀]
  have hm_eq : m (((↑) : U → _) ⁻¹' E) = ∏ᶠ i, μ i (C i) :=
    levelProductMeasure_box (B := B) μ S hS hC hCS
  have hdiv := measure_eq_div_smul (ν.comap ((↑) : U → Πʳ i, [G i, B i])) m
    (s := ((↑) : U → _) ⁻¹' E) (hm_eq ▸ hpos) (hm_eq ▸ htop)
  rw [hν_eq, hm_eq, ENNReal.div_self hpos htop, one_smul] at hdiv
  exact hdiv

/-- **Box mass formula.** For every family of Borel sets `C i ⊆ G i` with `C i = B i` for all but
finitely many `i`, `restrictedHaar μ hμ {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i)`. -/
@[to_additive /-- **Box mass formula.** For every family of Borel sets `C i ⊆ G i` with `C i = B i`
for all but finitely many `i`,
`restrictedAddHaar μ hμ {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i)`. -/]
theorem restrictedHaar_box (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) {C : ∀ i, Set (G i)}
    (hC : ∀ i, MeasurableSet (C i)) (hCB : ∀ᶠ i in cofinite, C i = (B i : Set (G i))) :
    restrictedHaar (B := B) μ hμ {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i) := by
  let S : Finset ι := (mem_cofinite.mp (hμ.and hCB)).toFinset
  have hS_both : ∀ i ∉ S, μ i (B i) = 1 ∧ C i = (B i : Set (G i)) := fun i hi ↦ by
    simpa [S, Set.Finite.mem_toFinset] using hi
  have hS : ∀ i ∉ S, μ i (B i) = 1 := fun i hi ↦ (hS_both i hi).1
  have hCS : ∀ i ∉ S, C i = (B i : Set (G i)) := fun i hi ↦ (hS_both i hi).2
  let U : OpenSubgroup (Πʳ i, [G i, B i]) := levelOpenSubgroup B S fun i _ ↦ hBo.out i
  let E : Set (Πʳ i, [G i, B i]) := {x | ∀ i, x i ∈ C i}
  have hEU : E ⊆ (U : Set (Πʳ i, [G i, B i])) := fun x hx ↦
    (mem_levelOpenSubgroup B S (fun i _ ↦ hBo.out i) x).mpr fun i hi ↦ by
      simpa only [hCS i hi, SetLike.mem_coe] using hx i
  have hUemb : MeasurableEmbedding ((↑) : U → Πʳ i, [G i, B i]) :=
    MeasurableEmbedding.subtype_coe U.isOpen.measurableSet
  calc restrictedHaar (B := B) μ hμ E
      = (restrictedHaar (B := B) μ hμ).comap ((↑) : U → Πʳ i, [G i, B i])
          (((↑) : U → _) ⁻¹' E) := by
        rw [hUemb.comap_preimage, Subtype.range_coe_subtype, SetLike.setOfPred_mem_eq,
          Set.inter_eq_left.mpr hEU]
    _ = levelProductMeasure (B := B) μ S (((↑) : U → _) ⁻¹' E) := by
        rw [restrictedHaar_comap_levelOpenSubgroup (B := B) μ hμ S hS, ← levelProductMeasure_def]
    _ = ∏ᶠ i, μ i (C i) := levelProductMeasure_box (B := B) μ S hS hC hCS

/-- **Uniqueness of the restricted product Haar measure.** Any σ-finite left-invariant measure on
`Πʳ i, [G i, B i]` that satisfies the box mass formula agrees with `restrictedHaar μ hμ`. -/
@[to_additive /-- **Uniqueness of the restricted product additive Haar measure.** Any σ-finite
left-invariant measure on `Πʳ i, [G i, B i]` that satisfies the box mass formula agrees with
`restrictedAddHaar μ hμ`. -/]
theorem eq_restrictedHaar_of_box (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) {ν : Measure (Πʳ i, [G i, B i])}
    [SigmaFinite ν] [ν.IsMulLeftInvariant]
    (hbox : ∀ C : ∀ i, Set (G i), (∀ i, MeasurableSet (C i)) →
      (∀ᶠ i in cofinite, C i = (B i : Set (G i))) →
      ν {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i)) :
    ν = restrictedHaar (B := B) μ hμ := by
  have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    locallyCompactSpace_of_eventually_eq_one μ hμ
  let S₀ : Finset ι := nonUnitFinset (B := B) μ hμ
  obtain ⟨C, hC, hCS₀, hpos, htop⟩ :=
    exists_test_box (B := B) hBo.out μ S₀ (apply_eq_one_of_notMem_nonUnitFinset (B := B) μ hμ)
  have hCB : ∀ᶠ i in cofinite, C i = (B i : Set (G i)) := by
    filter_upwards [S₀.finite_toSet.compl_mem_cofinite] with i hi
    exact hCS₀ i hi
  let E : Set (Πʳ i, [G i, B i]) := {x | ∀ i, x i ∈ C i}
  have hνE : ν E = ∏ᶠ i, μ i (C i) := hbox C hC hCB
  have hμE : restrictedHaar (B := B) μ hμ E = ∏ᶠ i, μ i (C i) :=
    restrictedHaar_box (B := B) μ hμ hC hCB
  have hdiv := measure_eq_div_smul ν (restrictedHaar (B := B) μ hμ) (s := E)
    (hμE ▸ hpos) (hμE ▸ htop)
  rwa [hνE, hμE, ENNReal.div_self hpos htop, one_smul] at hdiv

/-- **Existence and uniqueness of the restricted product Haar measure.** Given local left Haar
measures `μ i` on second-countable locally compact groups `G i` with open subgroups `B i` such that
`μ i (B i) = 1` for all but finitely many `i`, there is a unique left Haar measure `ν` on
`Πʳ i, [G i, B i]` assigning every Borel box `{x | ∀ i, x i ∈ C i}` with `C i = B i` cofinitely
the mass `∏ᶠ i, μ i (C i)`. -/
@[to_additive /-- **Existence and uniqueness of the restricted product additive Haar measure.**
Given local left additive Haar measures `μ i` on second-countable locally compact additive groups
`G i` with open additive subgroups `B i` such that `μ i (B i) = 1` for all but finitely many `i`,
there is a unique left additive Haar measure `ν` on `Πʳ i, [G i, B i]` assigning every Borel box
`{x | ∀ i, x i ∈ C i}` with `C i = B i` cofinitely the mass `∏ᶠ i, μ i (C i)`. -/]
theorem exists_unique_restrictedHaar (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    ∃! ν : Measure (Πʳ i, [G i, B i]), ν.IsHaarMeasure ∧
      ∀ C : ∀ i, Set (G i), (∀ i, MeasurableSet (C i)) →
        (∀ᶠ i in cofinite, C i = (B i : Set (G i))) →
        ν {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i) := by
  have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    locallyCompactSpace_of_eventually_eq_one μ hμ
  exact ⟨restrictedHaar (B := B) μ hμ,
    ⟨inferInstance, fun _ hC hCB ↦ restrictedHaar_box (B := B) μ hμ hC hCB⟩,
    fun _ ⟨_, hbox⟩ ↦ eq_restrictedHaar_of_box (B := B) μ hμ hbox⟩

/-- If every local Haar measure `μ i` is right-invariant, then `restrictedHaar μ hμ` is
right-invariant. -/
@[to_additive /-- If every local additive Haar measure `μ i` is right-invariant, then
`restrictedAddHaar μ hμ` is right-invariant. -/]
instance instIsMulRightInvariantRestrictedHaar (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    [∀ i, (μ i).IsMulRightInvariant] (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    (restrictedHaar (B := B) μ hμ).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
      locallyCompactSpace_of_eventually_eq_one μ hμ
    refine eq_restrictedHaar_of_box (B := B) μ hμ fun C hC hCB ↦ ?_
    rw [Measure.map_apply (measurable_mul_const g) (measurableSet_restrictedProduct_box hC)]
    have hpre : (· * g) ⁻¹' {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ C i} =
        {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ (· * g i) ⁻¹' C i} := by
      ext x
      simp
    have hCB' : ∀ᶠ i in cofinite, (· * g i) ⁻¹' C i = (B i : Set (G i)) := by
      filter_upwards [hCB, g.2] with i hiC hig
      ext y
      simp only [Set.mem_preimage, hiC, SetLike.mem_coe]
      exact mul_mem_cancel_right hig
    rw [hpre, restrictedHaar_box (B := B) μ hμ (fun i ↦ measurable_mul_const (g i) (hC i)) hCB']
    simp_rw [measure_preimage_mul_right]

/-- If every local Haar measure `μ i` is inversion-invariant, then `restrictedHaar μ hμ` is
inversion-invariant. -/
@[to_additive /-- If every local additive Haar measure `μ i` is negation-invariant, then
`restrictedAddHaar μ hμ` is negation-invariant. -/]
instance instIsInvInvariantRestrictedHaar (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    [∀ i, (μ i).IsInvInvariant] (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    (restrictedHaar (B := B) μ hμ).IsInvInvariant := by
  have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    locallyCompactSpace_of_eventually_eq_one μ hμ
  have (i : ι) : (μ i).IsMulRightInvariant := by
    rw [← Measure.inv_eq_self (μ i)]
    infer_instance
  refine ⟨eq_restrictedHaar_of_box (B := B) μ hμ fun C hC hCB ↦ ?_⟩
  rw [Measure.inv_def, Measure.map_apply measurable_inv (measurableSet_restrictedProduct_box hC)]
  have hpre : Inv.inv ⁻¹' {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ C i} =
      {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ Inv.inv ⁻¹' C i} := by
    ext x
    simp
  have hCB' : ∀ᶠ i in cofinite, Inv.inv ⁻¹' C i = (B i : Set (G i)) := by
    filter_upwards [hCB] with i hiC
    ext y
    simp only [Set.mem_preimage, hiC, SetLike.mem_coe, inv_mem_iff]
  rw [hpre, restrictedHaar_box (B := B) μ hμ (fun i ↦ measurable_inv (hC i)) hCB']
  simp_rw [Measure.measure_preimage_inv]

end RestrictedHaar

end TauCeti

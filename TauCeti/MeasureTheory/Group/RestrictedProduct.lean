/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import TauCeti.MeasureTheory.Constructions.BorelSpace.RestrictedProduct
public import TauCeti.MeasureTheory.Group.InfinitePi
public import TauCeti.MeasureTheory.Group.OpenSubgroup.Basic
public import TauCeti.Topology.Algebra.RestrictedProduct.Away.Decomposition

/-!
# Restricted products of Haar measures

Let `(G i)_{i : ι}` be a countable family of second-countable, weakly locally compact topological
groups equipped with Borel Haar measures `μ i` and open subgroups `B i` (represented via
`SubgroupClass` / `AddSubgroupClass`, covering `Subgroup`, `OpenSubgroup`, `ValuationSubring`, and
their additive counterparts) normalized so that `μ i (B i) = 1` for all but finitely many `i`.

Each open subgroup `B i` of finite `μ i`-measure is automatically compact
(`OpenSubgroup.isCompact_of_measure_ne_top`), so `Πʳ i, [G i, B i]` is a locally compact,
second-countable topological group. For every finite index set `F : Finset ι` outside which
`μ i (B i) = 1`, the open level subgroup `{x : Πʳ i, [G i, B i] | ∀ i ∉ F, x i ∈ B i}` is
isomorphic as a topological group via `TauCeti.restrictedProductLevelInclusion` to
`(∀ i : F, G i.1) × (∀ j : {i // i ∉ F}, B j.1)`, which carries the product Haar measure
`TauCeti.restrictedProductLevelMeasure` built from `Measure.pi` on `F` and Kolmogorov's
probability product measure `Measure.infinitePi` on the compact open factors outside `F`.

Rescaling an ambient Haar measure on `Πʳ i, [G i, B i]` to match this product measure on a base
level yields the canonical **restricted Haar measure** `TauCeti.restrictedHaar` (additive version
`TauCeti.restrictedAddHaar`), uniquely characterized by the product formula
`ν {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i)` on measurable cofinite boxes.

## Main definitions

* `TauCeti.restrictedProductLevelInclusion` / `TauCeti.addRestrictedProductLevelInclusion`: open
  embedding homomorphism `((∀ i : F, G i.1) × (∀ j : {i // i ∉ F}, B j.1)) →* Πʳ i, [G i, B i]`
  onto `{x | ∀ i ∉ F, x i ∈ B i}`.
* `TauCeti.restrictedProductLevelMeasure`: the product measure of `Measure.pi (fun i : F ↦ μ i.1)`
  with `Measure.infinitePi (fun j : {i // i ∉ F} ↦ (μ j.1).comap (↑))`.
* `TauCeti.restrictedHaar` / `TauCeti.restrictedAddHaar`: the restricted product of the local Haar
  measures `μ i` on `Πʳ i, [G i, B i]`.

## Main results

* `TauCeti.isHaarMeasure_restrictedHaar` / `TauCeti.isAddHaarMeasure_restrictedAddHaar`:
  `restrictedHaar B μ` is a Haar measure when `μ i (B i) = 1` cofinitely.
* `TauCeti.comap_restrictedProductLevelInclusion_restrictedHaar`,
  `TauCeti.setLIntegral_restrictedHaar_setOf_forall_notMem_eq`,
  `TauCeti.setIntegral_restrictedHaar_setOf_forall_notMem_eq`: level compatibility and integration
  formulas on `{x | ∀ i ∉ F, x i ∈ B i}` for every finite `F` with `∀ i ∉ F, μ i (B i) = 1`.
* `TauCeti.restrictedHaar_setOf_forall_mem` / `TauCeti.restrictedAddHaar_setOf_forall_mem`:
  box evaluation `restrictedHaar B μ {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i)` whenever every `C i`
  is measurable and `C i = B i` cofinitely.
* `TauCeti.exists_unique_restrictedHaar` / `TauCeti.exists_unique_restrictedAddHaar`: existence and
  uniqueness of the Haar measure on `Πʳ i, [G i, B i]` satisfying the cofinite box formula.
* `TauCeti.isMulRightInvariant_restrictedHaar`, `TauCeti.isInvInvariant_restrictedHaar`,
  `TauCeti.map_awayDecomposition_restrictedHaar`, `TauCeti.restrictedHaar_smul`: right/inversion
  invariance (unimodularity inheritance), finite-place decomposition, and finite scalar rescaling.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in J. W. S. Cassels and
  A. Fröhlich (eds.), *Algebraic Number Theory*, Academic Press (1967), §3.3.
* D. Ramakrishnan and R. J. Valenza, *Fourier Analysis on Number Fields*, Graduate Texts in
  Mathematics 186, Springer (1999), Chapter 5, §5.1, Theorem 5-3.
* V. Platonov, A. Rapinchuk, and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. I, 2nd
  ed., Cambridge University Press (2023), §3.5, Lemma 3.63.
-/

public section

noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal Pointwise RestrictedProduct

namespace TauCeti

/-! ### Open level-subgroup inclusions -/

section LevelInclusion

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]
  {S : ι → Type*} [∀ i, SetLike (S i) (G i)] [∀ i, SubgroupClass (S i) (G i)]

open Classical in
/-- For a finite index set `F : Finset ι`, the homomorphism embedding
`(∀ i : F, G i.1) × (∀ j : {i // i ∉ F}, B j.1)` into `Πʳ i, [G i, B i]` as the subgroup of
elements whose coordinates outside `F` lie in `B`. -/
@[to_additive addRestrictedProductLevelInclusion
  /-- For a finite index set `F : Finset ι`, the additive homomorphism embedding
  `(∀ i : F, G i.1) × (∀ j : {i // i ∉ F}, B j.1)` into `Πʳ i, [G i, B i]` as the additive subgroup
  of elements whose coordinates outside `F` lie in `B`. -/]
def restrictedProductLevelInclusion (B : ∀ i, S i) (F : Finset ι) :
    ((∀ i : F, G i.1) × (∀ j : {i // i ∉ F}, B j.1)) →* Πʳ i, [G i, B i] where
  toFun p := RestrictedProduct.mk (fun i ↦ if hi : i ∈ F then p.1 ⟨i, hi⟩ else p.2 ⟨i, hi⟩)
    (F.eventually_cofinite_notMem.mono fun i hi ↦ by simp [hi])
  map_one' := by
    ext i
    by_cases hi : i ∈ F <;> simp [hi]
  map_mul' p q := by
    ext i
    simp only [RestrictedProduct.mul_apply, RestrictedProduct.mk_apply]
    by_cases hi : i ∈ F <;> simp [hi]

@[to_additive (attr := simp) addRestrictedProductLevelInclusion_apply_of_mem]
theorem restrictedProductLevelInclusion_apply_of_mem (B : ∀ i, S i) (F : Finset ι)
    (p : (∀ i : F, G i.1) × (∀ j : {i // i ∉ F}, B j.1)) {i : ι} (hi : i ∈ F) :
    restrictedProductLevelInclusion B F p i = p.1 ⟨i, hi⟩ := by
  simp [restrictedProductLevelInclusion, hi]

@[to_additive (attr := simp) addRestrictedProductLevelInclusion_apply_of_notMem]
theorem restrictedProductLevelInclusion_apply_of_notMem (B : ∀ i, S i) (F : Finset ι)
    (p : (∀ i : F, G i.1) × (∀ j : {i // i ∉ F}, B j.1)) {i : ι} (hi : i ∉ F) :
    restrictedProductLevelInclusion B F p i = p.2 ⟨i, hi⟩ := by
  simp [restrictedProductLevelInclusion, hi]

/-- The range of `restrictedProductLevelInclusion B F` is `{x | ∀ i ∉ F, x i ∈ B i}`. -/
@[to_additive range_addRestrictedProductLevelInclusion
  /-- The range of `addRestrictedProductLevelInclusion B F` is `{x | ∀ i ∉ F, x i ∈ B i}`. -/]
theorem range_restrictedProductLevelInclusion (B : ∀ i, S i) (F : Finset ι) :
    range (restrictedProductLevelInclusion B F) =
      {x : Πʳ i, [G i, B i] | ∀ i ∉ F, x i ∈ B i} := by
  ext x
  simp only [mem_range, mem_ofPred_eq]
  refine ⟨?_, fun hx ↦ ⟨(fun i ↦ x i.1, fun j ↦ ⟨x j.1, hx j.1 j.2⟩), ?_⟩⟩
  · rintro ⟨p, rfl⟩ i hi
    rw [restrictedProductLevelInclusion_apply_of_notMem B F p hi]
    exact (p.2 ⟨i, hi⟩).2
  · ext i
    by_cases hi : i ∈ F
    · exact restrictedProductLevelInclusion_apply_of_mem B F _ hi
    · exact restrictedProductLevelInclusion_apply_of_notMem B F _ hi

/-- Preimage of any coordinate box `{x | ∀ i, x i ∈ C i}` under
`restrictedProductLevelInclusion B F`. -/
@[to_additive preimage_addRestrictedProductLevelInclusion_setOf_forall_mem
  /-- Preimage of any coordinate box `{x | ∀ i, x i ∈ C i}` under
  `addRestrictedProductLevelInclusion B F`. -/]
theorem preimage_restrictedProductLevelInclusion_setOf_forall_mem (B : ∀ i, S i) (F : Finset ι)
    (C : ∀ i, Set (G i)) :
    restrictedProductLevelInclusion B F ⁻¹' {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ C i} =
      (univ.pi fun i : F ↦ C i.1) ×ˢ
        (univ.pi fun j : {i // i ∉ F} ↦ ((↑) : B j.1 → G j.1) ⁻¹' C j.1) := by
  ext ⟨y, z⟩
  simp only [mem_preimage, mem_ofPred_eq, mem_prod, mem_univ_pi]
  refine ⟨fun h ↦ ⟨fun i ↦ ?_, fun j ↦ ?_⟩, fun ⟨hy, hz⟩ i ↦ ?_⟩
  · simpa only [restrictedProductLevelInclusion_apply_of_mem B F (y, z) i.2] using h i.1
  · simpa only [restrictedProductLevelInclusion_apply_of_notMem B F (y, z) j.2] using h j.1
  · by_cases hi : i ∈ F
    · rw [restrictedProductLevelInclusion_apply_of_mem B F (y, z) hi]
      exact hy ⟨i, hi⟩
    · rw [restrictedProductLevelInclusion_apply_of_notMem B F (y, z) hi]
      exact hz ⟨i, hi⟩

/-- When the reference subgroups away from `F` are open, `restrictedProductLevelInclusion B F` is an
open topological embedding. -/
@[to_additive isOpenEmbedding_addRestrictedProductLevelInclusion
  /-- When the reference additive subgroups away from `F` are open,
  `addRestrictedProductLevelInclusion B F` is an open topological embedding. -/]
theorem isOpenEmbedding_restrictedProductLevelInclusion [∀ i, TopologicalSpace (G i)]
    (B : ∀ i, S i) (F : Finset ι) (hB : ∀ i ∉ F, IsOpen (B i : Set (G i))) :
    IsOpenEmbedding (restrictedProductLevelInclusion B F) := by
  let U : ∀ i, Subgroup (G i) := fun i ↦ Subgroup.ofClass (B i)
  let e : (Πʳ i, [G i, U i]) ≃ₜ
      (∀ i : (F : Set ι), G i.1) × (Πʳ j : {i // i ∉ F}, [G j.1, U j.1]) :=
    { toEquiv := (awayDecomposition (F : Set ι) F.finite_toSet U).toEquiv
      continuous_toFun := continuous_awayDecomposition (F : Set ι) F.finite_toSet U
      continuous_invFun := continuous_awayDecomposition_symm (F : Set ι) F.finite_toSet U hB }
  have hprod : IsOpenEmbedding
      (Prod.map (id : (∀ i : F, G i.1) → ∀ i : F, G i.1)
        (RestrictedProduct.structureMap (fun j : {i // i ∉ F} ↦ G j.1)
          (fun j ↦ (U j.1 : Set (G j.1))) cofinite)) :=
    IsOpenEmbedding.id.prodMap
      (RestrictedProduct.isOpenEmbedding_structureMap fun j ↦ hB j.1 j.2)
  have hf : IsOpenEmbedding
      ((e.symm ∘ Prod.map (id : (∀ i : F, G i.1) → ∀ i : F, G i.1)
        (RestrictedProduct.structureMap (fun j : {i // i ∉ F} ↦ G j.1)
          (fun j ↦ (U j.1 : Set (G j.1))) cofinite)) :
        ((∀ i : F, G i.1) × (∀ j : {i // i ∉ F}, B j.1)) → Πʳ i, [G i, B i]) :=
    e.symm.isOpenEmbedding.comp hprod
  convert hf using 1
  ext p i
  by_cases hi : i ∈ F
  · rw [restrictedProductLevelInclusion_apply_of_mem B F p hi]
    exact (awayDecomposition_symm_apply_of_mem (F : Set ι) F.finite_toSet U
      (p.1, RestrictedProduct.structureMap _ _ cofinite p.2) i hi).symm
  · rw [restrictedProductLevelInclusion_apply_of_notMem B F p hi]
    exact (awayDecomposition_symm_apply_of_notMem (F : Set ι) F.finite_toSet U
      (p.1, RestrictedProduct.structureMap _ _ cofinite p.2) i hi).symm

/-- Over a countable index type with second-countable Borel factors,
`restrictedProductLevelInclusion B F` is a measurable embedding whenever the subgroups away from `F`
are open. -/
@[to_additive measurableEmbedding_addRestrictedProductLevelInclusion
  /-- Over a countable index type with second-countable Borel factors,
  `addRestrictedProductLevelInclusion B F` is a measurable embedding whenever the additive subgroups
  away from `F` are open. -/]
theorem measurableEmbedding_restrictedProductLevelInclusion [Countable ι]
    [∀ i, TopologicalSpace (G i)] [∀ i, SecondCountableTopology (G i)]
    [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)] (B : ∀ i, S i)
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (F : Finset ι) (hB : ∀ i ∉ F, IsOpen (B i : Set (G i))) :
    MeasurableEmbedding (restrictedProductLevelInclusion B F) := by
  have (j : {i // i ∉ F}) : SecondCountableTopology (B j.1) :=
    TopologicalSpace.secondCountableTopology_induced (B j.1) (G j.1) Subtype.val
  exact (isOpenEmbedding_restrictedProductLevelInclusion B F hB).measurableEmbedding

end LevelInclusion

/-! ### Level product measures -/

section LevelMeasure

/-- On the finite-level product `(∀ i : F, G i.1) × (∀ j : {i // i ∉ F}, B j.1)`, the product of the
finite product measure `Measure.pi` on `F` with Kolmogorov's infinite product measure
`Measure.infinitePi` of the subtype pullbacks `(μ j.1).comap (↑)` away from `F`. -/
def restrictedProductLevelMeasure {ι : Type*} {G : ι → Type*} [∀ i, MeasurableSpace (G i)]
    {S : ι → Type*} [∀ i, SetLike (S i) (G i)] (B : ∀ i, S i) (μ : ∀ i, Measure (G i))
    (F : Finset ι) : Measure ((∀ i : F, G i.1) × (∀ j : {i // i ∉ F}, B j.1)) :=
  (Measure.pi fun i : F ↦ μ i.1).prod
    (Measure.infinitePi fun j : {i // i ∉ F} ↦ (μ j.1).comap ((↑) : B j.1 → G j.1))

private theorem isProbabilityMeasure_comap_of_eq_one {X : Type*} [MeasurableSpace X] {B : Set X}
    (hB : MeasurableSet B) {μ : Measure X} (hμ : μ B = 1) :
    IsProbabilityMeasure (μ.comap ((↑) : B → X)) := by
  refine ⟨?_⟩
  rw [(MeasurableEmbedding.subtype_coe hB).comap_apply, image_univ, Subtype.range_coe]
  exact hμ

/-- When the subgroups away from `F` are open of `μ i`-measure `1` and the factors on `F` are
σ-finite, `restrictedProductLevelMeasure B μ F` is a Haar measure. -/
@[to_additive
  /-- When the additive subgroups away from `F` are open of `μ i`-measure `1` and the factors on `F`
  are σ-finite, `restrictedProductLevelMeasure B μ F` is an additive Haar measure. -/]
theorem isHaarMeasure_restrictedProductLevelMeasure {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
    [∀ i, MeasurableMul (G i)] {S : ι → Type*} [∀ i, SetLike (S i) (G i)]
    [∀ i, SubgroupClass (S i) (G i)] (B : ∀ i, S i) (μ : ∀ i, Measure (G i))
    [∀ i, (μ i).IsHaarMeasure] {F : Finset ι} [∀ i : F, SigmaFinite (μ i.1)]
    (hB : ∀ i ∉ F, IsOpen (B i : Set (G i))) (hF : ∀ i ∉ F, μ i (B i) = 1) :
    (restrictedProductLevelMeasure B μ F).IsHaarMeasure := by
  have (j : {i // i ∉ F}) : IsProbabilityMeasure ((μ j.1).comap ((↑) : B j.1 → G j.1)) :=
    isProbabilityMeasure_comap_of_eq_one (hB j.1 j.2).measurableSet (hF j.1 j.2)
  have (j : {i // i ∉ F}) : ((μ j.1).comap ((↑) : B j.1 → G j.1)).IsHaarMeasure :=
    OpenSubgroup.instIsHaarMeasureComap (μ j.1) ⟨Subgroup.ofClass (B j.1), hB j.1 j.2⟩
  rw [restrictedProductLevelMeasure]
  infer_instance

/-- **Evaluation of `restrictedProductLevelMeasure` on preimages of boxes.** If `F ⊆ T`, every
`C i` is measurable, `C i ⊆ B i` outside `F`, and `C i = B i` outside `T`, then the
`restrictedProductLevelMeasure B μ F` mass of the preimage of `{x | ∀ i, x i ∈ C i}` equals the
finite product `∏ i ∈ T, μ i (C i)`. -/
@[to_additive restrictedProductLevelMeasure_preimage_addLevelInclusion_setOf_forall_mem
  /-- **Evaluation of `restrictedProductLevelMeasure` on preimages of boxes (additive).** If
  `F ⊆ T`, every `C i` is measurable, `C i ⊆ B i` outside `F`, and `C i = B i` outside `T`, then the
  `restrictedProductLevelMeasure B μ F` mass of the preimage of `{x | ∀ i, x i ∈ C i}` equals
  `∏ i ∈ T, μ i (C i)`. -/]
theorem restrictedProductLevelMeasure_preimage_setOf_forall_mem {ι : Type*} {G : ι → Type*}
    [∀ i, Group (G i)] [∀ i, MeasurableSpace (G i)] {S : ι → Type*} [∀ i, SetLike (S i) (G i)]
    [∀ i, SubgroupClass (S i) (G i)] (B : ∀ i, S i) (μ : ∀ i, Measure (G i))
    {F T : Finset ι} [∀ i : F, SigmaFinite (μ i.1)]
    (hB : ∀ i ∉ F, MeasurableSet (B i : Set (G i))) (hF : ∀ i ∉ F, μ i (B i) = 1)
    (hFT : F ⊆ T) {C : ∀ i, Set (G i)} (hC : ∀ i, MeasurableSet (C i))
    (hCB : ∀ i ∉ F, C i ⊆ B i) (hCT : ∀ i ∉ T, C i = B i) :
    restrictedProductLevelMeasure B μ F
        (restrictedProductLevelInclusion B F ⁻¹' {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ C i}) =
      ∏ i ∈ T, μ i (C i) := by
  classical
  have (j : {i // i ∉ F}) : IsProbabilityMeasure ((μ j.1).comap ((↑) : B j.1 → G j.1)) :=
    isProbabilityMeasure_comap_of_eq_one (hB j.1 j.2) (hF j.1 j.2)
  rw [preimage_restrictedProductLevelInclusion_setOf_forall_mem, restrictedProductLevelMeasure,
    Measure.prod_prod, Measure.pi_pi]
  have hpi : (univ.pi fun j : {i // i ∉ F} ↦ ((↑) : B j.1 → G j.1) ⁻¹' C j.1) =
      (↑(T.subtype (· ∉ F)) : Set {i // i ∉ F}).pi
        fun j ↦ ((↑) : B j.1 → G j.1) ⁻¹' C j.1 := by
    ext z
    simp only [Set.mem_pi, mem_univ, true_implies, Finset.mem_coe, Finset.mem_subtype]
    refine ⟨fun h j _ ↦ h j, fun h j ↦ ?_⟩
    by_cases hjT : j.1 ∈ T
    · exact h j hjT
    · rw [mem_preimage, hCT j.1 hjT]
      exact (z j).2
  rw [hpi, Measure.infinitePi_pi _ fun j _ ↦ measurable_subtype_coe (hC j.1)]
  have hsub : ∀ j : {i // i ∉ F},
      ((μ j.1).comap ((↑) : B j.1 → G j.1)) (((↑) : B j.1 → G j.1) ⁻¹' C j.1) =
        μ j.1 (C j.1) := fun j ↦ by
    have hcoe : MeasurableEmbedding ((↑) : B j.1 → G j.1) :=
      MeasurableEmbedding.subtype_coe (hB j.1 j.2)
    rw [hcoe.comap_apply]
    congr 1
    ext x
    simp only [mem_image, mem_preimage, Subtype.exists, exists_and_right, exists_eq_right]
    exact ⟨fun ⟨_, hx⟩ ↦ hx, fun hx ↦ ⟨hCB j.1 j.2 hx, hx⟩⟩
  simp_rw [hsub]
  rw [Finset.prod_coe_sort F (fun i ↦ μ i (C i)),
    Finset.prod_subtype_eq_prod_filter (f := fun i ↦ μ i (C i)),
    Finset.filter_notMem_eq_sdiff, mul_comm, Finset.prod_sdiff hFT]

end LevelMeasure

/-! ### Restricted product of Haar measures -/

section RestrictedHaar

variable {ι : Type*} {G : ι → Type*} [Countable ι] [∀ i, Group (G i)]
  [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
  [∀ i, WeaklyLocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)]
  [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
  {S : ι → Type*} [∀ i, SetLike (S i) (G i)] [∀ i, SubgroupClass (S i) (G i)]

omit [Countable ι] [∀ i, SecondCountableTopology (G i)] in
@[to_additive]
private theorem isCompact_eventually_of_measure_eq_one_of_group (B : ∀ i, S i)
    (hBopen : ∀ i, IsOpen (B i : Set (G i))) (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)) :=
  hμ.mono fun i hi ↦ by
    have hne : μ i (B i) ≠ ∞ := by simp [hi]
    exact OpenSubgroup.isCompact_of_measure_ne_top ⟨Subgroup.ofClass (B i), hBopen i⟩ (μ i) hne

omit [Countable ι] [∀ i, SecondCountableTopology (G i)] in
@[to_additive]
private theorem locallyCompactSpace_restrictedProduct_of_group
    (B : ∀ i, S i) [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    LocallyCompactSpace (Πʳ i, [G i, B i]) := by
  have : WeaklyLocallyCompactSpace (Πʳ i, [G i, B i]) :=
    RestrictedProduct.weaklyLocallyCompactSpace_of_cofinite hBopen.out
      (isCompact_eventually_of_measure_eq_one_of_group B hBopen.out μ hμ)
  infer_instance

omit [Countable ι] [∀ i, WeaklyLocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)]
  [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)] in
@[to_additive]
private theorem isTopologicalGroup_levelProduct (B : ∀ i, S i) (F : Finset ι) :
    IsTopologicalGroup ((∀ i : F, G i.1) × (∀ j : {i // i ∉ F}, B j.1)) := by
  have (j : {i // i ∉ F}) : IsTopologicalGroup (B j.1) :=
    IsInducing.subtypeVal.isTopologicalGroup (SubgroupClass.subtype (B j.1))
  infer_instance

omit [∀ i, Group (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, WeaklyLocallyCompactSpace (G i)]
  [∀ i, SubgroupClass (S i) (G i)] in
private theorem borelSpace_levelProduct (B : ∀ i, S i) (F : Finset ι) :
    SecondCountableTopology ((∀ i : F, G i.1) × (∀ j : {i // i ∉ F}, B j.1)) ∧
      BorelSpace ((∀ i : F, G i.1) × (∀ j : {i // i ∉ F}, B j.1)) := by
  have (j : {i // i ∉ F}) : SecondCountableTopology (B j.1) :=
    TopologicalSpace.secondCountableTopology_induced (B j.1) (G j.1) Subtype.val
  exact ⟨inferInstance, inferInstance⟩

omit [Countable ι] [∀ i, SecondCountableTopology (G i)] in
@[to_additive]
private theorem locallyCompactSpace_levelProduct_of_group (B : ∀ i, S i)
    (hBopen : ∀ i, IsOpen (B i : Set (G i))) (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    {F : Finset ι} (hF : ∀ i ∉ F, μ i (B i) = 1) :
    LocallyCompactSpace ((∀ i : F, G i.1) × (∀ j : {i // i ∉ F}, B j.1)) := by
  have (j : {i // i ∉ F}) : CompactSpace (B j.1) :=
    isCompact_iff_compactSpace.mp <| by
      have hne : μ j.1 (B j.1) ≠ ∞ := by simp [hF j.1 j.2]
      exact OpenSubgroup.isCompact_of_measure_ne_top ⟨Subgroup.ofClass (B j.1), hBopen j.1⟩
        (μ j.1) hne
  infer_instance

omit [∀ i, WeaklyLocallyCompactSpace (G i)] in
@[to_additive]
private theorem isHaarMeasure_comap_restrictedProductLevelInclusion
    (B : ∀ i, S i) [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (ν : Measure (Πʳ i, [G i, B i])) [ν.IsHaarMeasure] (F : Finset ι) :
    (ν.comap (restrictedProductLevelInclusion B F)).IsHaarMeasure := by
  have : IsTopologicalGroup ((∀ i : F, G i.1) × (∀ j : {i // i ∉ F}, B j.1)) :=
    isTopologicalGroup_levelProduct B F
  obtain ⟨_, _⟩ := borelSpace_levelProduct B F
  have hemb := measurableEmbedding_restrictedProductLevelInclusion B F fun i _ ↦ hBopen.out i
  have hopen := isOpenEmbedding_restrictedProductLevelInclusion B F fun i _ ↦ hBopen.out i
  have : Measure.IsOpenPosMeasure (ν.comap (restrictedProductLevelInclusion B F)) :=
    Measure.IsOpenPosMeasure.comap ν hopen
  have : (ν.comap (restrictedProductLevelInclusion B F)).IsMulLeftInvariant :=
    Measure.isMulLeftInvariant_comap ν (restrictedProductLevelInclusion B F)
  have : IsFiniteMeasureOnCompacts (ν.comap (restrictedProductLevelInclusion B F)) :=
    ⟨fun K hK ↦ by
      rw [hemb.comap_apply]
      exact (hK.image hopen.continuous).measure_lt_top⟩
  exact { .. }

open Classical in
/-- **Restricted product of Haar measures.** Given local Haar measures `μ i` on second-countable
weakly locally compact topological groups `G i` and open subgroups `B i`, `restrictedHaar B μ` is
the Haar measure on `Πʳ i, [G i, B i]` normalized so that its pullback to the open level subgroup
outside `hμ.toFinset` coincides with `restrictedProductLevelMeasure` whenever `μ i (B i) = 1`
cofinitely (and `0` otherwise). -/
@[to_additive
  /-- **Restricted product of additive Haar measures.** Given local additive Haar measures `μ i` on
  second-countable weakly locally compact topological additive groups `G i` and open additive
  subgroups `B i`, `restrictedAddHaar B μ` is the additive Haar measure on `Πʳ i, [G i, B i]`
  normalized so that its pullback to the open level subgroup outside `hμ.toFinset` coincides with
  `restrictedProductLevelMeasure` whenever `μ i (B i) = 1` cofinitely (and `0` otherwise). -/]
def restrictedHaar (B : ∀ i, S i) [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure] :
    Measure (Πʳ i, [G i, B i]) :=
  if hμ : ∀ᶠ i in cofinite, μ i (B i) = 1 then
    letI : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
      locallyCompactSpace_restrictedProduct_of_group B μ hμ
    let F₀ : Finset ι := hμ.toFinset
    let ν₀ : Measure (Πʳ i, [G i, B i]) := Measure.haar
    haveI : IsTopologicalGroup ((∀ i : F₀, G i.1) × (∀ j : {i // i ∉ F₀}, B j.1)) :=
      isTopologicalGroup_levelProduct B F₀
    haveI : SecondCountableTopology ((∀ i : F₀, G i.1) × (∀ j : {i // i ∉ F₀}, B j.1)) :=
      (borelSpace_levelProduct B F₀).1
    haveI : BorelSpace ((∀ i : F₀, G i.1) × (∀ j : {i // i ∉ F₀}, B j.1)) :=
      (borelSpace_levelProduct B F₀).2
    haveI : (ν₀.comap (restrictedProductLevelInclusion B F₀)).IsHaarMeasure :=
      isHaarMeasure_comap_restrictedProductLevelInclusion B ν₀ F₀
    haveI : (restrictedProductLevelMeasure B μ F₀).IsHaarMeasure :=
      isHaarMeasure_restrictedProductLevelMeasure B μ (fun i _ ↦ hBopen.out i) fun _ hi ↦
        by_contra fun hne ↦ hi (hμ.mem_toFinset.mpr hne)
    Measure.haarScalarFactor (restrictedProductLevelMeasure B μ F₀)
      (ν₀.comap (restrictedProductLevelInclusion B F₀)) • ν₀
  else 0

/-- When `μ i (B i) = 1` fails to hold cofinitely, `restrictedHaar B μ` takes the junk value `0`. -/
@[to_additive (attr := simp)
  /-- When `μ i (B i) = 1` fails to hold cofinitely, `restrictedAddHaar B μ` takes the junk value
  `0`. -/]
theorem restrictedHaar_of_not_eventually (B : ∀ i, S i)
    [Fact (∀ i, IsOpen (B i : Set (G i)))]
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (h : ¬ ∀ᶠ i in cofinite, μ i (B i) = 1) :
    restrictedHaar B μ = 0 := by
  simp [restrictedHaar, h]

/-- `restrictedHaar B μ` is a Haar measure on `Πʳ i, [G i, B i]` whenever `μ i (B i) = 1` for all
but finitely many `i`. -/
@[to_additive
  /-- `restrictedAddHaar B μ` is an additive Haar measure on `Πʳ i, [G i, B i]` whenever
  `μ i (B i) = 1` for all but finitely many `i`. -/]
theorem isHaarMeasure_restrictedHaar (B : ∀ i, S i)
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    (restrictedHaar B μ).IsHaarMeasure := by
  classical
  have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    locallyCompactSpace_restrictedProduct_of_group B μ hμ
  let F₀ : Finset ι := hμ.toFinset
  have hF₀ : ∀ i ∉ F₀, μ i (B i) = 1 := fun _ hi ↦
    by_contra fun hne ↦ hi (hμ.mem_toFinset.mpr hne)
  let ν₀ : Measure (Πʳ i, [G i, B i]) := Measure.haar
  have : IsTopologicalGroup ((∀ i : F₀, G i.1) × (∀ j : {i // i ∉ F₀}, B j.1)) :=
    isTopologicalGroup_levelProduct B F₀
  obtain ⟨_, _⟩ := borelSpace_levelProduct B F₀
  have : (ν₀.comap (restrictedProductLevelInclusion B F₀)).IsHaarMeasure :=
    isHaarMeasure_comap_restrictedProductLevelInclusion B ν₀ F₀
  have : (restrictedProductLevelMeasure B μ F₀).IsHaarMeasure :=
    isHaarMeasure_restrictedProductLevelMeasure B μ (fun i _ ↦ hBopen.out i) hF₀
  have : LocallyCompactSpace ((∀ i : F₀, G i.1) × (∀ j : {i // i ∉ F₀}, B j.1)) :=
    locallyCompactSpace_levelProduct_of_group B hBopen.out μ hF₀
  have hc : 0 < Measure.haarScalarFactor (restrictedProductLevelMeasure B μ F₀)
      (ν₀.comap (restrictedProductLevelInclusion B F₀)) :=
    Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  simp only [restrictedHaar, hμ, ↓reduceDIte, ENNReal.smul_def]
  exact Measure.IsHaarMeasure.smul ν₀ (ENNReal.coe_ne_zero.mpr hc.ne') ENNReal.coe_ne_top

@[to_additive]
private theorem comap_restrictedProductLevelInclusion_restrictedHaar_toFinset
    (B : ∀ i, S i) [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    (restrictedHaar B μ).comap (restrictedProductLevelInclusion B hμ.toFinset) =
      restrictedProductLevelMeasure B μ hμ.toFinset := by
  classical
  have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    locallyCompactSpace_restrictedProduct_of_group B μ hμ
  set F₀ : Finset ι := hμ.toFinset
  have hF₀ : ∀ i ∉ F₀, μ i (B i) = 1 := fun _ hi ↦
    by_contra fun hne ↦ hi (hμ.mem_toFinset.mpr hne)
  let ν₀ : Measure (Πʳ i, [G i, B i]) := Measure.haar
  have : IsTopologicalGroup ((∀ i : F₀, G i.1) × (∀ j : {i // i ∉ F₀}, B j.1)) :=
    isTopologicalGroup_levelProduct B F₀
  obtain ⟨_, _⟩ := borelSpace_levelProduct B F₀
  have : (ν₀.comap (restrictedProductLevelInclusion B F₀)).IsHaarMeasure :=
    isHaarMeasure_comap_restrictedProductLevelInclusion B ν₀ F₀
  have : (restrictedProductLevelMeasure B μ F₀).IsHaarMeasure :=
    isHaarMeasure_restrictedProductLevelMeasure B μ (fun i _ ↦ hBopen.out i) hF₀
  have : LocallyCompactSpace ((∀ i : F₀, G i.1) × (∀ j : {i // i ∉ F₀}, B j.1)) :=
    locallyCompactSpace_levelProduct_of_group B hBopen.out μ hF₀
  have hemb := measurableEmbedding_restrictedProductLevelInclusion B F₀ fun i _ ↦ hBopen.out i
  simp only [restrictedHaar, hμ, ↓reduceDIte]
  ext E _
  rw [hemb.comap_apply, smul_apply, ← hemb.comap_apply, ← smul_apply,
    ← Measure.isMulLeftInvariant_eq_smul (restrictedProductLevelMeasure B μ F₀)
      (ν₀.comap (restrictedProductLevelInclusion B F₀))]

omit [Countable ι] [∀ i, IsTopologicalGroup (G i)] [∀ i, SecondCountableTopology (G i)]
  [∀ i, BorelSpace (G i)] in
@[to_additive]
private theorem exists_open_identity_box_of_group (B : ∀ i, S i)
    (hBopen : ∀ i, IsOpen (B i : Set (G i))) (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (T : Finset ι) :
    ∃ C : ∀ i, Set (G i), (∀ i, IsOpen (C i)) ∧ (∀ i, C i ⊆ B i) ∧ (∀ i ∉ T, C i = B i) ∧
      (∏ i ∈ T, μ i (C i)) ≠ 0 ∧ (∏ i ∈ T, μ i (C i)) ≠ ∞ := by
  classical
  choose K hKcomp hKnhds using fun i ↦ exists_compact_mem_nhds (1 : G i)
  refine ⟨fun i ↦ if i ∈ T then interior (K i) ∩ (B i : Set (G i)) else (B i : Set (G i)),
    fun i ↦ ?_, fun i ↦ ?_, fun i hi ↦ by simp [hi], ?_, ?_⟩
  · by_cases hi : i ∈ T <;> simp only [hi, ↓reduceIte, isOpen_interior.inter (hBopen i), hBopen i]
  · by_cases hi : i ∈ T <;> simp [hi]
  · refine (CanonicallyOrderedAdd.prod_pos.mpr fun i hi ↦ ?_).ne'
    simp only [hi, ↓reduceIte]
    exact (isOpen_interior.inter (hBopen i)).measure_pos (μ i)
      ⟨1, mem_interior_iff_mem_nhds.mpr (hKnhds i), one_mem _⟩
  · refine (ENNReal.prod_lt_top fun i hi ↦ ?_).ne
    simp only [hi, ↓reduceIte]
    exact (measure_mono (inter_subset_left.trans interior_subset)).trans_lt
      (hKcomp i).measure_lt_top

/-- **Level pullback formula.** For *every* finite index set `F : Finset ι` outside which
`μ i (B i) = 1`, pulling `restrictedHaar B μ` back along `restrictedProductLevelInclusion B F`
recovers the level product measure `restrictedProductLevelMeasure B μ F`. -/
@[to_additive comap_addRestrictedProductLevelInclusion_restrictedAddHaar
  /-- **Level pullback formula (additive).** For *every* finite index set `F : Finset ι` outside
  which `μ i (B i) = 1`, pulling `restrictedAddHaar B μ` back along
  `addRestrictedProductLevelInclusion B F` recovers `restrictedProductLevelMeasure B μ F`. -/]
theorem comap_restrictedProductLevelInclusion_restrictedHaar (B : ∀ i, S i)
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    {F : Finset ι} (hF : ∀ i ∉ F, μ i (B i) = 1) :
    (restrictedHaar B μ).comap (restrictedProductLevelInclusion B F) =
      restrictedProductLevelMeasure B μ F := by
  classical
  have hμ : ∀ᶠ i in cofinite, μ i (B i) = 1 := F.eventually_cofinite_notMem.mono hF
  set F₀ : Finset ι := hμ.toFinset
  have hF₀ : ∀ i ∉ F₀, μ i (B i) = 1 := fun _ hi ↦ by_contra fun h ↦ hi (hμ.mem_toFinset.mpr h)
  have : (restrictedHaar B μ).IsHaarMeasure := isHaarMeasure_restrictedHaar B μ hμ
  have : IsTopologicalGroup ((∀ i : F, G i.1) × (∀ j : {i // i ∉ F}, B j.1)) :=
    isTopologicalGroup_levelProduct B F
  obtain ⟨_, _⟩ := borelSpace_levelProduct B F
  set μ₁ := (restrictedHaar B μ).comap (restrictedProductLevelInclusion B F)
  set μ₂ := restrictedProductLevelMeasure B μ F
  have : μ₁.IsHaarMeasure :=
    isHaarMeasure_comap_restrictedProductLevelInclusion B (restrictedHaar B μ) F
  have : μ₂.IsHaarMeasure :=
    isHaarMeasure_restrictedProductLevelMeasure B μ (fun i _ ↦ hBopen.out i) hF
  have : LocallyCompactSpace ((∀ i : F, G i.1) × (∀ j : {i // i ∉ F}, B j.1)) :=
    locallyCompactSpace_levelProduct_of_group B hBopen.out μ hF
  obtain ⟨C, hCopen, hCB, hCT, hpos, htop⟩ :=
    exists_open_identity_box_of_group B hBopen.out μ (F₀ ∪ F)
  let s : Set (Πʳ i, [G i, B i]) := {x | ∀ i, x i ∈ C i}
  have hemb₀ := measurableEmbedding_restrictedProductLevelInclusion B F₀ fun i _ ↦ hBopen.out i
  have hemb := measurableEmbedding_restrictedProductLevelInclusion B F fun i _ ↦ hBopen.out i
  have hsub (E : Finset ι) : s ⊆ range (restrictedProductLevelInclusion B E) := by
    rw [range_restrictedProductLevelInclusion]
    exact fun _ hx i _ ↦ hCB i (hx i)
  have hbox : restrictedHaar B μ s = ∏ i ∈ F₀ ∪ F, μ i (C i) := by
    rw [← image_preimage_eq_of_subset (hsub F₀), ← hemb₀.comap_apply,
      comap_restrictedProductLevelInclusion_restrictedHaar_toFinset B μ hμ]
    exact restrictedProductLevelMeasure_preimage_setOf_forall_mem B μ
      (fun i _ ↦ (hBopen.out i).measurableSet) hF₀ Finset.subset_union_left
      (fun i ↦ (hCopen i).measurableSet) (fun i _ ↦ hCB i) hCT
  have hm₁ : μ₁ (restrictedProductLevelInclusion B F ⁻¹' s) = ∏ i ∈ F₀ ∪ F, μ i (C i) := by
    rw [hemb.comap_apply, image_preimage_eq_of_subset (hsub F), hbox]
  have hm₂ : μ₂ (restrictedProductLevelInclusion B F ⁻¹' s) = ∏ i ∈ F₀ ∪ F, μ i (C i) :=
    restrictedProductLevelMeasure_preimage_setOf_forall_mem B μ
      (fun i _ ↦ (hBopen.out i).measurableSet) hF Finset.subset_union_right
      (fun i ↦ (hCopen i).measurableSet) (fun i _ ↦ hCB i) hCT
  have hc_eq := Measure.isMulLeftInvariant_eq_smul μ₁ μ₂
  have heval := congrArg (fun m : Measure _ ↦ m (restrictedProductLevelInclusion B F ⁻¹' s)) hc_eq
  simp only [smul_apply, ENNReal.smul_def, smul_eq_mul, hm₁, hm₂] at heval
  have hc1 : (Measure.haarScalarFactor μ₁ μ₂ : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj hpos htop).mp (by simpa only [one_mul] using heval.symm)
  rw [hc_eq, ENNReal.smul_def, hc1, one_smul]

/-- Pushing `restrictedProductLevelMeasure B μ F` forward along
`restrictedProductLevelInclusion B F` restricts `restrictedHaar B μ` to
`{x | ∀ i ∉ F, x i ∈ B i}`. -/
@[to_additive map_addRestrictedProductLevelInclusion_levelMeasure
  /-- Pushing `restrictedProductLevelMeasure B μ F` forward along
  `addRestrictedProductLevelInclusion B F` restricts `restrictedAddHaar B μ` to
  `{x | ∀ i ∉ F, x i ∈ B i}`. -/]
theorem map_restrictedProductLevelInclusion_levelMeasure (B : ∀ i, S i)
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    {F : Finset ι} (hF : ∀ i ∉ F, μ i (B i) = 1) :
    (restrictedProductLevelMeasure B μ F).map (restrictedProductLevelInclusion B F) =
      (restrictedHaar B μ).restrict {x : Πʳ i, [G i, B i] | ∀ i ∉ F, x i ∈ B i} := by
  have hemb := measurableEmbedding_restrictedProductLevelInclusion B F fun i _ ↦ hBopen.out i
  rw [← comap_restrictedProductLevelInclusion_restrictedHaar B μ hF, hemb.map_comap,
    range_restrictedProductLevelInclusion]

/-- **Lower Lebesgue integral over an open level subgroup.** For every finite `F : Finset ι` with
`∀ i ∉ F, μ i (B i) = 1`, integrating over `{x | ∀ i ∉ F, x i ∈ B i}` against `restrictedHaar B μ`
reduces to integrating against the product measure `restrictedProductLevelMeasure B μ F`. -/
@[to_additive
  /-- **Lower Lebesgue integral over an open additive level subgroup.** For every finite
  `F : Finset ι` with `∀ i ∉ F, μ i (B i) = 1`, integrating over `{x | ∀ i ∉ F, x i ∈ B i}` against
  `restrictedAddHaar B μ` reduces to integrating against `restrictedProductLevelMeasure B μ F`. -/]
theorem setLIntegral_restrictedHaar_setOf_forall_notMem_eq (B : ∀ i, S i)
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    {F : Finset ι} (hF : ∀ i ∉ F, μ i (B i) = 1) (f : (Πʳ i, [G i, B i]) → ℝ≥0∞) :
    ∫⁻ x in {x : Πʳ i, [G i, B i] | ∀ i ∉ F, x i ∈ B i}, f x ∂(restrictedHaar B μ) =
      ∫⁻ p, f (restrictedProductLevelInclusion B F p) ∂(restrictedProductLevelMeasure B μ F) := by
  have hemb := measurableEmbedding_restrictedProductLevelInclusion B F fun i _ ↦ hBopen.out i
  rw [← map_restrictedProductLevelInclusion_levelMeasure B μ hF, hemb.lintegral_map]

/-- **Bochner integral over an open level subgroup.** For every finite `F : Finset ι` with
`∀ i ∉ F, μ i (B i) = 1`, the Bochner integral over `{x | ∀ i ∉ F, x i ∈ B i}` against
`restrictedHaar B μ` reduces to the product integral against
`restrictedProductLevelMeasure B μ F`. -/
@[to_additive
  /-- **Bochner integral over an open additive level subgroup.** For every finite `F : Finset ι`
  with `∀ i ∉ F, μ i (B i) = 1`, the Bochner integral over `{x | ∀ i ∉ F, x i ∈ B i}` against
  `restrictedAddHaar B μ` reduces to the product integral against
  `restrictedProductLevelMeasure B μ F`. -/]
theorem setIntegral_restrictedHaar_setOf_forall_notMem_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (B : ∀ i, S i) [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    {F : Finset ι} (hF : ∀ i ∉ F, μ i (B i) = 1) (f : (Πʳ i, [G i, B i]) → E) :
    ∫ x in {x : Πʳ i, [G i, B i] | ∀ i ∉ F, x i ∈ B i}, f x ∂(restrictedHaar B μ) =
      ∫ p, f (restrictedProductLevelInclusion B F p) ∂(restrictedProductLevelMeasure B μ F) := by
  have hemb := measurableEmbedding_restrictedProductLevelInclusion B F fun i _ ↦ hBopen.out i
  rw [← map_restrictedProductLevelInclusion_levelMeasure B μ hF, hemb.integral_map]

/-- **Box evaluation formula for `restrictedHaar`.** Whenever `μ i (B i) = 1` cofinitely, every
`C i` is measurable, and `C i = B i` cofinitely, the `restrictedHaar B μ` measure of the box
`{x | ∀ i, x i ∈ C i}` is the finite product `∏ᶠ i, μ i (C i)`. -/
@[to_additive
  /-- **Box evaluation formula for `restrictedAddHaar`.** Whenever `μ i (B i) = 1` cofinitely, every
  `C i` is measurable, and `C i = B i` cofinitely, the `restrictedAddHaar B μ` measure of
  `{x | ∀ i, x i ∈ C i}` is `∏ᶠ i, μ i (C i)`. -/]
theorem restrictedHaar_setOf_forall_mem (B : ∀ i, S i)
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) {C : ∀ i, Set (G i)}
    (hC : ∀ i, MeasurableSet (C i)) (hCB : ∀ᶠ i in cofinite, C i = B i) :
    restrictedHaar B μ {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i) := by
  classical
  let F : Finset ι := hμ.toFinset ∪ hCB.toFinset
  have hFμ : ∀ i ∉ F, μ i (B i) = 1 := fun i hi ↦
    by_contra fun hne ↦ hi (Finset.mem_union_left _ (hμ.mem_toFinset.mpr hne))
  have hFC : ∀ i ∉ F, C i = B i := fun i hi ↦
    by_contra fun hne ↦ hi (Finset.mem_union_right _ (hCB.mem_toFinset.mpr hne))
  have hemb := measurableEmbedding_restrictedProductLevelInclusion B F fun i _ ↦ hBopen.out i
  have hsub : {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ C i} ⊆
      range (restrictedProductLevelInclusion B F) := by
    rw [range_restrictedProductLevelInclusion]
    intro x hx i hi
    have hxi : x i ∈ C i := hx i
    rwa [hFC i hi] at hxi
  rw [← image_preimage_eq_of_subset hsub, ← hemb.comap_apply,
    comap_restrictedProductLevelInclusion_restrictedHaar B μ hFμ,
    restrictedProductLevelMeasure_preimage_setOf_forall_mem B μ
      (fun i _ ↦ (hBopen.out i).measurableSet) hFμ Subset.rfl hC
      (fun i hi ↦ (hFC i hi).subset) hFC,
    finprod_eq_prod_of_mulSupport_subset _ fun i hi ↦ by
      by_contra hiF
      rw [mem_mulSupport] at hi
      exact hi (by rw [hFC i hiF, hFμ i hiF])]

/-- The `restrictedHaar B μ` mass of the everywhere-integral open compact subgroup
`{x | ∀ i, x i ∈ B i}` is `∏ᶠ i, μ i (B i)`. -/
@[to_additive
  /-- The `restrictedAddHaar B μ` mass of `{x | ∀ i, x i ∈ B i}` is `∏ᶠ i, μ i (B i)`. -/]
theorem restrictedHaar_setOf_forall_mem_self (B : ∀ i, S i)
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    restrictedHaar B μ {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ B i} = ∏ᶠ i, μ i (B i) :=
  restrictedHaar_setOf_forall_mem B μ hμ (fun i ↦ (hBopen.out i).measurableSet)
    (.of_forall fun _ ↦ rfl)

/-- When `μ i (B i) = 1` at *every* index `i`, `{x | ∀ i, x i ∈ B i}` has `restrictedHaar B μ`
measure `1`. -/
@[to_additive
  /-- When `μ i (B i) = 1` at *every* index `i`, `{x | ∀ i, x i ∈ B i}` has `restrictedAddHaar B μ`
  measure `1`. -/]
theorem restrictedHaar_setOf_forall_mem_self_eq_one (B : ∀ i, S i)
    [Fact (∀ i, IsOpen (B i : Set (G i)))]
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ i, μ i (B i) = 1) :
    restrictedHaar B μ {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ B i} = 1 := by
  rw [restrictedHaar_setOf_forall_mem_self B μ (.of_forall hμ)]
  simp [hμ]

/-- **Uniqueness from open cofinite boxes.** Any Borel measure on `Πʳ i, [G i, B i]` assigning mass
`∏ᶠ i, μ i (C i)` to every open cofinite box `{x | ∀ i, x i ∈ C i}` (`C i = B i` cofinitely) equals
`restrictedHaar B μ`. -/
@[to_additive
  /-- **Uniqueness from open cofinite boxes (additive).** Any Borel measure on `Πʳ i, [G i, B i]`
  assigning mass `∏ᶠ i, μ i (C i)` to every open cofinite box `{x | ∀ i, x i ∈ C i}` (`C i = B i`
  cofinitely) equals `restrictedAddHaar B μ`. -/]
theorem eq_restrictedHaar_of_forall_openBox (B : ∀ i, S i)
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) {ν : Measure (Πʳ i, [G i, B i])}
    (hν : ∀ C : ∀ i, Set (G i), (∀ i, IsOpen (C i)) → (∀ᶠ i in cofinite, C i = B i) →
      ν {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i)) :
    ν = restrictedHaar B μ := by
  have : (restrictedHaar B μ).IsHaarMeasure := isHaarMeasure_restrictedHaar B μ hμ
  exact (ext_of_openBox_restrictedProduct hBopen.out
    (isCompact_eventually_of_measure_eq_one_of_group B hBopen.out μ hμ) fun C hCo hCB ↦
      (restrictedHaar_setOf_forall_mem B μ hμ (fun i ↦ (hCo i).measurableSet) hCB).trans
        (hν C hCo hCB).symm).symm

/-- **Uniqueness from measurable cofinite boxes.** Any Borel measure on `Πʳ i, [G i, B i]`
assigning mass `∏ᶠ i, μ i (C i)` to every measurable cofinite box `{x | ∀ i, x i ∈ C i}` equals
`restrictedHaar B μ`. -/
@[to_additive
  /-- **Uniqueness from measurable cofinite boxes (additive).** Any Borel measure on
  `Πʳ i, [G i, B i]` assigning mass `∏ᶠ i, μ i (C i)` to every measurable cofinite box equals
  `restrictedAddHaar B μ`. -/]
theorem eq_restrictedHaar_of_forall_box (B : ∀ i, S i)
    [Fact (∀ i, IsOpen (B i : Set (G i)))]
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) {ν : Measure (Πʳ i, [G i, B i])}
    (hν : ∀ C : ∀ i, Set (G i), (∀ i, MeasurableSet (C i)) → (∀ᶠ i in cofinite, C i = B i) →
      ν {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i)) :
    ν = restrictedHaar B μ :=
  eq_restrictedHaar_of_forall_openBox B μ hμ fun C hCo ↦ hν C fun i ↦ (hCo i).measurableSet

/-- **Existence and uniqueness of the restricted product of Haar measures.** Over a countable index
type, let `(G i)` be second-countable weakly locally compact topological groups with Borel Haar
measures `μ i` and open subgroups `B i` satisfying `μ i (B i) = 1` for all but finitely many `i`.
Then there exists a unique Borel Haar measure `ν` on `Πʳ i, [G i, B i]` such that
`ν {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i)` for every family of Borel sets `C i` with `C i = B i`
cofinitely. -/
@[to_additive
  /-- **Existence and uniqueness of the restricted product of additive Haar measures.** Over a
  countable index type, let `(G i)` be second-countable weakly locally compact topological additive
  groups with Borel additive Haar measures `μ i` and open additive subgroups `B i` satisfying
  `μ i (B i) = 1` for all but finitely many `i`. Then there exists a unique Borel additive Haar
  measure `ν` on `Πʳ i, [G i, B i]` such that `ν {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i)` for every
  family of Borel sets `C i` with `C i = B i` cofinitely. -/]
theorem exists_unique_restrictedHaar (B : ∀ i, S i)
    [Fact (∀ i, IsOpen (B i : Set (G i)))]
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    ∃! ν : Measure (Πʳ i, [G i, B i]), ν.IsHaarMeasure ∧
      ∀ C : ∀ i, Set (G i), (∀ i, MeasurableSet (C i)) →
        (∀ᶠ i in cofinite, C i = B i) →
        ν {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i) :=
  ⟨restrictedHaar B μ,
    ⟨isHaarMeasure_restrictedHaar B μ hμ,
      fun _ hCm hCB ↦ restrictedHaar_setOf_forall_mem B μ hμ hCm hCB⟩,
    fun _ ⟨_, hν⟩ ↦ eq_restrictedHaar_of_forall_box B μ hμ hν⟩

/-- **Unimodularity inheritance:** if every local Haar measure `μ i` is right-invariant, then
`restrictedHaar B μ` is right-invariant (including in the junk case `restrictedHaar B μ = 0`). -/
@[to_additive
  /-- If every local additive Haar measure `μ i` is right-invariant, then `restrictedAddHaar B μ`
  is right-invariant. -/]
theorem isMulRightInvariant_restrictedHaar (B : ∀ i, S i)
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure] [∀ i, (μ i).IsMulRightInvariant] :
    (restrictedHaar B μ).IsMulRightInvariant := by
  by_cases hμ : ∀ᶠ i in cofinite, μ i (B i) = 1
  · refine ⟨fun g ↦ eq_restrictedHaar_of_forall_box B μ hμ fun C hCm hCB ↦ ?_⟩
    rw [Measure.map_apply (measurable_mul_const g)
      (measurableSet_setOf_forall_mem_restrictedProduct hBopen.out hCm hCB)]
    have hpre : (· * g) ⁻¹' {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ C i} =
        {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ (· * g i) ⁻¹' C i} := by
      ext x
      rfl
    have hCB' : ∀ᶠ i in cofinite, (· * g i) ⁻¹' C i = B i :=
      (hCB.and g.2).mono fun i ⟨hiC, hig⟩ ↦ by
        have hig' : g i ∈ B i := hig
        ext y
        simp only [mem_preimage, hiC, SetLike.mem_coe, mul_mem_cancel_right hig']
    rw [hpre, restrictedHaar_setOf_forall_mem B μ hμ
      (fun i ↦ (hCm i).preimage (measurable_mul_const (g i))) hCB']
    simp_rw [measure_preimage_mul_right]
  · rw [restrictedHaar_of_not_eventually B μ hμ]
    exact ⟨fun _ ↦ Measure.map_zero _⟩

/-- **Inversion invariance inheritance:** if every local Haar measure `μ i` is inversion-invariant,
then `restrictedHaar B μ` is inversion-invariant. -/
@[to_additive
  /-- If every local additive Haar measure `μ i` is negation-invariant, then
  `restrictedAddHaar B μ` is negation-invariant. -/]
theorem isInvInvariant_restrictedHaar (B : ∀ i, S i)
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure] [∀ i, (μ i).IsInvInvariant] :
    (restrictedHaar B μ).IsInvInvariant := by
  by_cases hμ : ∀ᶠ i in cofinite, μ i (B i) = 1
  · refine ⟨eq_restrictedHaar_of_forall_box B μ hμ fun C hCm hCB ↦ ?_⟩
    rw [Measure.inv_apply]
    have hpre : ({x : Πʳ i, [G i, B i] | ∀ i, x i ∈ C i})⁻¹ =
        {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ Inv.inv ⁻¹' C i} := by
      ext x
      rfl
    have hCB' : ∀ᶠ i in cofinite, Inv.inv ⁻¹' C i = (B i : Set (G i)) :=
      hCB.mono fun i hiC ↦ by
        ext y
        simp only [mem_preimage, hiC, SetLike.mem_coe, inv_mem_iff]
    rw [hpre, restrictedHaar_setOf_forall_mem B μ hμ
      (fun i ↦ (hCm i).preimage measurable_inv) hCB']
    simp_rw [(μ _).measure_preimage_inv]
  · rw [restrictedHaar_of_not_eventually B μ hμ]
    exact ⟨by simp [Measure.inv]⟩

/-- **Finite scalar rescaling of `restrictedHaar`.** Rescaling the local Haar measures `μ i` by
nonzero positive reals `c i : ℝ≥0` with `c i = 1` cofinitely rescales `restrictedHaar B μ` by
`∏ᶠ i, (c i : ℝ≥0∞)`. -/
@[to_additive
  /-- **Finite scalar rescaling of `restrictedAddHaar`.** Rescaling the local additive Haar measures
  `μ i` by nonzero `c i : ℝ≥0` with `c i = 1` cofinitely rescales `restrictedAddHaar B μ` by
  `∏ᶠ i, (c i : ℝ≥0∞)`. -/]
theorem restrictedHaar_smul (B : ∀ i, S i) [Fact (∀ i, IsOpen (B i : Set (G i)))]
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    {c : ι → ℝ≥0} (hc0 : ∀ i, c i ≠ 0) (hc1 : ∀ᶠ i in cofinite, c i = 1)
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    haveI (i : ι) : (c i • μ i).IsHaarMeasure :=
      Measure.IsHaarMeasure.smul (μ i) (ENNReal.coe_ne_zero.mpr (hc0 i)) ENNReal.coe_ne_top
    restrictedHaar B (fun i ↦ c i • μ i) = (∏ᶠ i, (c i : ℝ≥0∞)) • restrictedHaar B μ := by
  classical
  have (i : ι) : (c i • μ i).IsHaarMeasure :=
    Measure.IsHaarMeasure.smul (μ i) (ENNReal.coe_ne_zero.mpr (hc0 i)) ENNReal.coe_ne_top
  have hcμ : ∀ᶠ i in cofinite, (c i • μ i) (B i) = 1 :=
    (hc1.and hμ).mono fun i ⟨hci, hμi⟩ ↦ by simp [hci, hμi]
  refine (eq_restrictedHaar_of_forall_box B (fun i ↦ c i • μ i) hcμ fun C hCm hCB ↦ ?_).symm
  rw [smul_apply, smul_eq_mul, restrictedHaar_setOf_forall_mem B μ hμ hCm hCB]
  let T : Finset ι := hc1.toFinset ∪ hCB.toFinset ∪ hμ.toFinset
  have hT_c : mulSupport (fun i ↦ (c i : ℝ≥0∞)) ⊆ T := fun i hi ↦ by
    by_contra hiT
    have : c i = 1 := by_contra fun hne ↦
      hiT (Finset.mem_union_left _ (Finset.mem_union_left _ (hc1.mem_toFinset.mpr hne)))
    exact mem_mulSupport.mp hi (by simp [this])
  have hT_μ : mulSupport (fun i ↦ μ i (C i)) ⊆ T := fun i hi ↦ by
    by_contra hiT
    have hiC : C i = B i := by_contra fun hne ↦
      hiT (Finset.mem_union_left _ (Finset.mem_union_right _ (hCB.mem_toFinset.mpr hne)))
    have hiμ : μ i (B i) = 1 := by_contra fun hne ↦
      hiT (Finset.mem_union_right _ (hμ.mem_toFinset.mpr hne))
    exact mem_mulSupport.mp hi (by rw [hiC, hiμ])
  have hT_cμ : mulSupport (fun i ↦ (c i • μ i) (C i)) ⊆ T := fun i hi ↦ by
    by_contra hiT
    have hci : c i = 1 := by_contra fun hne ↦
      hiT (Finset.mem_union_left _ (Finset.mem_union_left _ (hc1.mem_toFinset.mpr hne)))
    have hiμ : μ i (C i) = 1 := by_contra fun h ↦ hiT (hT_μ h)
    exact mem_mulSupport.mp hi (by simp [hci, hiμ])
  rw [finprod_eq_prod_of_mulSupport_subset _ hT_c,
    finprod_eq_prod_of_mulSupport_subset _ hT_μ,
    finprod_eq_prod_of_mulSupport_subset _ hT_cμ, ← Finset.prod_mul_distrib]
  rfl

end RestrictedHaar

section AwayDecomposition

@[to_additive]
private theorem preimage_awayDecomposition_symm_setOf_forall_mem_of_group
    {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]
    (U : ∀ i, Subgroup (G i)) (F : Finset ι) (C : ∀ i, Set (G i)) :
    (awayDecomposition (F : Set ι) F.finite_toSet U).symm ⁻¹'
        {x : Πʳ i, [G i, U i] | ∀ i, x i ∈ C i} =
      (univ.pi fun i : F ↦ C i.1) ×ˢ
        {z : Πʳ j : {i // i ∉ F}, [G j.1, U j.1] | ∀ j, z j ∈ C j.1} := by
  ext ⟨y, z⟩
  simp only [mem_preimage, mem_ofPred_eq, mem_prod, mem_univ_pi]
  refine ⟨fun h ↦ ⟨fun i ↦ ?_, fun j ↦ ?_⟩, fun ⟨hy, hz⟩ i ↦ ?_⟩
  · have hi := h i.1
    rwa [awayDecomposition_symm_apply_of_mem (F : Set ι) F.finite_toSet U (y, z) i.1 i.2] at hi
  · have hj := h j.1
    rwa [awayDecomposition_symm_apply_of_notMem (F : Set ι) F.finite_toSet U (y, z) j.1 j.2] at hj
  · by_cases hi : i ∈ F
    · simpa only [awayDecomposition_symm_apply_of_mem (F : Set ι) F.finite_toSet U (y, z) i hi]
        using hy ⟨i, hi⟩
    · simpa only [awayDecomposition_symm_apply_of_notMem (F : Set ι) F.finite_toSet U (y, z) i hi]
        using hz ⟨i, hi⟩

/-- **Finite-place decomposition of `restrictedHaar`.** Under `awayDecomposition` along any finite
set `F : Finset ι`, `restrictedHaar U μ` factors as the finite product measure `Measure.pi` on `F`
times the restricted Haar measure away from `F`. -/
@[to_additive map_addAwayDecomposition_restrictedAddHaar
  /-- **Finite-place decomposition of `restrictedAddHaar`.** Under `addAwayDecomposition` along any
  finite set `F : Finset ι`, `restrictedAddHaar U μ` factors as `Measure.pi` on `F` times the
  restricted additive Haar measure away from `F`. -/]
theorem map_awayDecomposition_restrictedHaar {ι : Type*} {G : ι → Type*} [Countable ι]
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    [∀ i, WeaklyLocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)]
    [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)] (U : ∀ i, Subgroup (G i))
    [hUopen : Fact (∀ i, IsOpen (U i : Set (G i)))]
    [MeasurableSpace (Πʳ i, [G i, U i])] [BorelSpace (Πʳ i, [G i, U i])]
    (F : Finset ι)
    [MeasurableSpace (Πʳ j : {i // i ∉ F}, [G j.1, U j.1])]
    [BorelSpace (Πʳ j : {i // i ∉ F}, [G j.1, U j.1])]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (U i) = 1) :
    haveI : Fact (∀ j : {i // i ∉ F}, IsOpen (U j.1 : Set (G j.1))) := ⟨fun j ↦ hUopen.out j.1⟩
    Measure.map (awayDecomposition (F : Set ι) F.finite_toSet U) (restrictedHaar U μ) =
      (Measure.pi fun i : F ↦ μ i.1).prod
        (restrictedHaar (fun j : {i // i ∉ F} ↦ U j.1) (fun j ↦ μ j.1)) := by
  classical
  have : Fact (∀ j : {i // i ∉ F}, IsOpen (U j.1 : Set (G j.1))) := ⟨fun j ↦ hUopen.out j.1⟩
  let e : (Πʳ i, [G i, U i]) ≃ₜ
      (∀ i : (F : Set ι), G i.1) × (Πʳ j : {i // i ∉ F}, [G j.1, U j.1]) :=
    { toEquiv := (awayDecomposition (F : Set ι) F.finite_toSet U).toEquiv
      continuous_toFun := continuous_awayDecomposition (F : Set ι) F.finite_toSet U
      continuous_invFun := continuous_awayDecomposition_symm (F : Set ι) F.finite_toSet U
        fun i _ ↦ hUopen.out i }
  have hμ' : ∀ᶠ j : {i // i ∉ F} in cofinite, μ j.1 (U j.1) = 1 :=
    Subtype.coe_injective.tendsto_cofinite.eventually hμ
  have : LocallyCompactSpace (Πʳ j : {i // i ∉ F}, [G j.1, U j.1]) :=
    locallyCompactSpace_restrictedProduct_of_group (fun j : {i // i ∉ F} ↦ U j.1)
      (fun j ↦ μ j.1) hμ'
  have : (restrictedHaar (fun j : {i // i ∉ F} ↦ U j.1) (fun j ↦ μ j.1)).IsHaarMeasure :=
    isHaarMeasure_restrictedHaar (fun j : {i // i ∉ F} ↦ U j.1) (fun j ↦ μ j.1) hμ'
  set η := (Measure.pi fun i : F ↦ μ i.1).prod
    (restrictedHaar (fun j : {i // i ∉ F} ↦ U j.1) (fun j ↦ μ j.1))
  have he : ⇑(awayDecomposition (F : Set ι) F.finite_toSet U) = ⇑e := rfl
  have he_symm : ⇑e.symm = ⇑(awayDecomposition (F : Set ι) F.finite_toSet U).symm := rfl
  suffices Measure.map e.symm η = restrictedHaar U μ by
    rw [← this, he]
    exact e.symm.toMeasurableEquiv.map_symm_map
  refine eq_restrictedHaar_of_forall_box U μ hμ fun C hCm hCB ↦ ?_
  have hCB' : ∀ᶠ j : {i // i ∉ F} in cofinite, C j.1 = U j.1 :=
    Subtype.coe_injective.tendsto_cofinite.eventually hCB
  rw [e.symm.measurableEmbedding.map_apply, he_symm,
    preimage_awayDecomposition_symm_setOf_forall_mem_of_group U F C,
    Measure.prod_prod, Measure.pi_pi,
    restrictedHaar_setOf_forall_mem _ _ hμ' (fun j ↦ hCm j.1) hCB']
  let T : Finset ι := F ∪ hCB.toFinset ∪ hμ.toFinset
  have hT : ∀ i ∉ T, μ i (C i) = 1 := fun i hiT ↦ by
    have hiC : C i = U i := by_contra fun hne ↦
      hiT (Finset.mem_union_left _ (Finset.mem_union_right _ (hCB.mem_toFinset.mpr hne)))
    have hiμ : μ i (U i) = 1 := by_contra fun hne ↦
      hiT (Finset.mem_union_right _ (hμ.mem_toFinset.mpr hne))
    rw [hiC, hiμ]
  rw [finprod_eq_prod_of_mulSupport_subset (fun j : {i // i ∉ F} ↦ μ j.1 (C j.1)) fun j hj ↦
      Finset.mem_coe.mpr <| Finset.mem_subtype.mpr <| by
        by_contra hjT
        exact mem_mulSupport.mp hj (hT j.1 hjT),
    finprod_eq_prod_of_mulSupport_subset (fun i ↦ μ i (C i)) fun i hi ↦ by
      by_contra hiT
      exact mem_mulSupport.mp hi (hT i hiT),
    Finset.prod_coe_sort F (fun i ↦ μ i (C i)),
    Finset.prod_subtype_eq_prod_filter (f := fun i ↦ μ i (C i)),
    Finset.filter_notMem_eq_sdiff, mul_comm,
    Finset.prod_sdiff (Finset.subset_union_left.trans Finset.subset_union_left)]

end AwayDecomposition

end TauCeti

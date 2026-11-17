/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.MeasureTheory.Measure.Haar.RestrictedProduct.Stage
public import TauCeti.Topology.Algebra.RestrictedProduct.Stage
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Group.OpenSubgroup.Basic
import TauCeti.MeasureTheory.Measure.Haar.Unique
import TauCeti.Topology.Algebra.RestrictedProduct.SecondCountable

/-!
# Haar measures on restricted products

Let `ι` be a countable index type, let `G i` be second-countable locally compact topological
groups with open subgroups `B i` (more generally, any `SetLike` family satisfying `SubgroupClass`),
and let `μ i` be a Haar measure on `G i` such that `μ i (B i) = 1` for all but finitely many `i`.
An open subgroup of finite Haar measure in a locally compact group is automatically compact
(`IsOpen.isCompact_of_isMulLeftInvariant`), so compactness of `B i` for all but finitely many `i`
follows automatically from `∀ᶠ i in Filter.cofinite, μ i (B i) = 1`; no Hausdorff hypothesis is
needed.

This file constructs the unique Haar measure `TauCeti.restrictedHaar μ hμ` on the restricted
product `Πʳ i, [G i, B i]` giving every Borel box `{x | ∀ i, x i ∈ C i}` with `C i = B i`
cofinitely the mass `∏ᶠ i, μ i (C i)`.

## Strategy

Instead of gluing the stage measures `stageMeasure B T μ` by hand, we construct one compact Borel
box `K₀` inside a single stage `U_{S₀}` (`S₀ = {i | μ i (B i) ≠ 1}`), taking closed compact
identity neighbourhoods `K_i` for `i ∈ S₀` and `K_i = B i` for `i ∉ S₀`. We define `restrictedHaar`
as `(∏ i ∈ S₀, μ i (K_i)) • Measure.haarMeasure K₀`. On every stage `U_T` with
`∀ i ∉ T, μ i (B i) = 1`, both `(restrictedHaar μ hμ).comap (↑)` and
`(stageMeasure B T μ).map (stageEquiv B hB T).symm` are Haar measures on the second-countable
locally compact group `U_T`. By uniqueness of Haar measure
(`MeasureTheory.Measure.isMulLeftInvariant_eq_of_measure_eq`) and agreement on the normalizing box
inside `U_T`, the two measures coincide identically. This yields the `MeasurePreserving` stage
decomposition (hence Fubini/Tonelli for factorizable integrands on `U_T`), the box formula (for
both cofinitely-`B` boxes and countable boxes `C i ⊆ B i`), uniqueness among all σ-finite
left-invariant measures, right- and inversion-invariance inheritance, scaling under factor
rescalings, and infinite mass when `C i ⊇ B i` has diverging finite products.

All group-theoretic constructions and theorems carry `@[to_additive]` counterparts
(`restrictedAddHaar`, `exists_unique_restrictedAddHaar`, …).

## Main definitions

* `TauCeti.restrictedHaar` / `TauCeti.restrictedAddHaar`: the canonical restricted-product Haar
  measure on `Πʳ i, [G i, B i]`.

## Main results

* `TauCeti.isHaarMeasure_restrictedHaar` and `TauCeti.restrictedHaar_integral_eq_one`: Haar-measure
  instance and mass `1` on `{x | ∀ i, x i ∈ B i}` when `∀ i, μ i (B i) = 1` (requiring neither
  countability of `ι` nor second countability of `G i`).
* `TauCeti.measurePreserving_stageEquiv_restrictedHaar`: the stage isomorphism `stageEquiv`
  identifies `(restrictedHaar μ hμ).comap (↑)` with `stageMeasure`.
* `TauCeti.setLIntegral_stageSubgroup_restrictedHaar_mul` and
  `TauCeti.setIntegral_stageSubgroup_restrictedHaar_smul`: Tonelli/Fubini factorization on `U_T`.
* `TauCeti.restrictedHaar_box`, `TauCeti.restrictedHaar_box_of_forall_subset`,
  `TauCeti.restrictedHaar_integral`, `TauCeti.restrictedHaar_box_single`: box mass formulas.
* `TauCeti.eq_restrictedHaar_of_box`: uniqueness among σ-finite left-invariant measures.
* `TauCeti.exists_unique_restrictedHaar` / `TauCeti.exists_unique_restrictedAddHaar`: existence
  and uniqueness of the restricted-product Haar measure.
* `TauCeti.restrictedHaar_congr`, `TauCeti.isMulRightInvariant_restrictedHaar`,
  `TauCeti.isInvInvariant_restrictedHaar`: congruence, right-invariance, and inversion-invariance.
* `TauCeti.restrictedHaar_smul`, `TauCeti.restrictedHaar_smul_single`: rescaling behavior.
* `TauCeti.finset_prod_le_restrictedHaar_box` and
  `TauCeti.restrictedHaar_box_eq_top_of_iSup_eq_top`: lower bounds and divergence criterion for
  non-cofinite boxes containing `B i`.

## References

* J. Tate, *Fourier analysis in number fields, and Hecke's zeta-functions*, in J. W. S. Cassels
  and A. Fröhlich, eds., *Algebraic Number Theory* (1967), §3.3.
* D. Ramakrishnan and R. J. Valenza, *Fourier Analysis on Number Fields*, Springer (1999),
  Chapter 5.
-/

public section

noncomputable section

open Filter MeasureTheory MeasureTheory.Measure Set TopologicalSpace Topology
open scoped ENNReal NNReal Pointwise RestrictedProduct

namespace TauCeti

/-! ### Private normalization helpers -/

section BadFinset

variable {ι : Type*} {G S : ι → Type*} [∀ i, MeasurableSpace (G i)] [∀ i, SetLike (S i) (G i)]
  {B : ∀ i, S i}

/-- Helper: the finite exceptional set `{i | μ i (B i) ≠ 1}`. -/
private def badFinset (μ : ∀ i, Measure (G i))
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) : Finset ι :=
  (mem_cofinite.mp hμ).toFinset

private theorem measure_eq_one_of_notMem_badFinset {μ : ∀ i, Measure (G i)}
    {hμ : ∀ᶠ i in cofinite, μ i (B i) = 1} {i : ι} (hi : i ∉ badFinset (B := B) μ hμ) :
    μ i (B i) = 1 := by
  by_contra hne
  exact hi ((mem_cofinite.mp hμ).mem_toFinset.mpr hne)

end BadFinset

section NormFactor

variable {ι : Type*} {G S : ι → Type*}
  [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
  [∀ i, LocallyCompactSpace (G i)]
  [∀ i, MeasurableSpace (G i)] [∀ i, SetLike (S i) (G i)]
  {B : ∀ i, S i}

/-- Helper: given `μ`, choose `B i` when `μ i (B i) = 1`, and a closed compact identity
neighbourhood otherwise. -/
@[to_additive addNormFactor]
private def normFactor (μ : ∀ i, Measure (G i)) (i : ι) : Set (G i) :=
  if μ i (B i) = 1 then (B i : Set (G i))
  else (exists_mem_nhds_isCompact_isClosed (1 : G i)).choose

@[to_additive addNormFactor_eq_of_measure_eq_one]
private theorem normFactor_eq_of_measure_eq_one {μ : ∀ i, Measure (G i)} {i : ι}
    (hi : μ i (B i) = 1) : normFactor (B := B) μ i = B i := by
  simp [normFactor, hi]

@[to_additive isCompact_addNormFactor]
private theorem isCompact_normFactor [∀ i, BorelSpace (G i)] [∀ i, SubgroupClass (S i) (G i)]
    (hBopen : ∀ i, IsOpen (B i : Set (G i)))
    {μ : ∀ i, Measure (G i)} [∀ i, (μ i).IsHaarMeasure] (i : ι) :
    IsCompact (normFactor (B := B) μ i) := by
  by_cases hi : μ i (B i) = 1
  · rw [normFactor_eq_of_measure_eq_one hi]
    have hne : μ i (B i) ≠ ∞ := by simp [hi]
    exact (hBopen i).isCompact_of_isMulLeftInvariant hne
  · simp only [normFactor, hi, ↓reduceIte]
    exact (exists_mem_nhds_isCompact_isClosed (1 : G i)).choose_spec.2.1

@[to_additive mem_nhds_zero_addNormFactor]
private theorem mem_nhds_one_normFactor [∀ i, SubgroupClass (S i) (G i)]
    (hBopen : ∀ i, IsOpen (B i : Set (G i))) {μ : ∀ i, Measure (G i)} (i : ι) :
    normFactor (B := B) μ i ∈ 𝓝 (1 : G i) := by
  by_cases hi : μ i (B i) = 1
  · rw [normFactor_eq_of_measure_eq_one hi]
    exact (hBopen i).mem_nhds (one_mem (B i))
  · simp only [normFactor, hi, ↓reduceIte]
    exact (exists_mem_nhds_isCompact_isClosed (1 : G i)).choose_spec.1

@[to_additive measurableSet_addNormFactor]
private theorem measurableSet_normFactor [∀ i, BorelSpace (G i)]
    (hBopen : ∀ i, IsOpen (B i : Set (G i))) {μ : ∀ i, Measure (G i)} (i : ι) :
    MeasurableSet (normFactor (B := B) μ i) := by
  by_cases hi : μ i (B i) = 1
  · rw [normFactor_eq_of_measure_eq_one hi]
    exact (hBopen i).measurableSet
  · simp only [normFactor, hi, ↓reduceIte]
    exact (exists_mem_nhds_isCompact_isClosed (1 : G i)).choose_spec.2.2.measurableSet

@[to_additive addNormFactor_pos_ne_top]
private theorem normFactor_pos_ne_top [∀ i, BorelSpace (G i)] [∀ i, SubgroupClass (S i) (G i)]
    (hBopen : ∀ i, IsOpen (B i : Set (G i)))
    {μ : ∀ i, Measure (G i)} [∀ i, (μ i).IsHaarMeasure] (i : ι) :
    μ i (normFactor (B := B) μ i) ≠ 0 ∧ μ i (normFactor (B := B) μ i) ≠ ∞ :=
  ⟨(measure_pos_of_mem_nhds (μ i) (mem_nhds_one_normFactor hBopen i)).ne',
    (isCompact_normFactor hBopen (μ := μ) i).measure_lt_top.ne⟩

end NormFactor

/-! ### Construction of `restrictedHaar` and stage decomposition -/

section Main

variable {ι : Type*} {G S : ι → Type*}
  [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
  [∀ i, LocallyCompactSpace (G i)]
  [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
  [∀ i, SetLike (S i) (G i)] [∀ i, SubgroupClass (S i) (G i)]
  {B : ∀ i, S i} [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]

/-- Helper: the normalizing box `{x | ∀ i, x i ∈ normFactor μ i}` as a `PositiveCompacts`. -/
@[to_additive addNormPositiveCompacts]
private def normPositiveCompacts (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    PositiveCompacts (Πʳ i, [G i, B i]) := by
  set S₀ := badFinset (B := B) μ hμ
  set U := stageSubgroup B hBopen.out (S₀ : Set ι)
  set e := stageEquiv B hBopen.out S₀
  have hcomp_out : ∀ j : {i // i ∉ (S₀ : Set ι)}, CompactSpace (B j.1) := fun j ↦ by
    have hne : μ j.1 (B j.1) ≠ ∞ := by simp [measure_eq_one_of_notMem_badFinset j.2]
    exact isCompact_iff_compactSpace.mp ((hBopen.out j.1).isCompact_of_isMulLeftInvariant hne)
  have hbox_eq : {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ normFactor (B := B) μ i} =
      (((↑) : U → Πʳ i, [G i, B i]) ∘ e.symm) ''
        ((Set.univ.pi fun i : S₀ ↦ normFactor (B := B) μ i.1) ×ˢ Set.univ) :=
    (stageEquiv_symm_image_box_of_eq B hBopen.out S₀ fun _ hi ↦
      normFactor_eq_of_measure_eq_one (measure_eq_one_of_notMem_badFinset hi)).symm
  refine ⟨⟨{x | ∀ i, x i ∈ normFactor (B := B) μ i}, ?_⟩, ?_⟩
  · rw [hbox_eq]
    have hKprod : IsCompact ((Set.univ.pi fun i : S₀ ↦ normFactor (B := B) μ i.1) ×ˢ
        (Set.univ : Set (∀ j : {i // i ∉ (S₀ : Set ι)}, B j.1))) :=
      (isCompact_univ_pi fun i ↦ isCompact_normFactor hBopen.out (μ := μ) i.1).prod isCompact_univ
    exact hKprod.image (continuous_subtype_val.comp e.symm.continuous)
  · refine ⟨1, mem_interior.mpr ?_⟩
    let V : Set (Πʳ i, [G i, B i]) :=
      (((↑) : U → Πʳ i, [G i, B i]) ∘ e.symm) ''
        ((Set.univ.pi fun i : S₀ ↦ interior (normFactor (B := B) μ i.1)) ×ˢ Set.univ)
    refine ⟨V, ?_, ?_, ?_⟩
    · dsimp only [V]
      rw [hbox_eq]
      exact image_mono (prod_mono (pi_mono fun _ _ ↦ interior_subset) Subset.rfl)
    · have hVopen : IsOpen ((Set.univ.pi fun i : S₀ ↦ interior (normFactor (B := B) μ i.1)) ×ˢ
          (Set.univ : Set (∀ j : {i // i ∉ (S₀ : Set ι)}, B j.1))) :=
        (isOpen_set_pi finite_univ fun _ _ ↦ isOpen_interior).prod isOpen_univ
      exact (U.isOpen.isOpenEmbedding_subtypeVal.comp
        e.symm.toHomeomorph.isOpenEmbedding).isOpenMap _ hVopen
    · refine ⟨(fun _ ↦ 1, fun _ ↦ 1), ⟨fun i _ ↦ ?_, trivial⟩, ?_⟩
      · exact mem_interior_iff_mem_nhds.mpr (mem_nhds_one_normFactor hBopen.out i.1)
      · exact congrArg ((↑) : U → Πʳ i, [G i, B i]) (map_one e.symm)

@[to_additive coe_addNormPositiveCompacts]
private theorem coe_normPositiveCompacts (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    ((normPositiveCompacts (B := B) μ hμ : PositiveCompacts (Πʳ i, [G i, B i])) :
      Set (Πʳ i, [G i, B i])) = {x | ∀ i, x i ∈ normFactor (B := B) μ i} :=
  rfl

@[to_additive addNormPositiveCompacts_subset_addStageSubgroup]
private theorem normPositiveCompacts_subset_stageSubgroup (μ : ∀ i, Measure (G i))
    [∀ i, (μ i).IsHaarMeasure] (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1)
    {T : Finset ι} (hT : ∀ i ∉ T, μ i (B i) = 1) :
    (normPositiveCompacts (B := B) μ hμ : Set (Πʳ i, [G i, B i])) ⊆
      stageSubgroup B hBopen.out (T : Set ι) := by
  intro x hx
  rw [coe_normPositiveCompacts] at hx
  rw [SetLike.mem_coe, mem_stageSubgroup]
  intro i hi
  rw [← SetLike.mem_coe, ← normFactor_eq_of_measure_eq_one (hT i hi)]
  exact hx i

variable [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]

/-- The canonical Haar measure on the restricted product `Πʳ i, [G i, B i]` attached to a family
of Haar measures `μ i` satisfying `μ i (B i) = 1` for all but finitely many `i`. When `ι` is
countable and each `G i` is second countable, it is uniquely characterized by giving every Borel
box `{x | ∀ i, x i ∈ C i}` with `C i = B i` cofinitely the mass `∏ᶠ i, μ i (C i)`. -/
@[to_additive /-- The canonical additive Haar measure on the restricted product
`Πʳ i, [G i, B i]` attached to a family of additive Haar measures `μ i` satisfying `μ i (B i) = 1`
for all but finitely many `i`. When `ι` is countable and each `G i` is second countable, it is
uniquely characterized by giving every Borel box `{x | ∀ i, x i ∈ C i}` with `C i = B i`
cofinitely the mass `∏ᶠ i, μ i (C i)`. -/]
def restrictedHaar (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    Measure (Πʳ i, [G i, B i]) :=
  (∏ i ∈ badFinset (B := B) μ hμ, μ i (normFactor (B := B) μ i)) •
    Measure.haarMeasure (normPositiveCompacts (B := B) μ hμ)

/-- `restrictedHaar μ hμ` is a Haar measure on `Πʳ i, [G i, B i]`. -/
@[to_additive /-- `restrictedAddHaar μ hμ` is an additive Haar measure on `Πʳ i, [G i, B i]`. -/]
instance isHaarMeasure_restrictedHaar (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    (restrictedHaar (B := B) μ hμ).IsHaarMeasure := by
  have hc0 : (∏ i ∈ badFinset (B := B) μ hμ, μ i (normFactor (B := B) μ i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ ↦ (normFactor_pos_ne_top hBopen.out (B := B) (μ := μ) i).1
  have hctop : (∏ i ∈ badFinset (B := B) μ hμ, μ i (normFactor (B := B) μ i)) ≠ ∞ :=
    ENNReal.prod_ne_top fun i _ ↦ (normFactor_pos_ne_top hBopen.out (B := B) (μ := μ) i).2
  have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    locallyCompactSpace_of_isMulLeftInvariant μ (hμ.mono fun _ hi ↦ by simp [hi])
  dsimp only [restrictedHaar]
  exact IsHaarMeasure.smul _ hc0 hctop

/-- Helper: mass of the normalizing positive compact box under `restrictedHaar`. -/
@[to_additive]
private theorem restrictedHaar_normPositiveCompacts (μ : ∀ i, Measure (G i))
    [∀ i, (μ i).IsHaarMeasure] (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    restrictedHaar (B := B) μ hμ (normPositiveCompacts (B := B) μ hμ) =
      ∏ i ∈ badFinset (B := B) μ hμ, μ i (normFactor (B := B) μ i) := by
  rw [restrictedHaar, smul_apply, smul_eq_mul, Measure.haarMeasure_self, mul_one]

/-- When `μ i (B i) = 1` at every index `i`, the everywhere-integral subgroup `{x | ∀ i, x i ∈ B i}`
has mass `1`. This requires neither countability of `ι` nor second countability of `G i`. -/
@[to_additive restrictedAddHaar_integral_eq_one /-- When `μ i (B i) = 1` at every index `i`, the
everywhere-integral additive subgroup `{x | ∀ i, x i ∈ B i}` has mass `1`. This requires neither
countability of `ι` nor second countability of `G i`. -/]
theorem restrictedHaar_integral_eq_one (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ i, μ i (B i) = 1) :
    restrictedHaar (B := B) μ (.of_forall hμ) {x | ∀ i, x i ∈ B i} = 1 := by
  have hbad : badFinset (B := B) μ (.of_forall hμ) = ∅ := by
    ext i
    simp [badFinset, hμ i]
  have hset : (normPositiveCompacts (B := B) μ (.of_forall hμ) : Set (Πʳ i, [G i, B i])) =
      {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ B i} := by
    rw [coe_normPositiveCompacts]
    ext x
    simp [normFactor_eq_of_measure_eq_one (hμ _)]
  rw [← hset]
  exact (restrictedHaar_normPositiveCompacts μ (.of_forall hμ)).trans (by rw [hbad]; simp)

variable [Countable ι] [∀ i, SecondCountableTopology (G i)]

/-- Helper: on any stage `U_T` containing `badFinset`, pushing `stageMeasure` forward along
`stageEquiv.symm` equals pulling `restrictedHaar` back to `U_T`. -/
@[to_additive map_addStageEquiv_symm_eq_comap_of_subset]
private theorem map_stageEquiv_symm_eq_comap_of_subset (μ : ∀ i, Measure (G i))
    [∀ i, (μ i).IsHaarMeasure] (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1)
    {T : Finset ι} (hsub : badFinset (B := B) μ hμ ⊆ T) :
    (stageMeasure B T μ).map (stageEquiv B hBopen.out T).symm =
      (restrictedHaar (B := B) μ hμ).comap
        ((↑) : stageSubgroup B hBopen.out (T : Set ι) → Πʳ i, [G i, B i]) := by
  have hT : ∀ i ∉ T, μ i (B i) = 1 :=
    fun i hi ↦ measure_eq_one_of_notMem_badFinset (fun h ↦ hi (hsub h))
  set U := stageSubgroup B hBopen.out (T : Set ι)
  set e := stageEquiv B hBopen.out T
  have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    locallyCompactSpace_of_isMulLeftInvariant μ (hμ.mono fun _ hi ↦ by simp [hi])
  have : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  have : SecondCountableTopology U := IsInducing.subtypeVal.secondCountableTopology
  have : ∀ i, IsTopologicalGroup (B i) :=
    fun i ↦ IsInducing.subtypeVal.isTopologicalGroup (SubgroupClass.subtype (B i))
  have : ∀ i, SecondCountableTopology (B i) :=
    fun i ↦ IsInducing.subtypeVal.secondCountableTopology
  have : (stageMeasure B T μ).IsHaarMeasure :=
    isHaarMeasure_stageMeasure (fun i _ ↦ hBopen.out i) μ hT
  set ν₁ : Measure U := (stageMeasure B T μ).map e.symm
  set ν₂ : Measure U := (restrictedHaar (B := B) μ hμ).comap ((↑) : U → Πʳ i, [G i, B i])
  have : ν₁.IsHaarMeasure := e.symm.isHaarMeasure_map _
  have : ν₂.IsHaarMeasure := inferInstance
  set K_U : Set U := ((↑) : U → Πʳ i, [G i, B i]) ⁻¹'
    (normPositiveCompacts (B := B) μ hμ : Set (Πʳ i, [G i, B i]))
  have hcoe : MeasurableEmbedding ((↑) : U → Πʳ i, [G i, B i]) :=
    MeasurableEmbedding.subtype_coe U.isOpen.measurableSet
  have hν₂K : ν₂ K_U = ∏ i ∈ badFinset (B := B) μ hμ, μ i (normFactor (B := B) μ i) := by
    rw [hcoe.comap_apply, image_preimage_eq_inter_range, Subtype.range_coe,
      inter_eq_left.mpr (normPositiveCompacts_subset_stageSubgroup μ hμ hT)]
    exact restrictedHaar_normPositiveCompacts μ hμ
  have hK_U_meas : MeasurableSet K_U := measurable_subtype_coe <| by
    rw [coe_normPositiveCompacts]
    exact measurableSet_restrictedProduct_box fun i ↦ measurableSet_normFactor hBopen.out i
  have hν₁K : ν₁ K_U = ∏ i ∈ badFinset (B := B) μ hμ, μ i (normFactor (B := B) μ i) := by
    have hmes : Measurable ⇑e.symm := e.symm.continuous.measurable
    rw [Measure.map_apply hmes hK_U_meas]
    have hpre : e.symm ⁻¹' K_U =
        (Set.univ.pi fun i : T ↦ normFactor (B := B) μ i.1) ×ˢ Set.univ := by
      dsimp only [K_U]
      rw [coe_normPositiveCompacts]
      exact stageEquiv_symm_preimage_box_of_eq B hBopen.out T fun i hi ↦
        normFactor_eq_of_measure_eq_one (hT i hi)
    rw [hpre, stageMeasure_prod_box (fun i _ ↦ (hBopen.out i).measurableSet) μ hT]
    refine (Finset.prod_subset hsub fun i _ hi ↦ ?_).symm
    have h1 : μ i (B i) = 1 := measure_eq_one_of_notMem_badFinset hi
    rw [normFactor_eq_of_measure_eq_one h1, h1]
  refine Measure.isMulLeftInvariant_eq_of_measure_eq ν₁ ν₂ (hν₁K.trans hν₂K.symm) ?_ ?_
  · rw [hν₂K]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦
      (normFactor_pos_ne_top hBopen.out (B := B) (μ := μ) i).1
  · rw [hν₂K]
    exact ENNReal.prod_ne_top fun i _ ↦ (normFactor_pos_ne_top hBopen.out (B := B) (μ := μ) i).2

/-! ### Stage decomposition and Fubini/Tonelli formulas -/

/-- **Stage decomposition of `restrictedHaar`:** for any finite set `T : Finset ι` such that
`μ i (B i) = 1` for all `i ∉ T`, pushing `stageMeasure B T μ` forward along
`(stageEquiv B hBopen.out T).symm` equals pulling `restrictedHaar μ hμ` back to the open stage
subgroup `stageSubgroup B hBopen.out (T : Set ι)`. -/
@[to_additive map_addStageEquiv_symm_stageMeasure /-- **Stage decomposition of
`restrictedAddHaar`:** for any finite set `T : Finset ι` such that `μ i (B i) = 1` for all
`i ∉ T`, pushing `stageMeasure B T μ` forward along `(addStageEquiv B hBopen.out T).symm` equals
pulling `restrictedAddHaar μ hμ` back to `addStageSubgroup B hBopen.out (T : Set ι)`. -/]
theorem map_stageEquiv_symm_stageMeasure (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) {T : Finset ι} (hT : ∀ i ∉ T, μ i (B i) = 1) :
    (stageMeasure B T μ).map (stageEquiv B hBopen.out T).symm =
      (restrictedHaar (B := B) μ hμ).comap
        ((↑) : stageSubgroup B hBopen.out (T : Set ι) → Πʳ i, [G i, B i]) := by
  have hsub : badFinset (B := B) μ hμ ⊆ T := by
    intro i hi
    by_contra hiT
    exact (mem_cofinite.mp hμ).mem_toFinset.mp hi (hT i hiT)
  exact map_stageEquiv_symm_eq_comap_of_subset μ hμ hsub

/-- The inverse stage isomorphism `stageEquiv.symm` is measure-preserving from `stageMeasure` to
the pullback of `restrictedHaar` on `stageSubgroup`. -/
@[to_additive measurePreserving_addStageEquiv_symm_restrictedAddHaar /-- The inverse additive stage
isomorphism `addStageEquiv.symm` is measure-preserving from `stageMeasure` to the pullback of
`restrictedAddHaar` on `addStageSubgroup`. -/]
theorem measurePreserving_stageEquiv_symm_restrictedHaar (μ : ∀ i, Measure (G i))
    [∀ i, (μ i).IsHaarMeasure] (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1)
    {T : Finset ι} (hT : ∀ i ∉ T, μ i (B i) = 1) :
    MeasurePreserving (stageEquiv B hBopen.out T).symm (stageMeasure B T μ)
      ((restrictedHaar (B := B) μ hμ).comap
        ((↑) : stageSubgroup B hBopen.out (T : Set ι) → Πʳ i, [G i, B i])) := by
  have : ∀ i, SecondCountableTopology (B i) :=
    fun i ↦ IsInducing.subtypeVal.secondCountableTopology
  exact ⟨(stageEquiv B hBopen.out T).symm.continuous.measurable,
    map_stageEquiv_symm_stageMeasure μ hμ hT⟩

/-- The stage isomorphism `stageEquiv` is measure-preserving from the pullback of `restrictedHaar`
on `stageSubgroup` to `stageMeasure`. -/
@[to_additive measurePreserving_addStageEquiv_restrictedAddHaar /-- The additive stage isomorphism
`addStageEquiv` is measure-preserving from the pullback of `restrictedAddHaar` on
`addStageSubgroup` to `stageMeasure`. -/]
theorem measurePreserving_stageEquiv_restrictedHaar (μ : ∀ i, Measure (G i))
    [∀ i, (μ i).IsHaarMeasure] (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1)
    {T : Finset ι} (hT : ∀ i ∉ T, μ i (B i) = 1) :
    MeasurePreserving (stageEquiv B hBopen.out T)
      ((restrictedHaar (B := B) μ hμ).comap
        ((↑) : stageSubgroup B hBopen.out (T : Set ι) → Πʳ i, [G i, B i]))
      (stageMeasure B T μ) := by
  have : ∀ i, SecondCountableTopology (B i) :=
    fun i ↦ IsInducing.subtypeVal.secondCountableTopology
  have hf : Measurable ⇑(stageEquiv B hBopen.out T) :=
    (stageEquiv B hBopen.out T).continuous.measurable
  have hg : Measurable ⇑(stageEquiv B hBopen.out T).symm :=
    (stageEquiv B hBopen.out T).symm.continuous.measurable
  refine ⟨hf, ?_⟩
  rw [← map_stageEquiv_symm_stageMeasure μ hμ hT, Measure.map_map hf hg]
  have hcomp : (⇑(stageEquiv B hBopen.out T) ∘ ⇑(stageEquiv B hBopen.out T).symm) = id :=
    funext fun p ↦ (stageEquiv B hBopen.out T).apply_symm_apply p
  rw [hcomp, Measure.map_id]

/-- Lower Lebesgue integral over a stage subgroup `U_T` rewritten on the product space. -/
@[to_additive setLIntegral_addStageSubgroup_restrictedAddHaar /-- Lower Lebesgue integral over an
additive stage subgroup `U_T` rewritten on the product space. -/]
theorem setLIntegral_stageSubgroup_restrictedHaar (μ : ∀ i, Measure (G i))
    [∀ i, (μ i).IsHaarMeasure] (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1)
    {T : Finset ι} (hT : ∀ i ∉ T, μ i (B i) = 1) (f : Πʳ i, [G i, B i] → ℝ≥0∞) :
    ∫⁻ x in (stageSubgroup B hBopen.out (T : Set ι) : Set (Πʳ i, [G i, B i])),
      f x ∂(restrictedHaar (B := B) μ hμ) =
      ∫⁻ p, f ((stageEquiv B hBopen.out T).symm p : Πʳ i, [G i, B i])
        ∂(stageMeasure B T μ) := by
  have : ∀ i, SecondCountableTopology (B i) :=
    fun i ↦ IsInducing.subtypeVal.secondCountableTopology
  set U := stageSubgroup B hBopen.out (T : Set ι)
  have hcoe : MeasurableEmbedding ((↑) : U → Πʳ i, [G i, B i]) :=
    MeasurableEmbedding.subtype_coe U.isOpen.measurableSet
  have hmp_coe : MeasurePreserving ((↑) : U → Πʳ i, [G i, B i])
      ((restrictedHaar (B := B) μ hμ).comap ((↑) : U → Πʳ i, [G i, B i]))
      ((restrictedHaar (B := B) μ hμ).restrict (U : Set (Πʳ i, [G i, B i]))) :=
    measurePreserving_subtype_coe U.isOpen.measurableSet
  have he : MeasurableEmbedding (stageEquiv B hBopen.out T).symm :=
    (stageEquiv B hBopen.out T).symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  rw [← hmp_coe.map_eq, hcoe.lintegral_map,
    ← (measurePreserving_stageEquiv_symm_restrictedHaar μ hμ hT).map_eq, he.lintegral_map]

/-- Tonelli factorization for lower Lebesgue integrals on `U_T`: the integral of a product
`f₁ (proj_T x) * f₂ (proj_compl x)` splits as the product of the integrals over `T` and `Tᶜ`. -/
@[to_additive setLIntegral_addStageSubgroup_restrictedAddHaar_mul /-- Tonelli factorization for
lower Lebesgue integrals on `U_T`: the integral of a product `f₁ (proj_T x) * f₂ (proj_compl x)`
splits as the product of the integrals over `T` and `Tᶜ`. -/]
theorem setLIntegral_stageSubgroup_restrictedHaar_mul (μ : ∀ i, Measure (G i))
    [∀ i, (μ i).IsHaarMeasure] (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1)
    {T : Finset ι} (hT : ∀ i ∉ T, μ i (B i) = 1)
    {f₁ : (∀ i : T, G i) → ℝ≥0∞} {f₂ : (∀ j : {i // i ∉ (T : Set ι)}, B j.1) → ℝ≥0∞}
    (hf₁ : AEMeasurable f₁ (Measure.pi fun i : T ↦ μ i.1))
    (hf₂ : AEMeasurable f₂ (stageTailMeasure B T μ)) :
    ∫⁻ x : stageSubgroup B hBopen.out (T : Set ι),
      f₁ (stageEquiv B hBopen.out T x).1 * f₂ (stageEquiv B hBopen.out T x).2
        ∂((restrictedHaar (B := B) μ hμ).comap
          ((↑) : stageSubgroup B hBopen.out (T : Set ι) → Πʳ i, [G i, B i])) =
      (∫⁻ y, f₁ y ∂(Measure.pi fun i : T ↦ μ i.1)) *
        ∫⁻ z, f₂ z ∂(stageTailMeasure B T μ) := by
  have : ∀ i, SecondCountableTopology (B i) :=
    fun i ↦ IsInducing.subtypeVal.secondCountableTopology
  have : IsProbabilityMeasure (stageTailMeasure B T μ) :=
    isProbabilityMeasure_stageTailMeasure (fun i _ ↦ (hBopen.out i).measurableSet) μ hT
  have he : MeasurableEmbedding (stageEquiv B hBopen.out T).symm :=
    (stageEquiv B hBopen.out T).symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  rw [← (measurePreserving_stageEquiv_symm_restrictedHaar μ hμ hT).map_eq, he.lintegral_map]
  simp only [ContinuousMulEquiv.apply_symm_apply, stageMeasure_eq_prod]
  exact lintegral_prod_mul hf₁ hf₂

/-- Bochner integral over a stage subgroup `U_T` rewritten on the product space. -/
@[to_additive setIntegral_addStageSubgroup_restrictedAddHaar /-- Bochner integral over an additive
stage subgroup `U_T` rewritten on the product space. -/]
theorem setIntegral_stageSubgroup_restrictedHaar {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) {T : Finset ι} (hT : ∀ i ∉ T, μ i (B i) = 1)
    (f : Πʳ i, [G i, B i] → E) :
    ∫ x in (stageSubgroup B hBopen.out (T : Set ι) : Set (Πʳ i, [G i, B i])),
      f x ∂(restrictedHaar (B := B) μ hμ) =
      ∫ p, f ((stageEquiv B hBopen.out T).symm p : Πʳ i, [G i, B i])
        ∂(stageMeasure B T μ) := by
  have : ∀ i, SecondCountableTopology (B i) :=
    fun i ↦ IsInducing.subtypeVal.secondCountableTopology
  set U := stageSubgroup B hBopen.out (T : Set ι)
  have hcoe : MeasurableEmbedding ((↑) : U → Πʳ i, [G i, B i]) :=
    MeasurableEmbedding.subtype_coe U.isOpen.measurableSet
  have hmp_coe : MeasurePreserving ((↑) : U → Πʳ i, [G i, B i])
      ((restrictedHaar (B := B) μ hμ).comap ((↑) : U → Πʳ i, [G i, B i]))
      ((restrictedHaar (B := B) μ hμ).restrict (U : Set (Πʳ i, [G i, B i]))) :=
    measurePreserving_subtype_coe U.isOpen.measurableSet
  have he : MeasurableEmbedding (stageEquiv B hBopen.out T).symm :=
    (stageEquiv B hBopen.out T).symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  rw [← hmp_coe.map_eq, hcoe.integral_map,
    ← (measurePreserving_stageEquiv_symm_restrictedHaar μ hμ hT).map_eq, he.integral_map]

/-- Fubini factorization for Bochner integrals on `U_T`: the integral of a product
`f₁ (proj_T x) • f₂ (proj_compl x)` splits as the product of the integrals over `T` and `Tᶜ`. -/
@[to_additive (dont_translate := 𝕜 E) setIntegral_addStageSubgroup_restrictedAddHaar_smul
/-- Fubini factorization for Bochner integrals on `U_T`: the integral of a product
`f₁ (proj_T x) • f₂ (proj_compl x)` splits as the product of the integrals over `T` and `Tᶜ`. -/]
theorem setIntegral_stageSubgroup_restrictedHaar_smul {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) {T : Finset ι} (hT : ∀ i ∉ T, μ i (B i) = 1)
    (f₁ : (∀ i : T, G i) → 𝕜) (f₂ : (∀ j : {i // i ∉ (T : Set ι)}, B j.1) → E) :
    ∫ x : stageSubgroup B hBopen.out (T : Set ι),
      f₁ (stageEquiv B hBopen.out T x).1 • f₂ (stageEquiv B hBopen.out T x).2
        ∂((restrictedHaar (B := B) μ hμ).comap
          ((↑) : stageSubgroup B hBopen.out (T : Set ι) → Πʳ i, [G i, B i])) =
      (∫ y, f₁ y ∂(Measure.pi fun i : T ↦ μ i.1)) •
        ∫ z, f₂ z ∂(stageTailMeasure B T μ) := by
  have : ∀ i, SecondCountableTopology (B i) :=
    fun i ↦ IsInducing.subtypeVal.secondCountableTopology
  have : IsProbabilityMeasure (stageTailMeasure B T μ) :=
    isProbabilityMeasure_stageTailMeasure (fun i _ ↦ (hBopen.out i).measurableSet) μ hT
  have he : MeasurableEmbedding (stageEquiv B hBopen.out T).symm :=
    (stageEquiv B hBopen.out T).symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  rw [← (measurePreserving_stageEquiv_symm_restrictedHaar μ hμ hT).map_eq, he.integral_map]
  simp only [ContinuousMulEquiv.apply_symm_apply, stageMeasure_eq_prod]
  exact integral_prod_smul f₁ f₂

/-! ### Box mass formulas -/

/-- Mass of a countable Borel box `{x | ∀ i, x i ∈ C i}` with `C i ⊆ B i` outside a finite set `T`
on which `μ i (B i) = 1` outside `T`. -/
@[to_additive /-- Mass of a countable Borel box `{x | ∀ i, x i ∈ C i}` with `C i ⊆ B i` outside a
finite set `T` on which `μ i (B i) = 1` outside `T`. -/]
theorem restrictedHaar_box_of_forall_subset (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) {T : Finset ι} (hT : ∀ i ∉ T, μ i (B i) = 1)
    {C : ∀ i, Set (G i)} (hCm : ∀ i, MeasurableSet (C i)) (hCB : ∀ i ∉ T, C i ⊆ B i) :
    restrictedHaar (B := B) μ hμ {x | ∀ i, x i ∈ C i} =
      (∏ i ∈ T, μ i (C i)) * ∏' j : {i // i ∉ (T : Set ι)}, μ j.1 (C j.1) := by
  have : ∀ i, SecondCountableTopology (B i) :=
    fun i ↦ IsInducing.subtypeVal.secondCountableTopology
  set U := stageSubgroup B hBopen.out (T : Set ι)
  set e := stageEquiv B hBopen.out T
  have hsub : {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ C i} ⊆ (U : Set (Πʳ i, [G i, B i])) := by
    intro x hx
    rw [SetLike.mem_coe, mem_stageSubgroup]
    exact fun i hi ↦ hCB i hi (hx i)
  have hcoe : MeasurableEmbedding ((↑) : U → Πʳ i, [G i, B i]) :=
    MeasurableEmbedding.subtype_coe U.isOpen.measurableSet
  have hmeas_U : MeasurableSet (((↑) : U → Πʳ i, [G i, B i]) ⁻¹' {x | ∀ i, x i ∈ C i}) :=
    measurable_subtype_coe (measurableSet_restrictedProduct_box hCm)
  have hval : restrictedHaar (B := B) μ hμ {x | ∀ i, x i ∈ C i} =
      ((restrictedHaar (B := B) μ hμ).comap ((↑) : U → Πʳ i, [G i, B i]))
        (((↑) : U → Πʳ i, [G i, B i]) ⁻¹' {x | ∀ i, x i ∈ C i}) := by
    rw [hcoe.comap_apply, image_preimage_eq_inter_range, Subtype.range_coe, inter_eq_left.mpr hsub]
  have hpre : e.symm ⁻¹' (((↑) : U → Πʳ i, [G i, B i]) ⁻¹' {x | ∀ i, x i ∈ C i}) =
      (Set.univ.pi fun i : T ↦ C i.1) ×ˢ
        (Set.univ.pi fun j : {i // i ∉ (T : Set ι)} ↦ ((↑) : B j.1 → G j.1) ⁻¹' C j.1) :=
    stageEquiv_symm_preimage_box B hBopen.out T C
  have hmes : Measurable ⇑e.symm := e.symm.continuous.measurable
  rw [hval, ← map_stageEquiv_symm_stageMeasure μ hμ hT, Measure.map_apply hmes hmeas_U, hpre,
    stageMeasure_prod_box_countable (fun i _ ↦ (hBopen.out i).measurableSet) μ hT hCm]
  congr 1
  congr 1 with j
  rw [inter_eq_left.mpr (hCB j.1 j.2)]

/-- **Box formula for `restrictedHaar`:** for every family of Borel sets `C i` with `C i = B i`
for all but finitely many `i`, the box `{x | ∀ i, x i ∈ C i}` has measure `∏ᶠ i, μ i (C i)`. -/
@[to_additive /-- **Box formula for `restrictedAddHaar`:** for every family of Borel sets `C i`
with `C i = B i` for all but finitely many `i`, the box `{x | ∀ i, x i ∈ C i}` has measure
`∏ᶠ i, μ i (C i)`. -/]
theorem restrictedHaar_box (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) {C : ∀ i, Set (G i)}
    (hCm : ∀ i, MeasurableSet (C i)) (hCB : ∀ᶠ i in cofinite, C i = B i) :
    restrictedHaar (B := B) μ hμ {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i) := by
  classical
  set T : Finset ι := badFinset (B := B) μ hμ ∪ (mem_cofinite.mp hCB).toFinset
  have hTμ : ∀ i ∉ T, μ i (B i) = 1 := fun i hi ↦
    measure_eq_one_of_notMem_badFinset (fun h ↦ hi (Finset.mem_union_left _ h))
  have hTC : ∀ i ∉ T, C i = B i := fun i hi ↦ by
    by_contra hne
    exact hi (Finset.mem_union_right _ ((mem_cofinite.mp hCB).mem_toFinset.mpr hne))
  rw [restrictedHaar_box_of_forall_subset μ hμ hTμ hCm fun i hi ↦ (hTC i hi).subset]
  have htail : ∀ j : {i // i ∉ (T : Set ι)}, μ j.1 (C j.1) = 1 := fun j ↦ by
    rw [hTC j.1 j.2, hTμ j.1 j.2]
  simp only [htail, tprod_one, mul_one]
  symm
  exact finprod_eq_prod_of_mulSupport_subset _ fun i hi ↦ by
    by_contra hiT
    exact hi (by dsimp only; rw [hTC i hiT, hTμ i hiT])

/-- The everywhere-integral subgroup `{x | ∀ i, x i ∈ B i}` has mass `∏ᶠ i, μ i (B i)`. -/
@[to_additive /-- The everywhere-integral additive subgroup `{x | ∀ i, x i ∈ B i}` has mass
`∏ᶠ i, μ i (B i)`. -/]
theorem restrictedHaar_integral (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    restrictedHaar (B := B) μ hμ {x | ∀ i, x i ∈ B i} = ∏ᶠ i, μ i (B i) :=
  restrictedHaar_box μ hμ (fun i ↦ (hBopen.out i).measurableSet) (.of_forall fun _ ↦ rfl)

/-- Modifying a single coordinate `i₀` of the integral box to a Borel set `C₀` gives mass
`μ i₀ C₀` whenever `μ i (B i) = 1` for all `i ≠ i₀`. -/
@[to_additive /-- Modifying a single coordinate `i₀` of the integral box to a Borel set `C₀` gives
mass `μ i₀ C₀` whenever `μ i (B i) = 1` for all `i ≠ i₀`. -/]
theorem restrictedHaar_box_single (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) (i₀ : ι) (h1 : ∀ i, i ≠ i₀ → μ i (B i) = 1)
    {C₀ : Set (G i₀)} (hC₀ : MeasurableSet C₀) :
    restrictedHaar (B := B) μ hμ {x | x i₀ ∈ C₀ ∧ ∀ i, i ≠ i₀ → x i ∈ B i} = μ i₀ C₀ := by
  classical
  let C : ∀ i, Set (G i) := Function.update (fun i ↦ (B i : Set (G i))) i₀ C₀
  have hset : {x : Πʳ i, [G i, B i] | x i₀ ∈ C₀ ∧ ∀ i, i ≠ i₀ → x i ∈ B i} =
      {x | ∀ i, x i ∈ C i} := by
    ext x
    constructor
    · rintro ⟨h₀, hrest⟩ i
      by_cases hi : i = i₀
      · subst hi; simpa [C] using h₀
      · simpa [C, hi] using hrest i hi
    · intro hx
      exact ⟨by simpa [C] using hx i₀, fun i hi ↦ by simpa [C, hi] using hx i⟩
  rw [hset, restrictedHaar_box μ hμ]
  · rw [finprod_eq_single _ i₀ fun i hi ↦ by simp [C, hi, h1 i hi]]
    simp [C]
  · intro i
    by_cases hi : i = i₀
    · subst hi; simpa [C] using hC₀
    · simpa [C, hi] using (hBopen.out i).measurableSet
  · refine Filter.eventually_cofinite.mpr ((Set.finite_singleton i₀).subset fun i hi ↦ ?_)
    by_contra hne
    have hne' : i ≠ i₀ := hne
    exact hi (by simp [C, hne'])

/-! ### Uniqueness and existence-and-uniqueness -/

/-- **Uniqueness of `restrictedHaar`:** any σ-finite left-invariant measure on `Πʳ i, [G i, B i]`
giving every cofinitely-`B` Borel box the product of the local masses equals
`restrictedHaar μ hμ`. -/
@[to_additive /-- **Uniqueness of `restrictedAddHaar`:** any σ-finite left-invariant measure on
`Πʳ i, [G i, B i]` giving every cofinitely-`B` Borel box the product of the local masses equals
`restrictedAddHaar μ hμ`. -/]
theorem eq_restrictedHaar_of_box (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) (ν : Measure (Πʳ i, [G i, B i]))
    [SigmaFinite ν] [ν.IsMulLeftInvariant]
    (hbox : ∀ C : ∀ i, Set (G i), (∀ i, MeasurableSet (C i)) →
      (∀ᶠ i in cofinite, C i = B i) →
      ν {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i)) :
    ν = restrictedHaar (B := B) μ hμ := by
  have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    locallyCompactSpace_of_isMulLeftInvariant μ (hμ.mono fun _ hi ↦ by simp [hi])
  have hK_ev : ∀ᶠ i in cofinite, normFactor (B := B) μ i = B i :=
    hμ.mono fun _ hi ↦ normFactor_eq_of_measure_eq_one hi
  have hνK : ν (normPositiveCompacts (B := B) μ hμ) =
      ∏ i ∈ badFinset (B := B) μ hμ, μ i (normFactor (B := B) μ i) := by
    rw [coe_normPositiveCompacts, hbox _ (fun i ↦ measurableSet_normFactor hBopen.out i) hK_ev]
    exact finprod_eq_prod_of_mulSupport_subset _ fun i hi ↦ by
      by_contra hbad
      have h1 : μ i (B i) = 1 := measure_eq_one_of_notMem_badFinset hbad
      exact hi (by dsimp only; rw [normFactor_eq_of_measure_eq_one h1, h1])
  rw [Measure.haarMeasure_unique ν (normPositiveCompacts (B := B) μ hμ), hνK]
  rfl

/-- **Restricted products of Haar measures (existence and uniqueness):** when `ι` is countable,
each `G i` is a second-countable locally compact topological group with an open subgroup `B i`
(in any `SubgroupClass`), and `μ i` is a Haar measure with `μ i (B i) = 1` for all but finitely
many `i`, there is a unique Haar measure `ν` on `Πʳ i, [G i, B i]` giving every Borel box
`{x | ∀ i, x i ∈ C i}` with `C i = B i` cofinitely the mass `∏ᶠ i, μ i (C i)`. -/
@[to_additive /-- **Restricted products of additive Haar measures (existence and uniqueness):**
when `ι` is countable, each `G i` is a second-countable locally compact topological additive group
with an open additive subgroup `B i` (in any `AddSubgroupClass`), and `μ i` is an additive Haar
measure with `μ i (B i) = 1` for all but finitely many `i`, there is a unique additive Haar measure
`ν` on `Πʳ i, [G i, B i]` giving every Borel box `{x | ∀ i, x i ∈ C i}` with `C i = B i` cofinitely
the mass `∏ᶠ i, μ i (C i)`. -/]
theorem exists_unique_restrictedHaar (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    ∃! ν : Measure (Πʳ i, [G i, B i]), ν.IsHaarMeasure ∧
      ∀ C : ∀ i, Set (G i), (∀ i, MeasurableSet (C i)) →
        (∀ᶠ i in cofinite, C i = B i) →
        ν {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i) := by
  have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    locallyCompactSpace_of_isMulLeftInvariant μ (hμ.mono fun _ hi ↦ by simp [hi])
  refine ⟨restrictedHaar (B := B) μ hμ, ⟨inferInstance, fun C hCm hCB ↦
    restrictedHaar_box μ hμ hCm hCB⟩, ?_⟩
  rintro ν ⟨hνHaar, hνbox⟩
  exact eq_restrictedHaar_of_box μ hμ ν hνbox

/-! ### Congruence, right-invariance, inversion-invariance, and rescaling -/

/-- Equal families of local Haar measures produce the same restricted-product Haar measure. -/
@[to_additive /-- Equal families of local additive Haar measures produce the same
restricted-product additive Haar measure. -/]
theorem restrictedHaar_congr {μ₁ μ₂ : ∀ i, Measure (G i)}
    [∀ i, (μ₁ i).IsHaarMeasure] [∀ i, (μ₂ i).IsHaarMeasure]
    (h₁ : ∀ᶠ i in cofinite, μ₁ i (B i) = 1) (h₂ : ∀ᶠ i in cofinite, μ₂ i (B i) = 1)
    (heq : ∀ i, μ₁ i = μ₂ i) :
    restrictedHaar (B := B) μ₁ h₁ = restrictedHaar (B := B) μ₂ h₂ := by
  have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    locallyCompactSpace_of_isMulLeftInvariant μ₂ (h₂.mono fun _ hi ↦ by simp [hi])
  refine eq_restrictedHaar_of_box μ₂ h₂ _ fun C hCm hCB ↦ ?_
  rw [restrictedHaar_box μ₁ h₁ hCm hCB]
  simp only [heq]

/-- If every local Haar measure `μ i` is right-invariant (e.g. when every `G i` is unimodular),
then `restrictedHaar μ hμ` is right-invariant. -/
@[to_additive /-- If every local additive Haar measure `μ i` is right-invariant, then
`restrictedAddHaar μ hμ` is right-invariant. -/]
instance isMulRightInvariant_restrictedHaar (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    [∀ i, (μ i).IsMulRightInvariant] (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    (restrictedHaar (B := B) μ hμ).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
      locallyCompactSpace_of_isMulLeftInvariant μ (hμ.mono fun _ hi ↦ by simp [hi])
    have : ((restrictedHaar (B := B) μ hμ).map (· * g)).IsHaarMeasure :=
      isHaarMeasure_map_mul_right _ g
    refine eq_restrictedHaar_of_box μ hμ _ fun C hCm hCB ↦ ?_
    have hpre : (· * g) ⁻¹' {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ C i} =
        {x | ∀ i, x i ∈ (· * g i) ⁻¹' C i} := rfl
    rw [Measure.map_apply (measurable_mul_const g) (measurableSet_restrictedProduct_box hCm), hpre,
      restrictedHaar_box μ hμ (fun i ↦ measurable_mul_const (g i) (hCm i))]
    · congr 1 with i
      exact measure_preimage_mul_right (μ i) (g i) (C i)
    · filter_upwards [hCB, g.2] with i hCi hgi
      ext y
      simp only [mem_preimage, hCi, SetLike.mem_coe]
      exact (Subgroup.ofClass (B i)).mul_mem_cancel_right hgi

/-- If every local Haar measure `μ i` is inversion-invariant, then `restrictedHaar μ hμ` is
inversion-invariant. -/
@[to_additive /-- If every local additive Haar measure `μ i` is negation-invariant, then
`restrictedAddHaar μ hμ` is negation-invariant. -/]
instance isInvInvariant_restrictedHaar (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    [∀ i, (μ i).IsInvInvariant] (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    (restrictedHaar (B := B) μ hμ).IsInvInvariant where
  inv_eq_self := by
    have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
      locallyCompactSpace_of_isMulLeftInvariant μ (hμ.mono fun _ hi ↦ by simp [hi])
    have : ∀ i, (μ i).IsMulRightInvariant := fun i ↦ by
      rw [← Measure.inv_eq_self (μ i)]
      infer_instance
    have : (restrictedHaar (B := B) μ hμ).IsMulRightInvariant := inferInstance
    refine eq_restrictedHaar_of_box μ hμ _ fun C hCm hCB ↦ ?_
    have hpre : (Inv.inv : Πʳ i, [G i, B i] → _) ⁻¹' {x | ∀ i, x i ∈ C i} =
        {x | ∀ i, x i ∈ (C i)⁻¹} := by
      ext x; simp
    rw [Measure.inv_def, Measure.map_apply measurable_inv (measurableSet_restrictedProduct_box hCm),
      hpre, restrictedHaar_box μ hμ (fun i ↦ (hCm i).inv)]
    · congr 1 with i
      exact (μ i).measure_inv (C i)
    · filter_upwards [hCB] with i hCi
      rw [hCi]
      ext y
      exact inv_mem_iff

/-- Rescaling each local Haar measure `μ i` by `c i` multiplies `restrictedHaar` by `∏ᶠ i, c i`.
Positivity, finiteness (`c i ≠ 0, ∞`), and `c i = 1` cofinitely follow automatically from the
`IsHaarMeasure` and normalization hypotheses. -/
@[to_additive restrictedAddHaar_smul /-- Rescaling each local additive Haar measure `μ i` by `c i`
multiplies `restrictedAddHaar` by `∏ᶠ i, c i`. Positivity, finiteness (`c i ≠ 0, ∞`), and
`c i = 1` cofinitely follow automatically from the `IsAddHaarMeasure` and normalization
hypotheses. -/]
theorem restrictedHaar_smul (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) (c : ι → ℝ≥0∞)
    [∀ i, (c i • μ i).IsHaarMeasure] (hμ' : ∀ᶠ i in cofinite, (c i • μ i) (B i) = 1) :
    restrictedHaar (B := B) (fun i ↦ c i • μ i) hμ' =
      (∏ᶠ i, c i) • restrictedHaar (B := B) μ hμ := by
  classical
  have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    locallyCompactSpace_of_isMulLeftInvariant μ (hμ.mono fun _ hi ↦ by simp [hi])
  have hc0 : ∀ i, c i ≠ 0 := fun i h0 ↦ by
    obtain ⟨K, _, hKnhds⟩ := exists_compact_mem_nhds (1 : G i)
    have : (c i • μ i) K = 0 := by simp [h0]
    exact (measure_pos_of_mem_nhds (c i • μ i) hKnhds).ne' this
  have hctop : ∀ i, c i ≠ ∞ := fun i htop ↦ by
    obtain ⟨K, hKcomp, hKnhds⟩ := exists_compact_mem_nhds (1 : G i)
    have hμ0 : μ i K ≠ 0 := (measure_pos_of_mem_nhds (μ i) hKnhds).ne'
    have : (c i • μ i) K = ∞ := by simp [smul_apply, htop, ENNReal.top_mul hμ0]
    exact hKcomp.measure_lt_top.ne this
  have hc1 : ∀ᶠ i in cofinite, c i = 1 := by
    filter_upwards [hμ, hμ'] with i h1 h2
    simpa [smul_apply, smul_eq_mul, h1] using h2
  have hcfin : (Function.mulSupport c).Finite := (mem_cofinite.mp hc1).subset fun _ hi ↦ hi
  have hprod0 : (∏ᶠ i, c i) ≠ 0 := by
    rw [finprod_eq_prod _ hcfin]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ hc0 i
  have hprodtop : (∏ᶠ i, c i) ≠ ∞ := by
    rw [finprod_eq_prod _ hcfin]
    exact ENNReal.prod_ne_top fun i _ ↦ hctop i
  have : ((∏ᶠ i, c i) • restrictedHaar (B := B) μ hμ).IsHaarMeasure :=
    IsHaarMeasure.smul _ hprod0 hprodtop
  symm
  refine eq_restrictedHaar_of_box (fun i ↦ c i • μ i) hμ' _ fun C hCm hCB ↦ ?_
  rw [smul_apply, smul_eq_mul, restrictedHaar_box μ hμ hCm hCB]
  have hCfin : (Function.mulSupport fun i ↦ μ i (C i)).Finite := by
    refine (mem_cofinite.mp (hCB.and hμ)).subset fun i hi ⟨hCi, hμi⟩ ↦ ?_
    exact hi (by simp [hCi, hμi])
  rw [← finprod_mul_distrib hcfin hCfin]
  rfl

/-- Rescaling a single local Haar measure `μ i₀` by `c` scales `restrictedHaar` by `c`. -/
@[to_additive restrictedAddHaar_smul_single /-- Rescaling a single local additive Haar measure
`μ i₀` by `c` scales `restrictedAddHaar` by `c`. -/]
theorem restrictedHaar_smul_single [DecidableEq ι] (μ : ∀ i, Measure (G i))
    [∀ i, (μ i).IsHaarMeasure] (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1)
    (i₀ : ι) (c : ℝ≥0∞) [∀ i, (Function.update μ i₀ (c • μ i₀) i).IsHaarMeasure]
    (hμ' : ∀ᶠ i in cofinite, Function.update μ i₀ (c • μ i₀) i (B i) = 1) :
    restrictedHaar (B := B) (Function.update μ i₀ (c • μ i₀)) hμ' =
      c • restrictedHaar (B := B) μ hμ := by
  let cfun : ι → ℝ≥0∞ := Function.update (fun _ ↦ 1) i₀ c
  have heq : ∀ i, Function.update μ i₀ (c • μ i₀) i = cfun i • μ i := fun i ↦ by
    by_cases hi : i = i₀
    · subst hi; simp [cfun]
    · simp [cfun, hi]
  have : ∀ i, (cfun i • μ i).IsHaarMeasure := fun i ↦ by
    rw [← heq i]; infer_instance
  have hμ'' : ∀ᶠ i in cofinite, (cfun i • μ i) (B i) = 1 := by
    filter_upwards [hμ'] with i hi
    rwa [← heq i]
  have hfp : (∏ᶠ i, cfun i) = c := by
    rw [finprod_eq_single _ i₀ fun i hi ↦ by simp [cfun, hi]]
    simp [cfun]
  calc
    restrictedHaar (B := B) (Function.update μ i₀ (c • μ i₀)) hμ'
      = restrictedHaar (B := B) (fun i ↦ cfun i • μ i) hμ'' :=
        restrictedHaar_congr hμ' hμ'' heq
    _ = (∏ᶠ i, cfun i) • restrictedHaar (B := B) μ hμ :=
        restrictedHaar_smul μ hμ cfun hμ''
    _ = c • restrictedHaar (B := B) μ hμ := by rw [hfp]

/-! ### Lower bounds and infinite mass for non-cofinite boxes -/

/-- If `μ i (B i) = 1` and `B i ⊆ C i` for all `i ∉ T`, then `∏ i ∈ T, μ i (C i)` is a lower bound
for `restrictedHaar μ hμ {x | ∀ i, x i ∈ C i}`. -/
@[to_additive finset_prod_le_restrictedAddHaar_box /-- If `μ i (B i) = 1` and `B i ⊆ C i` for all
`i ∉ T`, then `∏ i ∈ T, μ i (C i)` is a lower bound for
`restrictedAddHaar μ hμ {x | ∀ i, x i ∈ C i}`. -/]
theorem finset_prod_le_restrictedHaar_box (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) {C : ∀ i, Set (G i)} (hCm : ∀ i, MeasurableSet (C i))
    (T : Finset ι) (hT : ∀ i ∉ T, μ i (B i) = 1) (hBC : ∀ i ∉ T, (B i : Set (G i)) ⊆ C i) :
    ∏ i ∈ T, μ i (C i) ≤ restrictedHaar (B := B) μ hμ {x | ∀ i, x i ∈ C i} := by
  classical
  let D : ∀ i, Set (G i) := fun i ↦ if i ∈ T then C i else B i
  have hDm : ∀ i, MeasurableSet (D i) := fun i ↦ by
    by_cases hi : i ∈ T
    · simpa [D, hi] using hCm i
    · simpa [D, hi] using (hBopen.out i).measurableSet
  have hDB : ∀ᶠ i in cofinite, D i = B i := by
    filter_upwards [T.finite_toSet.compl_mem_cofinite] with i hi
    have hi' : i ∉ T := hi
    simp [D, hi']
  have hsub : {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ D i} ⊆ {x | ∀ i, x i ∈ C i} := fun x hx i ↦ by
    by_cases hi : i ∈ T
    · simpa [D, hi] using hx i
    · exact hBC i hi (by simpa [D, hi] using hx i)
  calc
    ∏ i ∈ T, μ i (C i) = ∏ i ∈ T, μ i (D i) :=
      Finset.prod_congr rfl fun i hi ↦ by simp [D, hi]
    _ = ∏ᶠ i, μ i (D i) := by
      symm
      exact finprod_eq_prod_of_mulSupport_subset _ fun i hi ↦ by
        by_contra hiT
        have hiT' : i ∉ T := hiT
        exact hi (by simp [D, hiT', hT i hiT'])
    _ = restrictedHaar (B := B) μ hμ {x | ∀ i, x i ∈ D i} :=
      (restrictedHaar_box μ hμ hDm hDB).symm
    _ ≤ restrictedHaar (B := B) μ hμ {x | ∀ i, x i ∈ C i} :=
      measure_mono hsub

/-- Divergence criterion: if `C i ⊇ B i` everywhere and the finite products `∏ i ∈ T, μ i (C i)`
have supremum `∞` over `T : Finset ι`, then the box `{x | ∀ i, x i ∈ C i}` has infinite measure
under `restrictedHaar μ hμ`. -/
@[to_additive /-- Divergence criterion: if `C i ⊇ B i` everywhere and the finite products
`∏ i ∈ T, μ i (C i)` have supremum `∞` over `T : Finset ι`, then the box `{x | ∀ i, x i ∈ C i}`
has infinite measure under `restrictedAddHaar μ hμ`. -/]
theorem restrictedHaar_box_eq_top_of_iSup_eq_top (μ : ∀ i, Measure (G i))
    [∀ i, (μ i).IsHaarMeasure] (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) {C : ∀ i, Set (G i)}
    (hCm : ∀ i, MeasurableSet (C i)) (hBC : ∀ i, (B i : Set (G i)) ⊆ C i)
    (hsup : ⨆ T : Finset ι, ∏ i ∈ T, μ i (C i) = ∞) :
    restrictedHaar (B := B) μ hμ {x | ∀ i, x i ∈ C i} = ∞ := by
  classical
  set S₀ := badFinset (B := B) μ hμ
  let m : ℝ≥0∞ := ∏ i ∈ S₀, min (μ i (B i)) 1
  have hm0 : m ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦
    (lt_min ((hBopen.out i).measure_pos (μ i) ⟨1, one_mem (B i)⟩) one_pos).ne'
  have hle (T : Finset ι) :
      m * ∏ i ∈ T, μ i (C i) ≤ restrictedHaar (B := B) μ hμ {x | ∀ i, x i ∈ C i} := by
    have h1 : m ≤ ∏ i ∈ S₀ \ T, min (μ i (B i)) 1 := by
      dsimp only [m]
      rw [← Finset.prod_sdiff (Finset.sdiff_subset (s := S₀) (t := T))]
      exact mul_le_of_le_one_left' (Finset.prod_le_one fun _ _ ↦ min_le_right _ _)
    have h2 : ∏ i ∈ S₀ \ T, min (μ i (B i)) 1 ≤ ∏ i ∈ S₀ \ T, μ i (C i) :=
      Finset.prod_le_prod fun i _ ↦ (min_le_left _ _).trans (measure_mono (hBC i))
    calc m * ∏ i ∈ T, μ i (C i)
        ≤ (∏ i ∈ S₀ \ T, μ i (C i)) * ∏ i ∈ T, μ i (C i) := by gcongr; exact h1.trans h2
      _ = ∏ i ∈ T ∪ S₀, μ i (C i) := by
          rw [mul_comm, ← Finset.prod_union disjoint_sdiff_self_right,
            Finset.union_sdiff_self_eq_union]
      _ ≤ restrictedHaar (B := B) μ hμ {x | ∀ i, x i ∈ C i} :=
          finset_prod_le_restrictedHaar_box μ hμ hCm (T ∪ S₀)
            (fun i hi ↦ measure_eq_one_of_notMem_badFinset fun h ↦
              hi (Finset.mem_union_right _ h))
            (fun i _ ↦ hBC i)
  have htop : m * ∞ ≤ restrictedHaar (B := B) μ hμ {x | ∀ i, x i ∈ C i} := by
    rw [← hsup, ENNReal.mul_iSup]
    exact iSup_le hle
  rw [ENNReal.mul_top hm0] at htop
  exact top_le_iff.mp htop

end Main

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import TauCeti.MeasureTheory.Constructions.BorelSpace.RestrictedProduct
public import TauCeti.Probability.ProductMeasure
import TauCeti.MeasureTheory.Group.Arithmetic
import TauCeti.MeasureTheory.Group.OpenSubgroup.Basic
import TauCeti.MeasureTheory.Measure.Haar.Unique
import TauCeti.MeasureTheory.Measure.Subtype
import TauCeti.Topology.Algebra.Group.Basic
import TauCeti.Topology.Bases

/-!
# Restricted products of Haar measures

Let `(G i)` be a countable family of second-countable locally compact Borel groups, `(B i)` a family
of open subgroups, and `μ i` a Haar measure on each `G i` normalized so that `μ i (B i) = 1` for all
but finitely many `i`. Because an open subgroup of finite left-invariant open-positive measure in a
weakly locally compact group is automatically compact
(`MeasureTheory.isCompact_of_isOpen_of_measure_ne_top_of_isMulLeftInvariant`), cofinitely many
`B i` are compact and `Πʳ i, [G i, B i]` is locally compact
(`locallyCompactSpace_restrictedProduct_of_measure_ne_top_of_isMulLeftInvariant`).

For any finite index set `S : Finset ι` containing `{i | μ i (B i) ≠ 1}`, the principal piece
`{x : Πʳ i, [G i, B i] | ∀ i ∉ S, x i ∈ B i}` is openly embedded as the topological group product
`(∀ i : S, G i) × (∀ i : {i // i ∉ S}, B i)` via `restrictedProductPrincipalPieceInclusion B S`. On
that product, `restrictedPrincipalPieceMeasure B S μ` combines the finite product Haar measure
`Measure.pi (fun i : S ↦ μ i)` with the infinite product probability Haar measure
`Measure.infinitePi (fun j : {i // i ∉ S} ↦ (μ j).comap (↑))`.

Choosing the reference set `S₀ = {i | μ i (B i) ≠ 1}`, we rescale an arbitrary Haar measure on the
locally compact group `Πʳ i, [G i, B i]` by `Measure.haarScalarFactor` so that its pullback to the
`S₀`-principal piece coincides with `restrictedPrincipalPieceMeasure B S₀ μ`. This defines
`restrictedHaar B μ hμ` (additively `restrictedAddHaar`), which is registered as a Haar, regular,
locally finite, and σ-finite measure (`isHaarMeasure_restrictedHaar`, `regular_restrictedHaar`,
`isLocallyFiniteMeasure_restrictedHaar`, `sigmaFinite_restrictedHaar`). Haar uniqueness on every
principal piece then yields:

* **Principal-piece compatibility** (`comap_restrictedHaar_principalPieceInclusion`,
  `measurePreserving_restrictedHaar_principalPieceInclusion`): for *every* finite set `S` outside
  which `μ i (B i) = 1`, pulling `restrictedHaar B μ hμ` back along
  `restrictedProductPrincipalPieceInclusion B S` recovers `restrictedPrincipalPieceMeasure B S μ`.
* **Box formula** (`restrictedHaar_box`, `restrictedHaar_restrictedProductBox`): for any coordinate
  sets `C i ⊆ G i` (without measurability assumptions) satisfying `C i = B i` cofinitely,
  `restrictedHaar B μ hμ {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i)`.
* **Existence and uniqueness** (`eq_restrictedHaar_of_box`, `exists_unique_restrictedHaar`,
  `exists_unique_restrictedAddHaar`): `restrictedHaar B μ hμ` is the unique Borel measure (with no
  left-invariance or compact-finiteness hypothesis needed) satisfying the box formula on open boxes,
  and in particular the unique Haar measure satisfying the box formula on measurable boxes.
* **Right and inversion invariance** (`isMulRightInvariant_restrictedHaar`,
  `isInvInvariant_restrictedHaar`): when all local factors `μ i` are right-invariant or
  inversion-invariant, so is `restrictedHaar B μ hμ`.

No Hausdorff assumption on the factors `G i` is required anywhere.

## References

* D. Ramakrishnan and R. J. Valenza, *Fourier Analysis on Number Fields*, Chapter 5.
* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, §3.3.
-/

public section

namespace TauCeti

open Filter _root_.MeasureTheory _root_.MeasureTheory.Measure Set Topology
open scoped ENNReal NNReal Pointwise RestrictedProduct

universe u v w

section PrincipalPieceDef

variable {ι : Type u} {G : ι → Type v} {K : ι → Type w}
variable [∀ i, MeasurableSpace (G i)] [∀ i, SetLike (K i) (G i)]

/-- On the principal-piece model `(∀ i : S, G i) × (∀ i : {i // i ∉ S}, B i)`, the product of the
finite product measure `Measure.pi (fun i : S ↦ μ i)` and the infinite product measure
`Measure.infinitePi (fun j : {i // i ∉ S} ↦ (μ j).comap (↑))`. -/
noncomputable def restrictedPrincipalPieceMeasure (B : ∀ i, K i) (S : Finset ι)
    (μ : ∀ i, Measure (G i)) :
    Measure ((∀ i : S, G i.1) × (∀ j : {i // i ∉ S}, B j.1)) :=
  (Measure.pi fun i : S ↦ μ i.1).prod
    (Measure.infinitePi fun j : {i // i ∉ S} ↦ (μ j.1).comap ((↑) : B j.1 → G j.1))

theorem restrictedPrincipalPieceMeasure_def (B : ∀ i, K i) (S : Finset ι)
    (μ : ∀ i, Measure (G i)) :
    restrictedPrincipalPieceMeasure B S μ =
      (Measure.pi fun i : S ↦ μ i.1).prod
        (Measure.infinitePi fun j : {i // i ∉ S} ↦ (μ j.1).comap ((↑) : B j.1 → G j.1)) :=
  (rfl)

private noncomputable def restrictedHaarRefFinset (B : ∀ i, K i) (μ : ∀ i, Measure (G i))
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) : Finset ι :=
  (eventually_cofinite.mp hμ).toFinset

private theorem measure_eq_one_of_notMem_restrictedHaarRefFinset {B : ∀ i, K i}
    {μ : ∀ i, Measure (G i)} (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1)
    {i : ι} (hi : i ∉ restrictedHaarRefFinset B μ hμ) : μ i (B i) = 1 := by
  by_contra hnot
  exact hi ((eventually_cofinite.mp hμ).mem_toFinset.mpr hnot)

end PrincipalPieceDef

section PrincipalPieceHaar

variable {ι : Type u} {G : ι → Type v} {K : ι → Type w}
variable [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, MeasurableSpace (G i)]
  [∀ i, BorelSpace (G i)] [∀ i, MeasurableMul (G i)]
  [∀ i, SetLike (K i) (G i)] [∀ i, SubgroupClass (K i) (G i)]

/-- When `B i` is open of `μ i`-mass `1` outside `S`, `restrictedPrincipalPieceMeasure B S μ` is a
Haar measure on `(∀ i : S, G i) × (∀ i : {i // i ∉ S}, B i)`. -/
@[to_additive
/-- When `B i` is open of `μ i`-mass `1` outside `S`, `restrictedPrincipalPieceMeasure B S μ` is an
additive Haar measure on `(∀ i : S, G i) × (∀ i : {i // i ∉ S}, B i)`. -/]
theorem isHaarMeasure_restrictedPrincipalPieceMeasure {B : ∀ i, K i} {S : Finset ι}
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure] [∀ i : S, SigmaFinite (μ i.1)]
    (hBopen : ∀ i ∉ S, IsOpen (B i : Set (G i))) (hμS : ∀ i ∉ S, μ i (B i) = 1) :
    (restrictedPrincipalPieceMeasure B S μ).IsHaarMeasure := by
  have : ∀ j : {i // i ∉ S}, IsProbabilityMeasure ((μ j.1).comap ((↑) : B j.1 → G j.1)) :=
    fun j ↦ (μ j.1).isProbabilityMeasure_comap_subtype (hBopen j.1 j.2).measurableSet (hμS j.1 j.2)
  have : ∀ j : {i // i ∉ S}, ((μ j.1).comap ((↑) : B j.1 → G j.1)).IsHaarMeasure := fun j ↦
    Measure.IsHaarMeasure.comap (mH := inferInstance) (μ j.1)
      (f := SubgroupClass.subtype (B j.1)) (hBopen j.1 j.2).isOpenEmbedding_subtypeVal
  rw [restrictedPrincipalPieceMeasure_def]
  infer_instance

end PrincipalPieceHaar

section LocallyCompact

/-- If `B i ≤ G i` are open subgroups of weakly locally compact topological groups with cofinitely
finite left-invariant open-positive Borel measure, then `Πʳ i, [G i, B i]` is locally compact. -/
@[to_additive
/-- If `B i ≤ G i` are open additive subgroups of weakly locally compact topological additive
groups with cofinitely finite left-invariant open-positive Borel measure, then `Πʳ i, [G i, B i]`
is locally compact. -/]
theorem locallyCompactSpace_restrictedProduct_of_measure_ne_top_of_isMulLeftInvariant
    {ι : Type u} {G : ι → Type v} {K : ι → Type w}
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    [∀ i, WeaklyLocallyCompactSpace (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
    [∀ i, SetLike (K i) (G i)] [∀ i, SubgroupClass (K i) (G i)] {B : ∀ i, K i}
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsOpenPosMeasure] [∀ i, (μ i).IsMulLeftInvariant]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) ≠ ∞) :
    LocallyCompactSpace (Πʳ i, [G i, B i]) :=
  RestrictedProduct.locallyCompactSpace_of_group G <|
    hμ.mono fun i hi ↦
      isCompact_of_isOpen_of_measure_ne_top_of_isMulLeftInvariant (hBopen.out i) (μ i) hi

end LocallyCompact

section RestrictedHaar

variable {ι : Type u} {G : ι → Type v} {K : ι → Type w}
variable [Countable ι] [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)]
  [∀ i, SecondCountableTopology (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
  [∀ i, SetLike (K i) (G i)] [∀ i, SubgroupClass (K i) (G i)]

@[to_additive]
private noncomputable def restrictedHaarAux (B : ∀ i, K i)
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    [LocallyCompactSpace (Πʳ i, [G i, B i])]
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (S₀ : Finset ι) (hμS₀ : ∀ i ∉ S₀, μ i (B i) = 1) :
    Measure (Πʳ i, [G i, B i]) :=
  have : (restrictedPrincipalPieceMeasure B S₀ μ).IsHaarMeasure :=
    isHaarMeasure_restrictedPrincipalPieceMeasure μ (fun i _ ↦ hBopen.out i) hμS₀
  let ν₀ : Measure (Πʳ i, [G i, B i]) := Measure.haar
  have : (ν₀.comap (restrictedProductPrincipalPieceInclusion B S₀)).IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := inferInstance) ν₀
      (isOpenEmbedding_restrictedProductPrincipalPieceInclusion B S₀ fun i _ ↦ hBopen.out i)
  haarScalarFactor (restrictedPrincipalPieceMeasure B S₀ μ)
    (ν₀.comap (restrictedProductPrincipalPieceInclusion B S₀)) • ν₀

@[to_additive]
private theorem isHaarMeasure_restrictedHaarAux {B : ∀ i, K i}
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    [LocallyCompactSpace (Πʳ i, [G i, B i])]
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (S₀ : Finset ι) (hμS₀ : ∀ i ∉ S₀, μ i (B i) = 1) :
    (restrictedHaarAux B μ S₀ hμS₀).IsHaarMeasure := by
  have hemb₀ := isOpenEmbedding_restrictedProductPrincipalPieceInclusion B S₀
    fun i _ ↦ hBopen.out i
  have : LocallyCompactSpace _ := hemb₀.locallyCompactSpace
  have : (restrictedPrincipalPieceMeasure B S₀ μ).IsHaarMeasure :=
    isHaarMeasure_restrictedPrincipalPieceMeasure μ (fun i _ ↦ hBopen.out i) hμS₀
  have : ((Measure.haar : Measure (Πʳ i, [G i, B i])).comap
      (restrictedProductPrincipalPieceInclusion B S₀)).IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := inferInstance) Measure.haar hemb₀
  rw [restrictedHaarAux]
  exact IsHaarMeasure.nnreal_smul Measure.haar (haarScalarFactor_pos_of_isHaarMeasure _ _).ne'

@[to_additive]
private theorem regular_restrictedHaarAux {B : ∀ i, K i}
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    [LocallyCompactSpace (Πʳ i, [G i, B i])]
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (S₀ : Finset ι) (hμS₀ : ∀ i ∉ S₀, μ i (B i) = 1) :
    (restrictedHaarAux B μ S₀ hμS₀).Regular := by
  rw [restrictedHaarAux]
  infer_instance

@[to_additive]
private theorem comap_restrictedHaarAux_self {B : ∀ i, K i}
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    [LocallyCompactSpace (Πʳ i, [G i, B i])]
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (S₀ : Finset ι) (hμS₀ : ∀ i ∉ S₀, μ i (B i) = 1) :
    (restrictedHaarAux B μ S₀ hμS₀).comap (restrictedProductPrincipalPieceInclusion B S₀) =
      restrictedPrincipalPieceMeasure B S₀ μ := by
  have hemb₀ := isOpenEmbedding_restrictedProductPrincipalPieceInclusion B S₀
    fun i _ ↦ hBopen.out i
  have : LocallyCompactSpace _ := hemb₀.locallyCompactSpace
  have : (restrictedPrincipalPieceMeasure B S₀ μ).IsHaarMeasure :=
    isHaarMeasure_restrictedPrincipalPieceMeasure μ (fun i _ ↦ hBopen.out i) hμS₀
  have : ((Measure.haar : Measure (Πʳ i, [G i, B i])).comap
      (restrictedProductPrincipalPieceInclusion B S₀)).IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := inferInstance) Measure.haar hemb₀
  rw [restrictedHaarAux, ← Measure.coe_nnreal_smul, Measure.comap_smul, Measure.coe_nnreal_smul]
  exact (isMulLeftInvariant_eq_smul (restrictedPrincipalPieceMeasure B S₀ μ)
    ((Measure.haar : Measure (Πʳ i, [G i, B i])).comap
      (restrictedProductPrincipalPieceInclusion B S₀))).symm

/-- **Restricted product of Haar measures.** Given open subgroups `B i ≤ G i` and local Haar
measures `μ i` satisfying `μ i (B i) = 1` cofinitely, this is the unique Haar measure on
`Πʳ i, [G i, B i]` assigning mass `∏ᶠ i, μ i (C i)` to every coordinate box `{x | ∀ i, x i ∈ C i}`
with `C i = B i` cofinitely. -/
@[to_additive
/-- **Restricted product of additive Haar measures.** Given open additive subgroups `B i ≤ G i` and
local additive Haar measures `μ i` satisfying `μ i (B i) = 1` cofinitely, this is the unique
additive Haar measure on `Πʳ i, [G i, B i]` assigning mass `∏ᶠ i, μ i (C i)` to every coordinate box
`{x | ∀ i, x i ∈ C i}` with `C i = B i` cofinitely. -/]
noncomputable def restrictedHaar (B : ∀ i, K i) [Fact (∀ i, IsOpen (B i : Set (G i)))]
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    Measure (Πʳ i, [G i, B i]) :=
  have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    locallyCompactSpace_restrictedProduct_of_measure_ne_top_of_isMulLeftInvariant μ
      (hμ.mono fun _ hi ↦ by simp [hi])
  restrictedHaarAux B μ (restrictedHaarRefFinset B μ hμ)
    fun _ ↦ measure_eq_one_of_notMem_restrictedHaarRefFinset hμ

section Properties

variable {B : ∀ i, K i} [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]

/-- Helper evaluating `restrictedPrincipalPieceMeasure B S μ` on the preimage of a box `C`
satisfying `C i ⊆ B i` for all `i` and `C i = B i` outside a finite superset `F ⊇ S`. -/
@[to_additive addRestrictedPrincipalPieceMeasure_preimage_box_of_subset]
private theorem restrictedPrincipalPieceMeasure_preimage_box_of_subset
    {S F : Finset ι} (hSF : S ⊆ F) (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμS : ∀ i ∉ S, μ i (B i) = 1) {C : ∀ i, Set (G i)}
    (hCB_sub : ∀ i, C i ⊆ B i) (hCBF : ∀ i ∉ F, C i = B i) :
    restrictedPrincipalPieceMeasure B S μ
      (restrictedProductPrincipalPieceInclusion B S ⁻¹'
        restrictedProductBox (fun i ↦ (B i : Set (G i))) cofinite C) =
      ∏ i ∈ F, μ i (C i) := by
  classical
  have : ∀ j : {i // i ∉ S}, IsProbabilityMeasure ((μ j.1).comap ((↑) : B j.1 → G j.1)) :=
    fun j ↦ (μ j.1).isProbabilityMeasure_comap_subtype (hBopen.out j.1).measurableSet (hμS j.1 j.2)
  let T : Finset {i // i ∉ S} := F.subtype (fun i ↦ i ∉ S)
  have hpi : (Set.univ.pi fun j : {i // i ∉ S} ↦ ((↑) : B j.1 → G j.1) ⁻¹' C j.1) =
      (T : Set {i // i ∉ S}).pi fun j ↦ ((↑) : B j.1 → G j.1) ⁻¹' C j.1 := by
    ext q
    simp only [Set.mem_pi, mem_univ, mem_preimage, forall_true_left, Finset.mem_coe, T,
      Finset.mem_subtype]
    refine ⟨fun h j _ ↦ h j, fun h j ↦ ?_⟩
    by_cases hjF : j.1 ∈ F
    · exact h j hjF
    · rw [hCBF j.1 hjF]
      exact (q j).2
  rw [preimage_restrictedProductPrincipalPieceInclusion_box, hpi,
    restrictedPrincipalPieceMeasure_def, prod_prod, pi_pi, infinitePi_pi',
    Finset.univ_eq_attach, Finset.prod_attach S fun i ↦ μ i (C i)]
  have hT : (∏ j ∈ T, (μ j.1).comap ((↑) : B j.1 → G j.1) (((↑) : B j.1 → G j.1) ⁻¹' C j.1)) =
      ∏ j ∈ T, μ j.1 (C j.1) := by
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    have hemb : MeasurableEmbedding ((↑) : B j.1 → G j.1) :=
      MeasurableEmbedding.subtype_coe (hBopen.out j.1).measurableSet
    rw [hemb.comap_preimage, Subtype.range_coe_subtype, SetLike.setOfPred_mem_eq,
      inter_eq_self_of_subset_left (hCB_sub j.1)]
  have hSF' : S = F.filter (· ∈ S) := by
    ext x
    simp only [Finset.mem_filter, iff_and_self]
    exact fun hx ↦ hSF hx
  rw [hT]
  dsimp only [T]
  rw [Finset.prod_subtype_eq_prod_filter (fun i ↦ μ i (C i)),
    congrArg (fun A : Finset ι ↦ ∏ x ∈ A, μ x (C x)) hSF',
    Finset.prod_filter_mul_prod_filter_not]

variable [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]

/-- `restrictedHaar B μ hμ` is a Haar measure on `Πʳ i, [G i, B i]`. -/
@[to_additive /-- `restrictedAddHaar B μ hμ` is an additive Haar measure on `Πʳ i, [G i, B i]`. -/]
instance isHaarMeasure_restrictedHaar
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    (restrictedHaar B μ hμ).IsHaarMeasure := by
  have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    locallyCompactSpace_restrictedProduct_of_measure_ne_top_of_isMulLeftInvariant μ
      (hμ.mono fun _ hi ↦ by simp [hi])
  rw [restrictedHaar]
  exact isHaarMeasure_restrictedHaarAux μ _ _

/-- `restrictedHaar B μ hμ` is a regular Borel measure on `Πʳ i, [G i, B i]`. -/
@[to_additive
/-- `restrictedAddHaar B μ hμ` is a regular Borel measure on `Πʳ i, [G i, B i]`. -/]
instance regular_restrictedHaar
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    (restrictedHaar B μ hμ).Regular := by
  have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    locallyCompactSpace_restrictedProduct_of_measure_ne_top_of_isMulLeftInvariant μ
      (hμ.mono fun _ hi ↦ by simp [hi])
  rw [restrictedHaar]
  exact regular_restrictedHaarAux μ _ _

/-- `restrictedHaar B μ hμ` is a locally finite measure on `Πʳ i, [G i, B i]`. -/
@[to_additive
/-- `restrictedAddHaar B μ hμ` is a locally finite measure on `Πʳ i, [G i, B i]`. -/]
instance isLocallyFiniteMeasure_restrictedHaar
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    IsLocallyFiniteMeasure (restrictedHaar B μ hμ) := by
  have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    locallyCompactSpace_restrictedProduct_of_measure_ne_top_of_isMulLeftInvariant μ
      (hμ.mono fun _ hi ↦ by simp [hi])
  infer_instance

/-- `restrictedHaar B μ hμ` is a σ-finite measure on `Πʳ i, [G i, B i]`. -/
@[to_additive /-- `restrictedAddHaar B μ hμ` is a σ-finite measure on `Πʳ i, [G i, B i]`. -/]
instance sigmaFinite_restrictedHaar
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    SigmaFinite (restrictedHaar B μ hμ) := by
  have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    locallyCompactSpace_restrictedProduct_of_measure_ne_top_of_isMulLeftInvariant μ
      (hμ.mono fun _ hi ↦ by simp [hi])
  infer_instance

/-- **Principal-piece compatibility.** For any finite set `S : Finset ι` outside which
`μ i (B i) = 1`, pulling `restrictedHaar B μ hμ` back along
`restrictedProductPrincipalPieceInclusion B S` yields `restrictedPrincipalPieceMeasure B S μ`. -/
@[to_additive
/-- **Principal-piece compatibility.** For any finite set `S : Finset ι` outside which
`μ i (B i) = 1`, pulling `restrictedAddHaar B μ hμ` back along
`addRestrictedProductPrincipalPieceInclusion B S` yields
`restrictedPrincipalPieceMeasure B S μ`. -/]
theorem comap_restrictedHaar_principalPieceInclusion
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1)
    {S : Finset ι} (hμS : ∀ i ∉ S, μ i (B i) = 1) :
    (restrictedHaar B μ hμ).comap (restrictedProductPrincipalPieceInclusion B S) =
      restrictedPrincipalPieceMeasure B S μ := by
  classical
  have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    locallyCompactSpace_restrictedProduct_of_measure_ne_top_of_isMulLeftInvariant μ
      (hμ.mono fun _ hi ↦ by simp [hi])
  let S₀ : Finset ι := restrictedHaarRefFinset B μ hμ
  have hμS₀ : ∀ i ∉ S₀, μ i (B i) = 1 := fun _ ↦
    measure_eq_one_of_notMem_restrictedHaarRefFinset hμ
  have hemb₀ := isOpenEmbedding_restrictedProductPrincipalPieceInclusion B S₀
    fun i _ ↦ hBopen.out i
  have hemb := isOpenEmbedding_restrictedProductPrincipalPieceInclusion B S
    fun i _ ↦ hBopen.out i
  have : LocallyCompactSpace ((∀ i : S, G i.1) × (∀ j : {i // i ∉ S}, B j.1)) :=
    hemb.locallyCompactSpace
  have : (restrictedPrincipalPieceMeasure B S μ).IsHaarMeasure :=
    isHaarMeasure_restrictedPrincipalPieceMeasure μ (fun i _ ↦ hBopen.out i) hμS
  have : ((restrictedHaar B μ hμ).comap
      (restrictedProductPrincipalPieceInclusion B S)).IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := inferInstance) (restrictedHaar B μ hμ) hemb
  -- Choose compact identity neighbourhoods `L i ⊆ B i` to build a positive finite-mass test box
  -- supported on `S ∪ S₀` and lying inside both the `S`- and `S₀`-principal pieces.
  choose L hLnhds hLB hLcomp using
    fun i ↦ local_compact_nhds ((hBopen.out i).mem_nhds (one_mem (B i)))
  let C : ∀ i, Set (G i) := fun i ↦ if i ∈ S ∪ S₀ then L i else B i
  have hCB_sub : ∀ i, C i ⊆ B i := fun i ↦ by
    dsimp only [C]; split_ifs; exacts [hLB i, Subset.rfl]
  have hCBF : ∀ i ∉ S ∪ S₀, C i = B i := fun _ hi ↦ ite_eq_right hi
  have hpos : ∏ i ∈ S ∪ S₀, μ i (C i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i hi ↦ by
    simpa only [C, ite_eq_left hi] using (measure_pos_of_mem_nhds (μ i) (hLnhds i)).ne'
  have htop : ∏ i ∈ S ∪ S₀, μ i (C i) ≠ ∞ := (WithTop.prod_lt_top fun i hi ↦ by
    dsimp only [C]
    rw [ite_eq_left hi]
    exact (hLcomp i).measure_lt_top).ne
  let box := restrictedProductBox (fun i ↦ (B i : Set (G i))) cofinite C
  have hbox_sub : ∀ T : Finset ι,
      box ⊆ Set.range (restrictedProductPrincipalPieceInclusion B T) := fun T ↦ by
    rw [range_restrictedProductPrincipalPieceInclusion]
    exact fun x hx i _ ↦ hCB_sub i (mem_restrictedProductBox.mp hx i)
  have hevalS : restrictedPrincipalPieceMeasure B S μ
      (restrictedProductPrincipalPieceInclusion B S ⁻¹' box) = ∏ i ∈ S ∪ S₀, μ i (C i) :=
    restrictedPrincipalPieceMeasure_preimage_box_of_subset Finset.subset_union_left μ hμS
      hCB_sub hCBF
  refine isMulLeftInvariant_eq_of_measure_eq_of_regular _ _
    (s := restrictedProductPrincipalPieceInclusion B S ⁻¹' box) ?_
    (hevalS.symm ▸ hpos) (hevalS.symm ▸ htop)
  rw [hemb.measurableEmbedding.comap_preimage, inter_eq_self_of_subset_left (hbox_sub S), hevalS]
  rw [← inter_eq_self_of_subset_left (hbox_sub S₀), ← hemb₀.measurableEmbedding.comap_preimage,
    restrictedHaar, comap_restrictedHaarAux_self,
    restrictedPrincipalPieceMeasure_preimage_box_of_subset Finset.subset_union_right μ hμS₀
      hCB_sub hCBF]

/-- For any finite set `S : Finset ι` outside which `μ i (B i) = 1`,
`restrictedProductPrincipalPieceInclusion B S` is measure-preserving from
`restrictedPrincipalPieceMeasure B S μ` onto
`(restrictedHaar B μ hμ).restrict {x | ∀ i ∉ S, x i ∈ B i}`. -/
@[to_additive
/-- For any finite set `S : Finset ι` outside which `μ i (B i) = 1`,
`addRestrictedProductPrincipalPieceInclusion B S` is measure-preserving from
`restrictedPrincipalPieceMeasure B S μ` onto
`(restrictedAddHaar B μ hμ).restrict {x | ∀ i ∉ S, x i ∈ B i}`. -/]
theorem measurePreserving_restrictedHaar_principalPieceInclusion
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1)
    {S : Finset ι} (hμS : ∀ i ∉ S, μ i (B i) = 1) :
    MeasurePreserving (restrictedProductPrincipalPieceInclusion B S)
      (restrictedPrincipalPieceMeasure B S μ)
      ((restrictedHaar B μ hμ).restrict {x | ∀ i ∉ S, x i ∈ B i}) := by
  have hemb : IsOpenEmbedding (restrictedProductPrincipalPieceInclusion B S) :=
    isOpenEmbedding_restrictedProductPrincipalPieceInclusion B S fun i _ ↦ hBopen.out i
  refine ⟨hemb.continuous.measurable, ?_⟩
  rw [← comap_restrictedHaar_principalPieceInclusion μ hμ hμS,
    hemb.measurableEmbedding.map_comap, range_restrictedProductPrincipalPieceInclusion]

/-- **Box formula for `restrictedHaar`** (`restrictedProductBox` form), requiring no measurability
hypothesis on the coordinate sets `C i`. -/
@[to_additive
/-- **Box formula for `restrictedAddHaar`** (`restrictedProductBox` form), requiring no
measurability hypothesis on the coordinate sets `C i`. -/]
theorem restrictedHaar_restrictedProductBox
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1)
    {C : ∀ i, Set (G i)} (hCB : ∀ᶠ i in cofinite, C i = B i) :
    restrictedHaar B μ hμ
      (restrictedProductBox (fun i ↦ (B i : Set (G i))) cofinite C) =
      ∏ᶠ i, μ i (C i) := by
  classical
  let hfin : {i | ¬ (μ i (B i) = 1 ∧ C i = B i)}.Finite := eventually_cofinite.mp (hμ.and hCB)
  let S : Finset ι := hfin.toFinset
  have hμS : ∀ i ∉ S, μ i (B i) = 1 := fun i hi ↦ by
    by_contra hnot
    exact hi (hfin.mem_toFinset.mpr fun h ↦ hnot h.1)
  have hCBS : ∀ i ∉ S, C i = B i := fun i hi ↦ by
    by_contra hnot
    exact hi (hfin.mem_toFinset.mpr fun h ↦ hnot h.2)
  have hemb : IsOpenEmbedding (restrictedProductPrincipalPieceInclusion B S) :=
    isOpenEmbedding_restrictedProductPrincipalPieceInclusion B S fun i _ ↦ hBopen.out i
  let box := restrictedProductBox (fun i ↦ (B i : Set (G i))) cofinite C
  have hbox_sub : box ⊆ Set.range (restrictedProductPrincipalPieceInclusion B S) := by
    rw [range_restrictedProductPrincipalPieceInclusion]
    intro x hx i hi
    rw [← SetLike.mem_coe, ← hCBS i hi]
    exact mem_restrictedProductBox.mp hx i
  have : ∀ j : {i // i ∉ S}, IsProbabilityMeasure ((μ j.1).comap ((↑) : B j.1 → G j.1)) :=
    fun j ↦ (μ j.1).isProbabilityMeasure_comap_subtype (hBopen.out j.1).measurableSet (hμS j.1 j.2)
  calc restrictedHaar B μ hμ box
      = restrictedHaar B μ hμ
          (box ∩ Set.range (restrictedProductPrincipalPieceInclusion B S)) :=
        (congrArg _ (inter_eq_self_of_subset_left hbox_sub)).symm
    _ = ((restrictedHaar B μ hμ).comap (restrictedProductPrincipalPieceInclusion B S))
          (restrictedProductPrincipalPieceInclusion B S ⁻¹' box) :=
        (hemb.measurableEmbedding.comap_preimage _ _).symm
    _ = restrictedPrincipalPieceMeasure B S μ
          ((Set.univ.pi fun i : S ↦ C i.1) ×ˢ Set.univ) := by
        rw [comap_restrictedHaar_principalPieceInclusion μ hμ hμS,
          preimage_restrictedProductPrincipalPieceInclusion_box_of_subset B S
            fun i hi ↦ (hCBS i hi).symm.subset]
    _ = ∏ i ∈ S, μ i (C i) := by
        rw [restrictedPrincipalPieceMeasure_def, prod_prod, measure_univ, mul_one, pi_pi,
          Finset.univ_eq_attach, Finset.prod_attach S fun i ↦ μ i (C i)]
    _ = ∏ᶠ i, μ i (C i) := by
        symm
        refine finprod_eq_prod_of_mulSupport_subset _ (s := S) fun i hi ↦ ?_
        by_contra hiS
        exact hi (by dsimp only; rw [hCBS i hiS, hμS i hiS])

/-- **Box formula for `restrictedHaar`** in set-builder notation: for any family
`C : ∀ i, Set (G i)` satisfying `C i = B i` cofinitely,
`restrictedHaar B μ hμ {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i)`. -/
@[to_additive
/-- **Box formula for `restrictedAddHaar`** in set-builder notation: for any family
`C : ∀ i, Set (G i)` satisfying `C i = B i` cofinitely,
`restrictedAddHaar B μ hμ {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i)`. -/]
theorem restrictedHaar_box
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1)
    {C : ∀ i, Set (G i)} (hCB : ∀ᶠ i in cofinite, C i = B i) :
    restrictedHaar B μ hμ {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i) := by
  rw [← restrictedProductBox_def (fun i ↦ (B i : Set (G i))) cofinite C]
  exact restrictedHaar_restrictedProductBox μ hμ hCB

/-- **Uniqueness of `restrictedHaar`.** Any Borel measure on `Πʳ i, [G i, B i]` that gives every
open coordinate box `{x | ∀ i, x i ∈ C i}` with `C i = B i` cofinitely the mass `∏ᶠ i, μ i (C i)`
equals `restrictedHaar B μ hμ`. -/
@[to_additive
/-- **Uniqueness of `restrictedAddHaar`.** Any Borel measure on `Πʳ i, [G i, B i]` that gives every
open coordinate box `{x | ∀ i, x i ∈ C i}` with `C i = B i` cofinitely the mass `∏ᶠ i, μ i (C i)`
equals `restrictedAddHaar B μ hμ`. -/]
theorem eq_restrictedHaar_of_box
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1)
    {ν : Measure (Πʳ i, [G i, B i])}
    (hν : ∀ C : ∀ i, Set (G i), (∀ i, IsOpen (C i)) →
      (∀ᶠ i in cofinite, C i = B i) → ν {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i)) :
    ν = restrictedHaar B μ hμ := by
  classical
  let A : ∀ i, Set (G i) := fun i ↦ (B i : Set (G i))
  let S : Set (Set (Πʳ i, [G i, B i])) := openRestrictedProductBoxes A
  have h_eq : ∀ U ∈ S, ν U = restrictedHaar B μ hμ U := by
    intro U hU
    obtain ⟨C, hC, hCB, rfl⟩ := mem_openRestrictedProductBoxes.mp hU
    rw [restrictedProductBox_def, hν C hC hCB, restrictedHaar_box μ hμ hCB]
  -- Cover `Πʳ i, [G i, B i]` by open coordinate boxes of finite `ν`-measure.
  let T₀ : Set (Set (Πʳ i, [G i, B i])) := {U ∈ S | ν U ≠ ∞}
  have hT₀_open : ∀ U ∈ T₀, IsOpen U := fun U hU ↦ by
    obtain ⟨C, hC, hCB, rfl⟩ := mem_openRestrictedProductBoxes.mp hU.1
    exact isOpen_restrictedProductBox hC (hCB.mono fun i hi ↦ hi.symm.subset)
  have hT₀_univ : ⋃₀ T₀ = Set.univ := by
    refine eq_univ_iff_forall.mpr fun x ↦ mem_sUnion.mpr ?_
    let hfin : {i | ¬ (x i ∈ B i ∧ μ i (B i) = 1)}.Finite := eventually_cofinite.mp (x.2.and hμ)
    let F : Finset ι := hfin.toFinset
    have hF : ∀ i ∉ F, x i ∈ B i ∧ μ i (B i) = 1 := fun i hi ↦ by
      by_contra h
      exact hi (hfin.mem_toFinset.mpr h)
    choose K hKcomp hKnhds using fun i ↦ exists_compact_mem_nhds (x i)
    let C : ∀ i, Set (G i) := fun i ↦ if i ∈ F then interior (K i) else B i
    have hCopen : ∀ i, IsOpen (C i) := fun i ↦ by
      dsimp only [C]; split_ifs; exacts [isOpen_interior, hBopen.out i]
    have hCB : ∀ᶠ i in cofinite, C i = B i := by
      filter_upwards [F.finite_toSet.compl_mem_cofinite] with i hi
      exact ite_eq_right (Finset.mem_coe.not.mp hi)
    refine ⟨restrictedProductBox A cofinite C,
      ⟨mem_openRestrictedProductBoxes.mpr ⟨C, hCopen, hCB, rfl⟩, ?_⟩, ?_⟩
    · rw [restrictedProductBox_def, hν C hCopen hCB,
        finprod_eq_prod_of_mulSupport_subset _ (s := F)]
      · refine (WithTop.prod_lt_top fun i hi ↦ ?_).ne
        dsimp only [C]
        rw [ite_eq_left hi]
        exact (measure_mono interior_subset).trans_lt (hKcomp i).measure_lt_top
      · intro i hi
        by_contra hiF
        have hiF' : i ∉ F := Finset.mem_coe.not.mp hiF
        exact hi (by dsimp only [C]; rw [ite_eq_right hiF', (hF i hiF').2])
    · refine mem_restrictedProductBox.mpr fun i ↦ ?_
      dsimp only [C]
      split_ifs with hiF
      · exact mem_interior_iff_mem_nhds.mpr (hKnhds i)
      · exact (hF i hiF).1
  -- Extract a countable subcover by second countability and apply the π-λ uniqueness theorem.
  obtain ⟨T, hTc, hTsub, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable T₀ hT₀_open
  exact Measure.ext_of_generateFrom_of_cover_subset
    (measurableSpace_restrictedProduct_eq_generateFrom_openBoxes (.of_forall hBopen.out))
    (isPiSystem_openRestrictedProductBoxes A)
    (hTsub.trans fun _ h ↦ h.1) hTc (hTU.trans hT₀_univ)
    (fun U hU ↦ (hTsub hU).2) h_eq

/-- **Existence and uniqueness of restricted-product Haar measure.** Given open subgroups
`B i ≤ G i` and local Haar measures `μ i` satisfying `μ i (B i) = 1` cofinitely, there is a unique
Haar measure on `Πʳ i, [G i, B i]` assigning mass `∏ᶠ i, μ i (C i)` to every measurable coordinate
box `{x | ∀ i, x i ∈ C i}` with `C i = B i` cofinitely. -/
@[to_additive
/-- **Existence and uniqueness of restricted-product additive Haar measure.** Given open additive
subgroups `B i ≤ G i` and local additive Haar measures `μ i` satisfying `μ i (B i) = 1` cofinitely,
there is a unique additive Haar measure on `Πʳ i, [G i, B i]` assigning mass `∏ᶠ i, μ i (C i)` to
every measurable coordinate box `{x | ∀ i, x i ∈ C i}` with `C i = B i` cofinitely. -/]
theorem exists_unique_restrictedHaar
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    ∃! ν : Measure (Πʳ i, [G i, B i]), ν.IsHaarMeasure ∧
      ∀ C : ∀ i, Set (G i), (∀ i, MeasurableSet (C i)) →
        (∀ᶠ i in cofinite, C i = B i) →
        ν {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i) :=
  ⟨restrictedHaar B μ hμ,
    ⟨inferInstance, fun _ _ hCB ↦ restrictedHaar_box μ hμ hCB⟩,
    fun _ ⟨_, hbox⟩ ↦
      eq_restrictedHaar_of_box μ hμ fun C hC hCB ↦ hbox C (fun i ↦ (hC i).measurableSet) hCB⟩

/-- When all local Haar measures `μ i` are right-invariant, so is `restrictedHaar B μ hμ`. -/
@[to_additive
/-- When all local additive Haar measures `μ i` are right-invariant, so is
`restrictedAddHaar B μ hμ`. -/]
instance isMulRightInvariant_restrictedHaar
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure] [∀ i, (μ i).IsMulRightInvariant]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    (restrictedHaar B μ hμ).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    refine eq_restrictedHaar_of_box μ hμ fun C hC hCB ↦ ?_
    have hbox_meas : MeasurableSet {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ C i} := by
      rw [← restrictedProductBox_def (fun i ↦ (B i : Set (G i))) cofinite C]
      exact (isOpen_restrictedProductBox hC (hCB.mono fun i hi ↦ hi.symm.subset)).measurableSet
    rw [Measure.map_apply (measurable_mul_const g) hbox_meas]
    have hpre : (· * g) ⁻¹' {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ C i} =
        {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ (· * g i) ⁻¹' C i} := by
      ext x
      simp
    have hCB' : ∀ᶠ i in cofinite, (· * g i) ⁻¹' C i = B i := by
      filter_upwards [hCB, g.2] with i hiC hig
      ext y
      simp only [mem_preimage, hiC, SetLike.mem_coe]
      exact mul_mem_cancel_right (SetLike.mem_coe.mp hig)
    rw [hpre, restrictedHaar_box μ hμ hCB']
    simp_rw [measure_preimage_mul_right]

/-- When all local Haar measures `μ i` are inversion-invariant, so is `restrictedHaar B μ hμ`. -/
@[to_additive
/-- When all local additive Haar measures `μ i` are negation-invariant, so is
`restrictedAddHaar B μ hμ`. -/]
instance isInvInvariant_restrictedHaar
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure] [∀ i, (μ i).IsInvInvariant]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    (restrictedHaar B μ hμ).IsInvInvariant where
  inv_eq_self := by
    refine eq_restrictedHaar_of_box μ hμ fun C _ hCB ↦ ?_
    have hpre : ({x : Πʳ i, [G i, B i] | ∀ i, x i ∈ C i})⁻¹ =
        {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ (C i)⁻¹} := by
      ext x
      simp
    have hCB' : ∀ᶠ i in cofinite, (C i)⁻¹ = B i := by
      filter_upwards [hCB] with i hiC
      ext y
      simp [hiC]
    rw [Measure.inv_apply, hpre, restrictedHaar_box μ hμ hCB']
    simp_rw [measure_inv]

end Properties

end RestrictedHaar

end TauCeti

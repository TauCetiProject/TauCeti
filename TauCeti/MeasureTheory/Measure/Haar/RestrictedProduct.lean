/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import TauCeti.MeasureTheory.Constructions.BorelSpace.RestrictedProduct
public import TauCeti.MeasureTheory.Measure.Haar.InfinitePi
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Topology.Algebra.Group.Basic
import TauCeti.Topology.Bases

/-!
# Restricted products of Haar measures

Let `(G i)` be a countable family of second-countable locally compact Borel groups, `(B i)` a family
of open subgroups such that cofinitely many `B i` are compact, and `μ i` a Haar measure on each
`G i` normalized so that `μ i (B i) = 1` for all but finitely many `i`.

For any finite index set `S : Finset ι` containing `{i | μ i (B i) ≠ 1}`, the principal piece
`{x : Πʳ i, [G i, B i] | ∀ i ∉ S, x i ∈ B i}` is openly embedded as the topological group product
`(∀ i : S, G i) × (∀ i : {i // i ∉ S}, B i)` via `restrictedProductPrincipalPieceInclusion B S`. On
that product, `restrictedPrincipalPieceMeasure B S μ` combines the finite product Haar measure
`Measure.pi (fun i : S ↦ μ i)` with the infinite product probability Haar measure
`Measure.infinitePi (fun j : {i // i ∉ S} ↦ (μ j).comap (↑))`.

Choosing one reference set `S₀` outside which `B i` is compact of mass `1`, we rescale an arbitrary
Haar measure on the locally compact group `Πʳ i, [G i, B i]` by `Measure.haarScalarFactor` so that
its pullback to the `S₀`-principal piece coincides with `restrictedPrincipalPieceMeasure B S₀ μ`.
This defines `restrictedHaar B hB μ hμ` (additively `restrictedAddHaar`), and Haar uniqueness on
every principal piece then yields:

* **Principal-piece compatibility** (`comap_restrictedHaar_principalPieceInclusion`,
  `measurePreserving_restrictedHaar_principalPieceInclusion`): for *every* finite set `S` outside
  which `μ i (B i) = 1`, pulling `restrictedHaar B hB μ hμ` back along
  `restrictedProductPrincipalPieceInclusion B S` recovers `restrictedPrincipalPieceMeasure B S μ`.
* **Box formula** (`restrictedHaar_box`, `restrictedHaar_restrictedProductBox`): for any coordinate
  sets `C i ⊆ G i` (without measurability assumptions) satisfying `C i = B i` cofinitely,
  `restrictedHaar B hB μ hμ {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i)`.
* **Existence and uniqueness** (`eq_restrictedHaar_of_box`, `exists_unique_restrictedHaar`,
  `exists_unique_restrictedAddHaar`): `restrictedHaar B hB μ hμ` is the unique Haar measure (indeed,
  the unique left-invariant measure finite on compacts) satisfying the box formula on measurable
  boxes.
* **Right and inversion invariance** (`isMulRightInvariant_restrictedHaar`,
  `isInvInvariant_restrictedHaar`): when all local factors `μ i` are right-invariant or
  inversion-invariant, so is `restrictedHaar B hB μ hμ`.

No Hausdorff assumption on the factors `G i` is required anywhere.

## References

* D. Ramakrishnan and R. J. Valenza, *Fourier Analysis on Number Fields*, Chapter 5.
* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, §3.3.
-/

public section

namespace TauCeti

open Filter MeasureTheory MeasureTheory.Measure Set Topology
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

/-- When `B i` is open of `μ i`-mass `1` outside `S`, the pullback `(μ j).comap (↑)` to `B j` is a
probability measure for every `j : {i // i ∉ S}`. -/
theorem isProbabilityMeasure_comap_of_notMem
    [∀ i, TopologicalSpace (G i)] [∀ i, OpensMeasurableSpace (G i)]
    {B : ∀ i, K i} {S : Finset ι} {μ : ∀ i, Measure (G i)}
    (hBopen : ∀ i ∉ S, IsOpen (B i : Set (G i)))
    (hμS : ∀ i ∉ S, μ i (B i) = 1) (j : {i // i ∉ S}) :
    IsProbabilityMeasure ((μ j.1).comap ((↑) : B j.1 → G j.1)) :=
  ⟨by
    have hemb : MeasurableEmbedding ((↑) : B j.1 → G j.1) :=
      MeasurableEmbedding.subtype_coe (hBopen j.1 j.2).measurableSet
    rw [hemb.comap_apply, image_univ, Subtype.range_coe_subtype]
    exact hμS j.1 j.2⟩

end PrincipalPieceDef

section RestrictedHaar

variable {ι : Type u} {G : ι → Type v} {K : ι → Type w}
variable [Countable ι] [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)]
  [∀ i, SecondCountableTopology (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
  [∀ i, SetLike (K i) (G i)] [∀ i, SubgroupClass (K i) (G i)]

omit [Countable ι] in
/-- When `B i` is open of `μ i`-mass `1` outside `S`, `restrictedPrincipalPieceMeasure B S μ` is a
Haar measure on `(∀ i : S, G i) × (∀ i : {i // i ∉ S}, B i)`. -/
@[to_additive]
theorem isHaarMeasure_restrictedPrincipalPieceMeasure {B : ∀ i, K i} {S : Finset ι}
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hBopen : ∀ i ∉ S, IsOpen (B i : Set (G i))) (hμS : ∀ i ∉ S, μ i (B i) = 1) :
    (restrictedPrincipalPieceMeasure B S μ).IsHaarMeasure := by
  have : ∀ j : {i // i ∉ S}, IsProbabilityMeasure ((μ j.1).comap ((↑) : B j.1 → G j.1)) :=
    isProbabilityMeasure_comap_of_notMem hBopen hμS
  have : ∀ j : {i // i ∉ S}, ((μ j.1).comap ((↑) : B j.1 → G j.1)).IsHaarMeasure := fun j ↦
    Measure.IsHaarMeasure.comap (mH := inferInstance) (μ j.1)
      (f := SubgroupClass.subtype (B j.1)) (hBopen j.1 j.2).isOpenEmbedding_subtypeVal
  rw [restrictedPrincipalPieceMeasure_def]
  infer_instance

/-- **Restricted product of Haar measures.** Given open subgroups `B i ≤ G i` that are compact for
cofinitely many `i` and local Haar measures `μ i` satisfying `μ i (B i) = 1` cofinitely, this is
the unique Haar measure on `Πʳ i, [G i, B i]` assigning mass `∏ᶠ i, μ i (C i)` to every coordinate
box `{x | ∀ i, x i ∈ C i}` with `C i = B i` cofinitely. -/
@[to_additive
/-- **Restricted product of additive Haar measures.** Given open additive subgroups `B i ≤ G i` that
are compact for cofinitely many `i` and local additive Haar measures `μ i` satisfying
`μ i (B i) = 1` cofinitely, this is the unique additive Haar measure on `Πʳ i, [G i, B i]` assigning
mass `∏ᶠ i, μ i (C i)` to every coordinate box `{x | ∀ i, x i ∈ C i}` with `C i = B i`
cofinitely. -/]
noncomputable def restrictedHaar (B : ∀ i, K i) [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    [MeasurableSpace (Πʳ i, [G i, B i])] [BorelSpace (Πʳ i, [G i, B i])]
    (hB : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    Measure (Πʳ i, [G i, B i]) :=
  let _ := Classical.decEq ι
  have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    RestrictedProduct.locallyCompactSpace_of_group G hB
  let hfin : {i | ¬ (IsCompact (B i : Set (G i)) ∧ μ i (B i) = 1)}.Finite :=
    eventually_cofinite.mp (hB.and hμ)
  let S₀ : Finset ι := hfin.toFinset
  have hμS₀ : ∀ i ∉ S₀, μ i (B i) = 1 := fun i hi ↦ by
    by_contra hnot
    exact hi (hfin.mem_toFinset.mpr fun h ↦ hnot h.2)
  have : (restrictedPrincipalPieceMeasure B S₀ μ).IsHaarMeasure :=
    isHaarMeasure_restrictedPrincipalPieceMeasure μ (fun i _ ↦ hBopen.out i) hμS₀
  let ν₀ : Measure (Πʳ i, [G i, B i]) := Measure.haar
  have : (ν₀.comap (restrictedProductPrincipalPieceInclusion B S₀)).IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := inferInstance) ν₀
      (isOpenEmbedding_restrictedProductPrincipalPieceInclusion B S₀ fun i _ ↦ hBopen.out i)
  haarScalarFactor (restrictedPrincipalPieceMeasure B S₀ μ)
    (ν₀.comap (restrictedProductPrincipalPieceInclusion B S₀)) • ν₀

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
    isProbabilityMeasure_comap_of_notMem (fun i _ ↦ hBopen.out i) hμS
  let T : Finset {i // i ∉ S} := F.subtype (fun i ↦ i ∉ S)
  have hpre : restrictedProductPrincipalPieceInclusion B S ⁻¹'
      restrictedProductBox (fun i ↦ (B i : Set (G i))) cofinite C =
      (Set.univ.pi fun i : S ↦ C i.1) ×ˢ
        ((T : Set {i // i ∉ S}).pi fun j ↦ ((↑) : B j.1 → G j.1) ⁻¹' C j.1) := by
    ext p
    simp only [mem_preimage, mem_restrictedProductBox, mem_prod, Set.mem_pi, mem_univ,
      forall_true_left, Finset.mem_coe, T, Finset.mem_subtype]
    constructor
    · intro hp
      refine ⟨fun i ↦ ?_, fun j _ ↦ ?_⟩
      · simpa [restrictedProductPrincipalPieceInclusion_apply_of_mem B S p i.2] using hp i.1
      · simpa [restrictedProductPrincipalPieceInclusion_apply_of_notMem B S p j.2] using hp j.1
    · rintro ⟨hp₁, hp₂⟩ i
      by_cases hiS : i ∈ S
      · rw [restrictedProductPrincipalPieceInclusion_apply_of_mem B S p hiS]
        exact hp₁ ⟨i, hiS⟩
      · rw [restrictedProductPrincipalPieceInclusion_apply_of_notMem B S p hiS]
        by_cases hiF : i ∈ F
        · exact hp₂ ⟨i, hiS⟩ hiF
        · rw [hCBF i hiF]
          exact (p.2 ⟨i, hiS⟩).2
  rw [hpre, restrictedPrincipalPieceMeasure_def, prod_prod, pi_pi, infinitePi_pi',
    Finset.univ_eq_attach, Finset.prod_attach S fun i ↦ μ i (C i)]
  have hT : (∏ j ∈ T, (μ j.1).comap ((↑) : B j.1 → G j.1) (((↑) : B j.1 → G j.1) ⁻¹' C j.1)) =
      ∏ j ∈ T, μ j.1 (C j.1) := by
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    have hemb : MeasurableEmbedding ((↑) : B j.1 → G j.1) :=
      MeasurableEmbedding.subtype_coe (hBopen.out j.1).measurableSet
    rw [hemb.comap_apply, image_preimage_eq_inter_range, Subtype.range_coe_subtype,
      SetLike.setOfPred_mem_eq, inter_eq_self_of_subset_left (hCB_sub j.1)]
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

@[to_additive]
instance isHaarMeasure_restrictedHaar
    (hB : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    (restrictedHaar B hB μ hμ).IsHaarMeasure := by
  classical
  have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    RestrictedProduct.locallyCompactSpace_of_group G hB
  let hfin : {i | ¬ (IsCompact (B i : Set (G i)) ∧ μ i (B i) = 1)}.Finite :=
    eventually_cofinite.mp (hB.and hμ)
  let S₀ : Finset ι := hfin.toFinset
  let ν₀ : Measure (Πʳ i, [G i, B i]) := Measure.haar
  have hμS₀ : ∀ i ∉ S₀, μ i (B i) = 1 := fun i hi ↦ by
    by_contra hnot
    exact hi (hfin.mem_toFinset.mpr fun h ↦ hnot h.2)
  have hemb₀ : IsOpenEmbedding (restrictedProductPrincipalPieceInclusion B S₀) :=
    isOpenEmbedding_restrictedProductPrincipalPieceInclusion B S₀ fun i _ ↦ hBopen.out i
  have : LocallyCompactSpace ((∀ i : S₀, G i.1) × (∀ j : {i // i ∉ S₀}, B j.1)) :=
    hemb₀.locallyCompactSpace
  have : (restrictedPrincipalPieceMeasure B S₀ μ).IsHaarMeasure :=
    isHaarMeasure_restrictedPrincipalPieceMeasure μ (fun i _ ↦ hBopen.out i) hμS₀
  have : (ν₀.comap (restrictedProductPrincipalPieceInclusion B S₀)).IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := inferInstance) ν₀ hemb₀
  have hc : haarScalarFactor (restrictedPrincipalPieceMeasure B S₀ μ)
      (ν₀.comap (restrictedProductPrincipalPieceInclusion B S₀)) ≠ 0 :=
    (haarScalarFactor_pos_of_isHaarMeasure _ _).ne'
  exact IsHaarMeasure.nnreal_smul ν₀ hc

/-- **Principal-piece compatibility.** For any finite set `S : Finset ι` outside which
`μ i (B i) = 1`, pulling `restrictedHaar B hB μ hμ` back along
`restrictedProductPrincipalPieceInclusion B S` yields `restrictedPrincipalPieceMeasure B S μ`. -/
@[to_additive]
theorem comap_restrictedHaar_principalPieceInclusion
    (hB : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1)
    {S : Finset ι} (hμS : ∀ i ∉ S, μ i (B i) = 1) :
    (restrictedHaar B hB μ hμ).comap (restrictedProductPrincipalPieceInclusion B S) =
      restrictedPrincipalPieceMeasure B S μ := by
  classical
  have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    RestrictedProduct.locallyCompactSpace_of_group G hB
  let hfin : {i | ¬ (IsCompact (B i : Set (G i)) ∧ μ i (B i) = 1)}.Finite :=
    eventually_cofinite.mp (hB.and hμ)
  let S₀ : Finset ι := hfin.toFinset
  have hμS₀ : ∀ i ∉ S₀, μ i (B i) = 1 := fun i hi ↦ by
    by_contra hnot
    exact hi (hfin.mem_toFinset.mpr fun h ↦ hnot h.2)
  have hemb₀ : IsOpenEmbedding (restrictedProductPrincipalPieceInclusion B S₀) :=
    isOpenEmbedding_restrictedProductPrincipalPieceInclusion B S₀ fun i _ ↦ hBopen.out i
  have hemb : IsOpenEmbedding (restrictedProductPrincipalPieceInclusion B S) :=
    isOpenEmbedding_restrictedProductPrincipalPieceInclusion B S fun i _ ↦ hBopen.out i
  have : LocallyCompactSpace ((∀ i : S₀, G i.1) × (∀ j : {i // i ∉ S₀}, B j.1)) :=
    hemb₀.locallyCompactSpace
  have : LocallyCompactSpace ((∀ i : S, G i.1) × (∀ j : {i // i ∉ S}, B j.1)) :=
    hemb.locallyCompactSpace
  have : (restrictedPrincipalPieceMeasure B S₀ μ).IsHaarMeasure :=
    isHaarMeasure_restrictedPrincipalPieceMeasure μ (fun i _ ↦ hBopen.out i) hμS₀
  have : (restrictedPrincipalPieceMeasure B S μ).IsHaarMeasure :=
    isHaarMeasure_restrictedPrincipalPieceMeasure μ (fun i _ ↦ hBopen.out i) hμS
  let ν := restrictedHaar B hB μ hμ
  -- First verify the base case `S = S₀` directly from the definition of `restrictedHaar`.
  have hbase : ν.comap (restrictedProductPrincipalPieceInclusion B S₀) =
      restrictedPrincipalPieceMeasure B S₀ μ := by
    let ν₀ : Measure (Πʳ i, [G i, B i]) := Measure.haar
    have : (ν₀.comap (restrictedProductPrincipalPieceInclusion B S₀)).IsHaarMeasure :=
      Measure.IsHaarMeasure.comap (mH := inferInstance) ν₀ hemb₀
    let c : ℝ≥0 := haarScalarFactor (restrictedPrincipalPieceMeasure B S₀ μ)
      (ν₀.comap (restrictedProductPrincipalPieceInclusion B S₀))
    have hν : ν = c • ν₀ := rfl
    have hsmul : (c • ν₀).comap (restrictedProductPrincipalPieceInclusion B S₀) =
        c • ν₀.comap (restrictedProductPrincipalPieceInclusion B S₀) := by
      ext E _
      simp [hemb₀.measurableEmbedding.comap_apply]
    rw [hν, hsmul]
    exact (isMulLeftInvariant_eq_smul (restrictedPrincipalPieceMeasure B S₀ μ)
      (ν₀.comap (restrictedProductPrincipalPieceInclusion B S₀))).symm
  -- Now compare the two Haar measures on the `S`-principal piece on a common compact test box.
  have : (ν.comap (restrictedProductPrincipalPieceInclusion B S)).IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := inferInstance) ν hemb
  let c : ℝ≥0 := haarScalarFactor (ν.comap (restrictedProductPrincipalPieceInclusion B S))
    (restrictedPrincipalPieceMeasure B S μ)
  have hc_eq : ν.comap (restrictedProductPrincipalPieceInclusion B S) =
      c • restrictedPrincipalPieceMeasure B S μ :=
    isMulLeftInvariant_eq_smul _ _
  have hL : ∀ i, ∃ L : Set (G i), (L ∈ 𝓝 (1 : G i) ∧ IsCompact L ∧ IsClosed L) ∧
      L ⊆ (B i : Set (G i)) :=
    fun i ↦ (isCompact_isClosed_basis_nhds (1 : G i)).mem_iff.mp
      ((hBopen.out i).mem_nhds (one_mem (B i)))
  choose L hLprop hLB using hL
  let F : Finset ι := S ∪ S₀
  let C : ∀ i, Set (G i) := fun i ↦ if i ∈ F then L i else B i
  have hCB_sub : ∀ i, C i ⊆ B i := fun i ↦ by
    dsimp only [C]
    split_ifs
    · exact hLB i
    · exact Subset.rfl
  have hCBF : ∀ i ∉ F, C i = B i := fun i hi ↦ by simp [C, hi]
  let box := restrictedProductBox (fun i ↦ (B i : Set (G i))) cofinite C
  have hbox_sub₀ : box ⊆ Set.range (restrictedProductPrincipalPieceInclusion B S₀) := by
    rw [range_restrictedProductPrincipalPieceInclusion]
    exact fun x hx i _ ↦ hCB_sub i (mem_restrictedProductBox.mp hx i)
  have hbox_sub : box ⊆ Set.range (restrictedProductPrincipalPieceInclusion B S) := by
    rw [range_restrictedProductPrincipalPieceInclusion]
    exact fun x hx i _ ↦ hCB_sub i (mem_restrictedProductBox.mp hx i)
  have heval₀ : ν box = ∏ i ∈ F, μ i (C i) := by
    calc ν box
        = ν (restrictedProductPrincipalPieceInclusion B S₀ ''
            (restrictedProductPrincipalPieceInclusion B S₀ ⁻¹' box)) := by
          rw [image_preimage_eq_inter_range, inter_eq_self_of_subset_left hbox_sub₀]
      _ = (ν.comap (restrictedProductPrincipalPieceInclusion B S₀))
            (restrictedProductPrincipalPieceInclusion B S₀ ⁻¹' box) :=
          (hemb₀.measurableEmbedding.comap_apply _ _).symm
      _ = ∏ i ∈ F, μ i (C i) := by
          rw [hbase]
          exact restrictedPrincipalPieceMeasure_preimage_box_of_subset Finset.subset_union_right μ
            hμS₀ hCB_sub hCBF
  have heval : (ν.comap (restrictedProductPrincipalPieceInclusion B S))
      (restrictedProductPrincipalPieceInclusion B S ⁻¹' box) = ν box := by
    rw [hemb.measurableEmbedding.comap_apply, image_preimage_eq_inter_range,
      inter_eq_self_of_subset_left hbox_sub]
  have hprod_pos : ∏ i ∈ F, μ i (C i) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    dsimp only [C]
    rw [ite_eq_left hi]
    exact (measure_pos_of_mem_nhds (μ i) (hLprop i).1).ne'
  have hprod_top : ∏ i ∈ F, μ i (C i) ≠ ∞ := by
    refine (WithTop.prod_lt_top fun i hi ↦ ?_).ne
    dsimp only [C]
    rw [ite_eq_left hi]
    exact (hLprop i).2.1.measure_lt_top
  have hscalar : (c : ℝ≥0∞) * ∏ i ∈ F, μ i (C i) = 1 * ∏ i ∈ F, μ i (C i) := by
    have h₁ := congrArg (fun m : Measure _ ↦
      m (restrictedProductPrincipalPieceInclusion B S ⁻¹' box)) hc_eq
    simp only [smul_apply, nnreal_smul_coe_apply] at h₁
    rw [heval, heval₀, restrictedPrincipalPieceMeasure_preimage_box_of_subset
      Finset.subset_union_left μ hμS hCB_sub hCBF] at h₁
    simpa only [one_mul] using h₁.symm
  have hc1 : c = 1 := by
    exact_mod_cast (ENNReal.mul_left_inj hprod_pos hprod_top).mp hscalar
  rw [hc_eq, hc1, one_smul]

/-- For any finite set `S : Finset ι` outside which `μ i (B i) = 1`,
`restrictedProductPrincipalPieceInclusion B S` is measure-preserving from
`restrictedPrincipalPieceMeasure B S μ` onto
`(restrictedHaar B hB μ hμ).restrict {x | ∀ i ∉ S, x i ∈ B i}`. -/
@[to_additive]
theorem measurePreserving_restrictedHaar_principalPieceInclusion
    (hB : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1)
    {S : Finset ι} (hμS : ∀ i ∉ S, μ i (B i) = 1) :
    MeasurePreserving (restrictedProductPrincipalPieceInclusion B S)
      (restrictedPrincipalPieceMeasure B S μ)
      ((restrictedHaar B hB μ hμ).restrict {x | ∀ i ∉ S, x i ∈ B i}) := by
  have hemb : IsOpenEmbedding (restrictedProductPrincipalPieceInclusion B S) :=
    isOpenEmbedding_restrictedProductPrincipalPieceInclusion B S fun i _ ↦ hBopen.out i
  refine ⟨hemb.continuous.measurable, ?_⟩
  rw [← comap_restrictedHaar_principalPieceInclusion hB μ hμ hμS,
    hemb.measurableEmbedding.map_comap, range_restrictedProductPrincipalPieceInclusion]

/-- **Box formula for `restrictedHaar`** (`restrictedProductBox` form), requiring no measurability
hypothesis on the coordinate sets `C i`. -/
@[to_additive]
theorem restrictedHaar_restrictedProductBox
    (hB : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1)
    {C : ∀ i, Set (G i)} (hCB : ∀ᶠ i in cofinite, C i = B i) :
    restrictedHaar B hB μ hμ
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
    isProbabilityMeasure_comap_of_notMem (fun i _ ↦ hBopen.out i) hμS
  calc restrictedHaar B hB μ hμ box
      = restrictedHaar B hB μ hμ
          (restrictedProductPrincipalPieceInclusion B S ''
            (restrictedProductPrincipalPieceInclusion B S ⁻¹' box)) := by
        rw [image_preimage_eq_inter_range, inter_eq_self_of_subset_left hbox_sub]
    _ = ((restrictedHaar B hB μ hμ).comap (restrictedProductPrincipalPieceInclusion B S))
          (restrictedProductPrincipalPieceInclusion B S ⁻¹' box) :=
        (hemb.measurableEmbedding.comap_apply _ _).symm
    _ = restrictedPrincipalPieceMeasure B S μ
          ((Set.univ.pi fun i : S ↦ C i.1) ×ˢ Set.univ) := by
        rw [comap_restrictedHaar_principalPieceInclusion hB μ hμ hμS,
          preimage_restrictedProductPrincipalPieceInclusion_box B S
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
`restrictedHaar B hB μ hμ {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i)`. -/
@[to_additive]
theorem restrictedHaar_box
    (hB : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1)
    {C : ∀ i, Set (G i)} (hCB : ∀ᶠ i in cofinite, C i = B i) :
    restrictedHaar B hB μ hμ {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i) := by
  rw [← restrictedProductBox_def (fun i ↦ (B i : Set (G i))) cofinite C]
  exact restrictedHaar_restrictedProductBox hB μ hμ hCB

/-- **Uniqueness of `restrictedHaar`.** Any left-invariant measure on `Πʳ i, [G i, B i]` that is
finite on compact sets and gives every measurable coordinate box `{x | ∀ i, x i ∈ C i}` with
`C i = B i` cofinitely the mass `∏ᶠ i, μ i (C i)` equals `restrictedHaar B hB μ hμ`. -/
@[to_additive]
theorem eq_restrictedHaar_of_box
    (hB : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1)
    {ν : Measure (Πʳ i, [G i, B i])} [ν.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts ν]
    (hν : ∀ C : ∀ i, Set (G i), (∀ i, MeasurableSet (C i)) →
      (∀ᶠ i in cofinite, C i = B i) → ν {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i)) :
    ν = restrictedHaar B hB μ hμ := by
  classical
  have : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    RestrictedProduct.locallyCompactSpace_of_group G hB
  let c : ℝ≥0 := haarScalarFactor ν (restrictedHaar B hB μ hμ)
  have hc_eq : ν = c • restrictedHaar B hB μ hμ :=
    isMulLeftInvariant_eq_smul ν (restrictedHaar B hB μ hμ)
  let hfin : {i | μ i (B i) ≠ 1}.Finite := eventually_cofinite.mp hμ
  let S₀ : Finset ι := hfin.toFinset
  have hL : ∀ i, ∃ L : Set (G i), L ∈ 𝓝 (1 : G i) ∧ IsCompact L ∧ IsClosed L :=
    fun i ↦ exists_mem_nhds_isCompact_isClosed (1 : G i)
  choose L hL1 hLcomp hLclosed using hL
  let C : ∀ i, Set (G i) := fun i ↦ if i ∈ S₀ then L i else B i
  have hCmeas : ∀ i, MeasurableSet (C i) := fun i ↦ by
    dsimp only [C]
    split_ifs
    · exact (hLclosed i).measurableSet
    · exact (hBopen.out i).measurableSet
  have hCB : ∀ᶠ i in cofinite, C i = B i := by
    filter_upwards [S₀.finite_toSet.compl_mem_cofinite] with i hi
    exact ite_eq_right (Finset.mem_coe.not.mp hi)
  have hprod : ∏ᶠ i, μ i (C i) = ∏ i ∈ S₀, μ i (L i) := by
    calc ∏ᶠ i, μ i (C i)
        = ∏ i ∈ S₀, μ i (C i) := by
          refine finprod_eq_prod_of_mulSupport_subset _ (s := S₀) fun i hi ↦ ?_
          by_contra hiS
          have hμ1 : μ i (B i) = 1 := by
            by_contra hnot
            exact hiS (hfin.mem_toFinset.mpr hnot)
          have hiS' : i ∉ S₀ := Finset.mem_coe.not.mp hiS
          exact hi (by dsimp only [C]; rw [ite_eq_right hiS', hμ1])
      _ = ∏ i ∈ S₀, μ i (L i) := Finset.prod_congr rfl fun i hi ↦ by simp [C, hi]
  have hpos : ∏ᶠ i, μ i (C i) ≠ 0 := by
    rw [hprod, Finset.prod_ne_zero_iff]
    exact fun i _ ↦ (measure_pos_of_mem_nhds (μ i) (hL1 i)).ne'
  have htop : ∏ᶠ i, μ i (C i) ≠ ∞ := by
    rw [hprod]
    exact (WithTop.prod_lt_top fun i _ ↦ (hLcomp i).measure_lt_top).ne
  have hscalar : (c : ℝ≥0∞) * ∏ᶠ i, μ i (C i) = 1 * ∏ᶠ i, μ i (C i) := by
    have h₁ := congrArg (fun m : Measure _ ↦ m {x | ∀ i, x i ∈ C i}) hc_eq
    simp only [smul_apply, nnreal_smul_coe_apply] at h₁
    rw [hν C hCmeas hCB, restrictedHaar_box hB μ hμ hCB] at h₁
    simpa only [one_mul] using h₁.symm
  have hc1 : c = 1 := by
    exact_mod_cast (ENNReal.mul_left_inj hpos htop).mp hscalar
  rw [hc_eq, hc1, one_smul]

/-- **Existence and uniqueness of restricted-product Haar measure.** When cofinitely many open
subgroups `B i` are compact and cofinitely many local Haar measures satisfy `μ i (B i) = 1`, there
is a unique Haar measure on `Πʳ i, [G i, B i]` assigning mass `∏ᶠ i, μ i (C i)` to every measurable
coordinate box `{x | ∀ i, x i ∈ C i}` with `C i = B i` cofinitely. -/
@[to_additive
/-- **Existence and uniqueness of restricted-product additive Haar measure.** When cofinitely many
open additive subgroups `B i` are compact and cofinitely many local additive Haar measures satisfy
`μ i (B i) = 1`, there is a unique additive Haar measure on `Πʳ i, [G i, B i]` assigning mass
`∏ᶠ i, μ i (C i)` to every measurable coordinate box `{x | ∀ i, x i ∈ C i}` with `C i = B i`
cofinitely. -/]
theorem exists_unique_restrictedHaar
    (hB : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    ∃! ν : Measure (Πʳ i, [G i, B i]), ν.IsHaarMeasure ∧
      ∀ C : ∀ i, Set (G i), (∀ i, MeasurableSet (C i)) →
        (∀ᶠ i in cofinite, C i = B i) →
        ν {x | ∀ i, x i ∈ C i} = ∏ᶠ i, μ i (C i) :=
  ⟨restrictedHaar B hB μ hμ,
    ⟨inferInstance, fun _ _ hCB ↦ restrictedHaar_box hB μ hμ hCB⟩,
    fun _ ⟨_hHaar, hbox⟩ ↦ eq_restrictedHaar_of_box hB μ hμ hbox⟩

/-- When all local Haar measures `μ i` are right-invariant, so is `restrictedHaar B hB μ hμ`. -/
@[to_additive]
instance isMulRightInvariant_restrictedHaar
    (hB : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure] [∀ i, (μ i).IsMulRightInvariant]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    (restrictedHaar B hB μ hμ).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    refine eq_restrictedHaar_of_box hB μ hμ fun C hC hCB ↦ ?_
    have hbox_meas : MeasurableSet {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ C i} := by
      rw [← restrictedProductBox_def (fun i ↦ (B i : Set (G i))) cofinite C]
      exact measurableSet_restrictedProductBox_of_countable hC
    rw [Measure.map_apply (measurable_mul_const g) hbox_meas]
    have hpre : (· * g) ⁻¹' {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ C i} =
        {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ (· * g i) ⁻¹' C i} := rfl
    have hCB' : ∀ᶠ i in cofinite, (· * g i) ⁻¹' C i = B i := by
      filter_upwards [hCB, g.2] with i hiC hig
      ext y
      simp only [mem_preimage, hiC, SetLike.mem_coe]
      exact mul_mem_cancel_right (SetLike.mem_coe.mp hig)
    rw [hpre, restrictedHaar_box hB μ hμ hCB']
    simp_rw [measure_preimage_mul_right]

/-- When all local Haar measures `μ i` are inversion-invariant, so is `restrictedHaar B hB μ hμ`. -/
@[to_additive]
instance isInvInvariant_restrictedHaar
    (hB : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure] [∀ i, (μ i).IsInvInvariant]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    (restrictedHaar B hB μ hμ).IsInvInvariant where
  inv_eq_self := by
    have : ∀ i, (μ i).IsMulRightInvariant := fun i ↦
      Measure.inv_eq_self (μ i) ▸ (inferInstance : (μ i).inv.IsMulRightInvariant)
    have : IsFiniteMeasureOnCompacts (restrictedHaar B hB μ hμ).inv :=
      ⟨fun K hK ↦ by
        rw [Measure.inv_apply, ← image_inv_eq_inv]
        exact (hK.image continuous_inv).measure_lt_top⟩
    refine eq_restrictedHaar_of_box hB μ hμ fun C _ hCB ↦ ?_
    have hpre : ({x : Πʳ i, [G i, B i] | ∀ i, x i ∈ C i})⁻¹ =
        {x : Πʳ i, [G i, B i] | ∀ i, x i ∈ (C i)⁻¹} := by
      ext x
      simp
    have hCB' : ∀ᶠ i in cofinite, (C i)⁻¹ = B i := by
      filter_upwards [hCB] with i hiC
      ext y
      simp [hiC]
    rw [Measure.inv_apply, hpre, restrictedHaar_box hB μ hμ hCB']
    simp_rw [measure_inv]

end Properties

end RestrictedHaar

end TauCeti

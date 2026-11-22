/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Log.Summable
public import TauCeti.MeasureTheory.Constructions.BorelSpace.RestrictedProduct
public import TauCeti.MeasureTheory.Measure.Haar.InfinitePi
public import TauCeti.MeasureTheory.Measure.Haar.Unique
public import TauCeti.MeasureTheory.Measure.Subtype
public import TauCeti.Topology.Algebra.Group.Basic
public import TauCeti.Topology.Algebra.RestrictedProduct.Congr.Basic
public import TauCeti.Topology.Algebra.RestrictedProduct.Principal
public import TauCeti.Topology.Bases
import TauCeti.MeasureTheory.Group.Arithmetic
import TauCeti.MeasureTheory.Group.OpenSubgroup.Basic
import TauCeti.MeasureTheory.Measure.Comap
import TauCeti.Topology.Algebra.InfiniteSum.Group

/-!
# Convergent restricted products of local Haar measures

Let `(G i)` be a countable family of second-countable locally compact topological groups equipped
with open subgroups `B i`, together with left Haar measures `μ i` on `G i`. We construct left Haar
measures on `Πʳ i, [G i, B i]` in two regimes:

1. **Normalized restricted Haar product** (`TauCeti.restrictedHaar`,
   `TauCeti.exists_unique_restrictedHaar`): assuming `μ i (B i) = 1` cofinitely, there is a unique
   left Haar measure `ν` with `ν (box C) = ∏ᶠ i, μ i (C i)` on measurable boxes agreeing cofinitely
   with `B i` (extended to such boxes without measurability assumptions on their factors in
   `TauCeti.restrictedHaar_box_eq_finprod` and `TauCeti.restrictedHaar_box`). No compactness of
   `B i` is assumed: an open subgroup of finite Haar measure is compact
   (`MeasureTheory.isCompact_of_isOpen_of_measure_ne_top_of_isMulLeftInvariant`), so
   `Πʳ i, [G i, B i]` is locally compact
   (`TauCeti.locallyCompactSpace_restrictedProduct_of_measure_ne_top_of_isMulLeftInvariant`). The
   measure is determined among *all* measures by its values on open boxes
   (`TauCeti.eq_restrictedHaar_of_box`), and on each principal piece (for any finite set `T` with
   `μ i (B i) = 1` for every `i ∉ T`) it is the product `TauCeti.restrictedPrincipalPieceMeasure`
   of a finite product Haar measure with Kolmogorov's infinite product of probability Haar measures.
2. **Convergent restricted Haar product** (`TauCeti.convergentHaarProduct`,
   `TauCeti.exists_unique_convergentHaarProduct`): assuming only
   `Summable fun i : {i // i ∉ S} ↦ |(μ i.1 (B i.1)).toReal - 1|` outside a finite set `S`, there
   is a unique left Haar measure `ν` assigning
   `(∏ i ∈ T, μ i (C i)) * ENNReal.ofReal (∏' i : {i // i ∉ T}, (μ i.1 (B i.1)).toReal)`
   to every measurable box `box C` agreeing with `B i` outside `T ⊇ S` (extended to such boxes
   without measurability assumptions on their factors in `TauCeti.convergentHaarProduct_box`,
   and expressed as a rescaled `restrictedHaar` in
   `TauCeti.convergentHaarProduct_eq_smul_restrictedHaar`).

Every definition and theorem has an additive counterpart (`TauCeti.restrictedAddHaar`,
`TauCeti.convergentAddHaarProduct`, …) via `@[to_additive]`.

## Main definitions and results

* `TauCeti.restrictedPrincipalPieceMeasure`,
  `TauCeti.isHaarMeasure_restrictedPrincipalPieceMeasure`: the product measure on the
  principal-piece model `(Π i : T, G i) × (Π i : {i // i ∉ T}, B i)`.
* `TauCeti.locallyCompactSpace_restrictedProduct_of_measure_ne_top_of_isMulLeftInvariant`.
* `TauCeti.exists_unique_restrictedHaar`, `TauCeti.restrictedHaar`, `TauCeti.restrictedHaar_unique`,
  `TauCeti.eq_restrictedHaar_of_box`, `TauCeti.comap_levelMonoidHom_restrictedHaar`,
  `TauCeti.comap_levelOpenSubgroup_restrictedHaar`,
  `TauCeti.measurePreserving_restrictedHaar_levelMonoidHom`, `TauCeti.restrictedHaar_box`,
  `TauCeti.restrictedHaar_box_eq_finprod`, `TauCeti.restrictedHaar_box_self`,
  `TauCeti.regular_restrictedHaar`, `TauCeti.isLocallyFiniteMeasure_restrictedHaar`,
  `TauCeti.sigmaFinite_restrictedHaar`, `TauCeti.isMulRightInvariant_restrictedHaar`,
  `TauCeti.isInvInvariant_restrictedHaar`,
  `TauCeti.map_restrictedProductCongr_restrictedHaar`.
* `TauCeti.exists_unique_convergentHaarProduct`, `TauCeti.convergentHaarProduct`,
  `TauCeti.convergentHaarProduct_unique`, `TauCeti.convergentHaarProduct_eq_smul_restrictedHaar`,
  `TauCeti.convergentHaarProduct_box`, `TauCeti.convergentHaarProduct_eq_of_subset`,
  `TauCeti.convergentHaarProduct_congr_finset`, `TauCeti.convergentHaarProduct_eq_restrictedHaar`,
  `TauCeti.comap_levelMonoidHom_convergentHaarProduct`,
  `TauCeti.isMulRightInvariant_convergentHaarProduct`,
  `TauCeti.map_restrictedProductCongr_convergentHaarProduct`.

## References

* D. Ramakrishnan and R. J. Valenza, *Fourier Analysis on Number Fields*, Chapter 5.
* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, §3.3.
* A. Weil, *Adeles and Algebraic Groups*, Progress in Mathematics 23, Birkhäuser (1982),
  Chapter II, §§2.1–2.3.
* V. Platonov, A. Rapinchuk, and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. 1,
  2nd ed., Cambridge University Press (2023), §3.5, pp. 188–195.
* A. Borel, *Some finiteness properties of adele groups over number fields*, Publ. Math. IHÉS 16
  (1963), 5–30, §1.
-/

public section

noncomputable section

open Filter MeasureTheory MeasureTheory.Measure RestrictedProduct Set Topology
open scoped ENNReal NNReal Pointwise RestrictedProduct

namespace TauCeti

/-! ### The principal-piece product measure -/

section PrincipalPieceMeasure

variable {ι : Type*} {G : ι → Type*} {K : ι → Type*} [∀ i, MeasurableSpace (G i)]
  [∀ i, SetLike (K i) (G i)]

/-- On the principal-piece model `(Π i : T, G i) × (Π i : {i // i ∉ T}, B i)`, the product of the
finite product measure `Measure.pi fun i : T ↦ μ i` with the infinite product measure
`Measure.infinitePi fun i : {i // i ∉ T} ↦ (μ i).comap (↑)`. -/
def restrictedPrincipalPieceMeasure (B : ∀ i, K i) (T : Finset ι) (μ : ∀ i, Measure (G i)) :
    Measure ((Π i : T, G i) × (Π i : {i // i ∉ T}, B i)) :=
  (Measure.pi fun i : T ↦ μ i.val).prod
    (Measure.infinitePi fun i : {i // i ∉ T} ↦ (μ i.val).comap Subtype.val)

/-- Unfolding `restrictedPrincipalPieceMeasure B T μ`. -/
theorem restrictedPrincipalPieceMeasure_def (B : ∀ i, K i) (T : Finset ι)
    (μ : ∀ i, Measure (G i)) :
    restrictedPrincipalPieceMeasure B T μ =
      (Measure.pi fun i : T ↦ μ i.val).prod
        (Measure.infinitePi fun i : {i // i ∉ T} ↦ (μ i.val).comap Subtype.val) :=
  (rfl)

variable [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, BorelSpace (G i)]
  [∀ i, MeasurableMul (G i)] [∀ i, SubgroupClass (K i) (G i)]

/-- When `B i` is open of `μ i`-mass `1` for every `i ∉ T`, `restrictedPrincipalPieceMeasure B T μ`
is a Haar measure on `(Π i : T, G i) × (Π i : {i // i ∉ T}, B i)`. -/
@[to_additive /-- When `B i` is open of `μ i`-mass `1` for every `i ∉ T`,
`restrictedPrincipalPieceMeasure B T μ` is an additive Haar measure on
`(Π i : T, G i) × (Π i : {i // i ∉ T}, B i)`. -/]
theorem isHaarMeasure_restrictedPrincipalPieceMeasure {B : ∀ i, K i} {T : Finset ι}
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure] [∀ i : T, SigmaFinite (μ i.val)]
    (hBopen : ∀ i ∉ T, IsOpen (B i : Set (G i))) (hμT : ∀ i ∉ T, μ i (B i) = 1) :
    (restrictedPrincipalPieceMeasure B T μ).IsHaarMeasure := by
  have _ (i : {i // i ∉ T}) :
      IsProbabilityMeasure ((μ i.val).comap (Subtype.val : B i.val → G i.val)) :=
    isProbabilityMeasure_comap_subtype (hBopen i.val i.property).measurableSet (μ i.val)
      (hμT i.val i.property)
  have _ (i : {i // i ∉ T}) : ((μ i.val).comap (Subtype.val : B i.val → G i.val)).IsHaarMeasure :=
    IsHaarMeasure.comap (mH := inferInstance) (μ i.val) (f := SubgroupClass.subtype (B i.val))
      (hBopen i.val i.property).isOpenEmbedding_subtypeVal
  rw [restrictedPrincipalPieceMeasure_def]
  infer_instance

end PrincipalPieceMeasure

/-- If `B i ≤ G i` are open subgroups of weakly locally compact topological groups whose masses
under left-invariant open-positive Borel measures are cofinitely finite, then `Πʳ i, [G i, B i]` is
locally compact: cofinitely many `B i` are then compact. -/
@[to_additive /-- If `B i ≤ G i` are open additive subgroups of weakly locally compact topological
additive groups whose masses under left-invariant open-positive Borel measures are cofinitely
finite, then `Πʳ i, [G i, B i]` is locally compact: cofinitely many `B i` are then compact. -/]
theorem locallyCompactSpace_restrictedProduct_of_measure_ne_top_of_isMulLeftInvariant
    {ι : Type*} {G : ι → Type*} {K : ι → Type*}
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    [∀ i, WeaklyLocallyCompactSpace (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
    [∀ i, SetLike (K i) (G i)] [∀ i, SubgroupClass (K i) (G i)] {B : ∀ i, K i}
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsOpenPosMeasure] [∀ i, (μ i).IsMulLeftInvariant]
    (hμ : ∀ᶠ i in cofinite, μ i (B i) ≠ ∞) :
    LocallyCompactSpace (Πʳ i, [G i, B i]) :=
  locallyCompactSpace_of_group G <| hμ.mono fun i hi ↦
    isCompact_of_isOpen_of_measure_ne_top_of_isMulLeftInvariant (hBopen.out i) (μ i) hi

variable {ι : Type*} [Countable ι]
variable {G : ι → Type*} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)]
  [∀ i, SecondCountableTopology (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
variable {K : ι → Type*} [∀ i, SetLike (K i) (G i)] [∀ i, SubgroupClass (K i) (G i)]

/-! ### Private helpers for reference boxes and level pullbacks -/

section Helpers

omit [Countable ι] [∀ i, SecondCountableTopology (G i)] in
/-- Construct a measurable family `C` agreeing with `B` outside `T`, compact on `T`, containing `1`
in its interior at every place, and having positive finite product Haar mass on `T`. -/
@[to_additive]
private theorem exists_compact_measurable_one_mem_interior (B : ∀ i, K i)
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))] (T : Finset ι)
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure] :
    ∃ C : ∀ i, Set (G i),
      (∀ i ∈ T, IsCompact (C i)) ∧ (∀ i, MeasurableSet (C i)) ∧ (∀ i ∉ T, C i = B i) ∧
      (∀ i, (1 : G i) ∈ interior (C i)) ∧
      0 < ∏ i ∈ T, μ i (C i) ∧ (∏ i ∈ T, μ i (C i)) < ⊤ := by
  classical
  choose K₀ hK₀_nhds hK₀_comp hK₀_closed using fun i : ι ↦
    exists_mem_nhds_isCompact_isClosed (1 : G i)
  let C : ∀ i, Set (G i) := fun i ↦ if i ∈ T then K₀ i else (B i : Set (G i))
  have hCcomp (i : ι) (hi : i ∈ T) : IsCompact (C i) := by simpa [C, hi] using hK₀_comp i
  have hCmeas (i : ι) : MeasurableSet (C i) := by
    by_cases hi : i ∈ T <;> [simpa [C, hi] using (hK₀_closed i).measurableSet;
      simpa [C, hi] using (hBopen.out i).measurableSet]
  have hCint (i : ι) : (1 : G i) ∈ interior (C i) := by
    by_cases hi : i ∈ T
    · simpa [C, hi] using mem_interior_iff_mem_nhds.mpr (hK₀_nhds i)
    · simp [C, hi, (hBopen.out i).interior_eq]
  exact ⟨C, hCcomp, hCmeas, fun i hi ↦ by simp [C, hi], hCint,
    CanonicallyOrderedAdd.prod_pos.mpr fun i _ ↦
      (isOpen_interior.measure_pos (μ i) ⟨1, hCint i⟩).trans_le (measure_mono interior_subset),
    ENNReal.prod_lt_top fun i hi ↦ (hCcomp i hi).measure_lt_top⟩

/-- Identify the pullback `ν.comap (levelMonoidHom B T)` of any left Haar measure `ν` on
`Πʳ i, [G i, B i]` that agrees with `∏ i ∈ T, μ i (C i)` on a single box `box C` of positive finite
product mass supported in `T`. -/
@[to_additive]
private theorem comap_levelMonoidHom_eq (B : ∀ i, K i)
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    (hBcompact : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (ν : Measure (Πʳ i, [G i, B i])) [ν.IsHaarMeasure]
    {T : Finset ι} (hT : ∀ i ∉ T, μ i (B i) = 1)
    {C : ∀ i, Set (G i)} (hCB : ∀ i ∉ T, C i = B i)
    (hpos : 0 < ∏ i ∈ T, μ i (C i)) (hlt : (∏ i ∈ T, μ i (C i)) < ⊤)
    (hνC : ν (box C) = ∏ i ∈ T, μ i (C i)) :
    ν.comap (levelMonoidHom B T) =
      (Measure.pi fun i : T ↦ μ i.val).prod
        (Measure.infinitePi fun i : {i // i ∉ T} ↦ (μ i.val).comap Subtype.val) := by
  have _ : LocallyCompactSpace (Πʳ i, [G i, B i]) := locallyCompactSpace_of_group G hBcompact
  have _ (i : {i // i ∉ T}) : ((μ i.val).comap (Subtype.val : B i.val → G i.val)).IsHaarMeasure :=
    IsHaarMeasure.comap (mH := inferInstance) (μ i.val) (f := SubmonoidClass.subtype (B i.val))
      (hBopen.out i.val).isOpenEmbedding_subtypeVal
  have _ (i : {i // i ∉ T}) :
      IsProbabilityMeasure ((μ i.val).comap (Subtype.val : B i.val → G i.val)) :=
    isProbabilityMeasure_comap_subtype (hBopen.out i.val).measurableSet (μ i.val)
      (hT i.val i.property)
  have _ (i : {i // i ∉ T}) : CompactSpace (B i.val) := by
    have _ : LocallyCompactSpace (B i.val) :=
      (hBopen.out i.val).isOpenEmbedding_subtypeVal.locallyCompactSpace
    by_contra hnc
    have _ : NoncompactSpace (B i.val) := not_compactSpace_iff.mp hnc
    exact measure_ne_top ((μ i.val).comap (Subtype.val : B i.val → G i.val)) univ
      (measure_univ_of_isMulLeftInvariant _)
  have _ : (ν.comap (levelMonoidHom B T)).IsHaarMeasure :=
    IsHaarMeasure.comap (mH := inferInstance) ν (isOpenEmbedding_levelMonoidHom B T)
  let E : Set ((Π i : T, G i) × (Π i : {i // i ∉ T}, B i.val)) :=
    (univ.pi fun i : T ↦ C i.val) ×ˢ univ
  have hprod_E : ((Measure.pi fun i : T ↦ μ i.val).prod
      (Measure.infinitePi fun i : {i // i ∉ T} ↦ (μ i.val).comap Subtype.val)) E =
        ∏ i ∈ T, μ i (C i) := by
    rw [Measure.prod_prod, Measure.pi_pi, measure_univ, mul_one,
      Finset.prod_coe_sort T fun i ↦ μ i (C i)]
  have hν_E : (ν.comap (levelMonoidHom B T)) E = ∏ i ∈ T, μ i (C i) := by
    rw [(isOpenEmbedding_levelMonoidHom B T).measurableEmbedding.comap_apply,
      image_levelMonoidHom_pi_prod_univ B T hCB, hνC]
  exact isMulLeftInvariant_eq_of_apply_eq _ _ (hprod_E ▸ hpos.ne') (hprod_E ▸ hlt.ne)
    (hν_E.trans hprod_E.symm)

omit [Countable ι] [∀ i, SecondCountableTopology (G i)] in
/-- Construct a reference box `box Kref` and a normalized left Haar measure `ν` on
`Πʳ i, [G i, B i]` assigning `∏ i ∈ S₀, μ i (Kref i)` to `box Kref`. -/
@[to_additive exists_addHaarMeasure_box_eq_prod]
private theorem exists_haarMeasure_box_eq_prod (B : ∀ i, K i)
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    (hBcompact : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (S₀ : Finset ι) (hS₀_comp : ∀ i ∉ S₀, IsCompact (B i : Set (G i))) :
    ∃ (Kref : ∀ i, Set (G i)) (ν : Measure (Πʳ i, [G i, B i])) (_ : ν.IsHaarMeasure),
      (∀ i, MeasurableSet (Kref i)) ∧ (∀ i ∉ S₀, Kref i = B i) ∧
      0 < ∏ i ∈ S₀, μ i (Kref i) ∧ (∏ i ∈ S₀, μ i (Kref i)) < ⊤ ∧
      ν (box Kref) = ∏ i ∈ S₀, μ i (Kref i) := by
  classical
  have _ : LocallyCompactSpace (Πʳ i, [G i, B i]) := locallyCompactSpace_of_group G hBcompact
  obtain ⟨Kref, hKref_comp_S₀, hKref_meas, hKref_eq, hKref_int, hprod_pos, hprod_lt_top⟩ :=
    exists_compact_measurable_one_mem_interior B S₀ μ
  have hKref_comp (i : ι) : IsCompact (Kref i) :=
    if hi : i ∈ S₀ then hKref_comp_S₀ i hi else hKref_eq i hi ▸ hS₀_comp i hi
  have hboxK_comp : IsCompact (box Kref : Set (Πʳ i, [G i, B i])) :=
    isCompact_box hKref_comp <| Filter.Eventually.mono S₀.finite_toSet.compl_mem_cofinite
      fun i hi ↦ (hKref_eq i (Finset.mem_coe.not.mp hi)).subset
  have hboxK_int : (interior (box Kref : Set (Πʳ i, [G i, B i]))).Nonempty :=
    ⟨1, box_interior_subset_interior_box
      (Filter.Eventually.mono S₀.finite_toSet.compl_mem_cofinite fun i hi ↦ by
        rw [hKref_eq i (Finset.mem_coe.not.mp hi), (hBopen.out i).interior_eq])
      (mem_box.mpr hKref_int)⟩
  let Kpos : TopologicalSpace.PositiveCompacts (Πʳ i, [G i, B i]) :=
    ⟨⟨box Kref, hboxK_comp⟩, hboxK_int⟩
  let c₀ : ℝ≥0 := ∏ i ∈ S₀, (μ i (Kref i)).toNNReal
  have hc₀_pos : 0 < c₀ := Finset.prod_pos fun i hi ↦
    ENNReal.toNNReal_pos (pos_of_gt (CanonicallyOrderedAdd.prod_pos.mp hprod_pos i hi)).ne'
      (hKref_comp i).measure_lt_top.ne
  refine ⟨Kref, c₀ • haarMeasure Kpos, IsHaarMeasure.nnreal_smul _ hc₀_pos.ne', hKref_meas,
    hKref_eq, hprod_pos, hprod_lt_top, ?_⟩
  have hK : haarMeasure Kpos (box Kref) = 1 := haarMeasure_self
  rw [coe_nnreal_smul_apply, hK, mul_one, ENNReal.ofNNReal_finsetProd]
  exact Finset.prod_congr rfl fun i _ ↦ ENNReal.coe_toNNReal (hKref_comp i).measure_lt_top.ne

omit [Countable ι] [∀ i, SecondCountableTopology (G i)] in
/-- Open subgroups `B i` of `μ i`-mass `1` are compact, so `μ i (B i) = 1` cofinitely forces
cofinite compactness of `B i`. -/
@[to_additive]
private theorem eventually_isCompact_of_eventually_measure_eq_one (B : ∀ i, K i)
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμB : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)) :=
  hμB.mono fun i hi ↦
    isCompact_of_isOpen_of_measure_ne_top_of_isMulLeftInvariant (hBopen.out i) (μ i) (by simp [hi])

end Helpers

/-! ### Normalized restricted products of local Haar measures -/

section NormalizedRestrictedHaar

section
variable (B : ∀ i, K i) [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
  (μ : ∀ i, Measure (G i)) [hμ : ∀ i, (μ i).IsHaarMeasure]
  (hμB : ∀ᶠ i in cofinite, μ i (B i) = 1)
include hBopen hμ hμB

/-- On a restricted product `Πʳ i, [G i, B i]` where `B i` is compact and `μ i (B i) = 1` at all
but finitely many indices, there exists a unique left Haar measure `ν` assigning measure
`∏ᶠ i, μ i (C i)` to every measurable coordinate box `box C` agreeing cofinitely with `B i`. -/
@[to_additive /-- On a restricted product `Πʳ i, [G i, B i]` of locally compact additive groups
where `B i` is compact and `μ i (B i) = 1` at all but finitely many indices, there exists a unique
left-invariant additive Haar measure `ν` assigning measure `∏ᶠ i, μ i (C i)` to every measurable
coordinate box `box C` agreeing cofinitely with `B i`. -/]
theorem exists_unique_restrictedHaar :
    ∃! ν : Measure (Πʳ i, [G i, B i]),
      ν.IsHaarMeasure ∧
      ∀ C : ∀ i, Set (G i), (∀ i, MeasurableSet (C i)) → (∀ᶠ i in cofinite, C i = B i) →
        ν (box C) = ∏ᶠ i, μ i (C i) := by
  classical
  have hBcompact := eventually_isCompact_of_eventually_measure_eq_one B μ hμB
  have _ : LocallyCompactSpace (Πʳ i, [G i, B i]) := locallyCompactSpace_of_group G hBcompact
  let S₀ : Finset ι := (mem_cofinite.mp (hBcompact.and hμB)).toFinset
  have hS₀ (i : ι) (hi : i ∉ S₀) : IsCompact (B i : Set (G i)) ∧ μ i (B i) = 1 :=
    Classical.byContradiction fun hnot ↦ hi ((Set.Finite.mem_toFinset _).mpr hnot)
  obtain ⟨Kref, ν, _, hKref_meas, hKref_eq, hprod_pos, hprod_lt_top, hν_Kref⟩ :=
    exists_haarMeasure_box_eq_prod B hBcompact μ S₀ fun i hi ↦ (hS₀ i hi).1
  -- Evaluate `ν` on any cofinitely-`B` box `box C` by pulling back to `T := S₀ ∪ ...`.
  have hν_box (C : ∀ i, Set (G i)) (_ : ∀ i, MeasurableSet (C i))
      (hCB : ∀ᶠ i in cofinite, C i = B i) : ν (box C) = ∏ᶠ i, μ i (C i) := by
    let T : Finset ι := S₀ ∪ (mem_cofinite.mp hCB).toFinset
    have hS₀T : S₀ ⊆ T := Finset.subset_union_left
    have hT_one (i : ι) (hi : i ∉ T) : μ i (B i) = 1 := (hS₀ i fun h ↦ hi (hS₀T h)).2
    have hCBT (i : ι) (hi : i ∉ T) : C i = B i := Classical.byContradiction fun hnot ↦
      hi (Finset.subset_union_right ((Set.Finite.mem_toFinset _).mpr hnot))
    have hKref_prodT : ∏ i ∈ T, μ i (Kref i) = ∏ i ∈ S₀, μ i (Kref i) :=
      (Finset.prod_subset hS₀T fun i _ hiS₀ ↦ by rw [hKref_eq i hiS₀, (hS₀ i hiS₀).2]).symm
    have _ (i : {i // i ∉ T}) :
        IsProbabilityMeasure ((μ i.val).comap (Subtype.val : B i.val → G i.val)) :=
      isProbabilityMeasure_comap_subtype (hBopen.out i.val).measurableSet (μ i.val)
        (hT_one i.val i.property)
    rw [← image_levelMonoidHom_pi_prod_univ B T hCBT,
      ← (isOpenEmbedding_levelMonoidHom B T).measurableEmbedding.comap_apply,
      comap_levelMonoidHom_eq B hBcompact μ ν hT_one
        (fun i hi ↦ hKref_eq i fun h ↦ hi (hS₀T h))
        (hKref_prodT.symm ▸ hprod_pos) (hKref_prodT.symm ▸ hprod_lt_top)
        (hν_Kref.trans hKref_prodT.symm),
      Measure.prod_prod, Measure.pi_pi, measure_univ, mul_one,
      Finset.prod_coe_sort T fun i ↦ μ i (C i)]
    exact (finprod_eq_prod_of_mulSupport_subset _ (s := T) fun i hi ↦
      Classical.byContradiction fun hiT ↦ hi (by rw [hCBT i hiT, hT_one i hiT])).symm
  -- Any two left Haar measures agreeing on `box Kref` coincide by Haar uniqueness.
  have hKref_cof : ∀ᶠ i in cofinite, Kref i = B i :=
    Filter.Eventually.mono S₀.finite_toSet.compl_mem_cofinite fun i hi ↦
      hKref_eq i (Finset.mem_coe.not.mp hi)
  refine ⟨ν, ⟨inferInstance, hν_box⟩, fun ν' ⟨_, hν'_box⟩ ↦
    isMulLeftInvariant_eq_of_apply_eq ν' ν (hν_Kref ▸ hprod_pos.ne') (hν_Kref ▸ hprod_lt_top.ne)
      ((hν'_box Kref hKref_meas hKref_cof).trans (hν_box Kref hKref_meas hKref_cof).symm)⟩

/-- The canonical restricted Haar measure on `Πʳ i, [G i, B i]` attached to local Haar measures
`μ i` normalized by `μ i (B i) = 1` at all but finitely many indices. -/
@[to_additive /-- The canonical restricted additive Haar measure on `Πʳ i, [G i, B i]` attached to
local additive Haar measures `μ i` normalized by `μ i (B i) = 1` at all but finitely many
indices. -/]
def restrictedHaar : Measure (Πʳ i, [G i, B i]) :=
  (exists_unique_restrictedHaar B μ hμB).choose

/-- `restrictedHaar` is a left Haar measure on `Πʳ i, [G i, B i]`. -/
@[to_additive /-- `restrictedAddHaar` is a left-invariant additive Haar measure on
`Πʳ i, [G i, B i]`. -/]
instance isHaarMeasure_restrictedHaar : (restrictedHaar B μ hμB).IsHaarMeasure :=
  (exists_unique_restrictedHaar B μ hμB).choose_spec.1.1

/-- Uniqueness of `restrictedHaar`: any left Haar measure assigning `∏ᶠ i, μ i (C i)` to every
measurable coordinate box `box C` agreeing cofinitely with `B i` coincides with
`restrictedHaar`. -/
@[to_additive /-- Uniqueness of `restrictedAddHaar`: any left-invariant additive Haar measure
assigning `∏ᶠ i, μ i (C i)` to every measurable coordinate box `box C` agreeing cofinitely with
`B i` coincides with `restrictedAddHaar`. -/]
theorem restrictedHaar_unique {ν : Measure (Πʳ i, [G i, B i])} [ν.IsHaarMeasure]
    (hν : ∀ C : ∀ i, Set (G i), (∀ i, MeasurableSet (C i)) → (∀ᶠ i in cofinite, C i = B i) →
      ν (box C) = ∏ᶠ i, μ i (C i)) :
    ν = restrictedHaar B μ hμB :=
  (exists_unique_restrictedHaar B μ hμB).choose_spec.2 ν ⟨inferInstance, hν⟩

/-- Pulling `restrictedHaar` back along `levelMonoidHom B T` (for any finite set `T` outside which
`μ i (B i) = 1`) recovers the product of the finite product Haar measure on `Π i : T, G i` with
Kolmogorov's infinite product probability Haar measure on `Π i : {i // i ∉ T}, B i`. -/
@[to_additive /-- Pulling `restrictedAddHaar` back along `levelAddMonoidHom B T` (for any finite set
`T` outside which `μ i (B i) = 1`) recovers the product of the finite product additive Haar measure
on `Π i : T, G i` with Kolmogorov's infinite product probability additive Haar measure on
`Π i : {i // i ∉ T}, B i`. -/]
theorem comap_levelMonoidHom_restrictedHaar {T : Finset ι} (hT : ∀ i ∉ T, μ i (B i) = 1) :
    (restrictedHaar B μ hμB).comap (levelMonoidHom B T) =
      restrictedPrincipalPieceMeasure B T μ := by
  classical
  have hBcompact := eventually_isCompact_of_eventually_measure_eq_one B μ hμB
  rw [restrictedPrincipalPieceMeasure_def]
  obtain ⟨C, -, hCmeas, hCB, -, hpos, hlt⟩ := exists_compact_measurable_one_mem_interior B T μ
  refine comap_levelMonoidHom_eq B hBcompact μ (restrictedHaar B μ hμB) hT hCB hpos hlt ?_
  rw [restrictedHaar, (exists_unique_restrictedHaar B μ hμB).choose_spec.1.2 C hCmeas
    (Filter.Eventually.mono T.finite_toSet.compl_mem_cofinite fun i hi ↦
      hCB i (Finset.mem_coe.not.mp hi))]
  exact finprod_eq_prod_of_mulSupport_subset _ (s := T) fun i hi ↦
    Classical.byContradiction fun hiT ↦ hi (by dsimp only; rw [hCB i hiT, hT i hiT])

/-- Pulling `restrictedHaar` back to `levelOpenSubgroup B T _` (for any finite set `T` with
`μ i (B i) = 1` for every `i ∉ T`) identifies it via `levelOpenSubgroupEquiv` with
`restrictedPrincipalPieceMeasure B T μ`. -/
@[to_additive /-- Pulling `restrictedAddHaar` back to `levelOpenAddSubgroup B T _` (for any finite
set `T` with `μ i (B i) = 1` for every `i ∉ T`) identifies it via `levelOpenAddSubgroupEquiv` with
`restrictedPrincipalPieceMeasure B T μ`. -/]
theorem comap_levelOpenSubgroup_restrictedHaar {T : Finset ι} (hT : ∀ i ∉ T, μ i (B i) = 1) :
    (restrictedHaar B μ hμB).comap
        ((↑) : levelOpenSubgroup B T (fun i _ ↦ hBopen.out i) → Πʳ i, [G i, B i]) =
      (restrictedPrincipalPieceMeasure B T μ).map
        (levelOpenSubgroupEquiv B T fun i _ ↦ hBopen.out i) := by
  let U := levelOpenSubgroup B T fun i _ ↦ hBopen.out i
  let e := levelOpenSubgroupEquiv B T fun i _ ↦ hBopen.out i
  have hmu : MeasurableEmbedding (Subtype.val : U → Πʳ i, [G i, B i]) :=
    MeasurableEmbedding.subtypeVal U.isOpen.measurableSet
  have he : (e : _ → _) = e.toHomeomorph.toMeasurableEquiv :=
    e.toHomeomorph.toMeasurableEquiv_coe.symm
  rw [eq_comm, he, e.toHomeomorph.toMeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq,
    MeasurableEquiv.map_symm, hmu.comap_comap, ← he, coe_comp_levelOpenSubgroupEquiv,
    comap_levelMonoidHom_restrictedHaar B μ hμB hT]

/-- Value of `restrictedHaar` on a coordinate box `box C` agreeing with `B i` outside a finite set
`T` on whose complement `μ i (B i) = 1`. No measurability assumption on `C i` is needed. -/
@[to_additive /-- Value of `restrictedAddHaar` on a coordinate box `box C` agreeing with `B i`
outside a finite set `T` on whose complement `μ i (B i) = 1`. No measurability assumption on `C i`
is needed. -/]
theorem restrictedHaar_box {T : Finset ι} (hT : ∀ i ∉ T, μ i (B i) = 1)
    {C : ∀ i, Set (G i)} (hCB : ∀ i ∉ T, C i = B i) :
    restrictedHaar B μ hμB (box C) = ∏ i ∈ T, μ i (C i) := by
  have _ (i : {i // i ∉ T}) :
      IsProbabilityMeasure ((μ i.val).comap (Subtype.val : B i.val → G i.val)) :=
    isProbabilityMeasure_comap_subtype (hBopen.out i.val).measurableSet (μ i.val)
      (hT i.val i.property)
  rw [← image_levelMonoidHom_pi_prod_univ B T hCB,
    ← (isOpenEmbedding_levelMonoidHom B T).measurableEmbedding.comap_apply,
    comap_levelMonoidHom_restrictedHaar B μ hμB hT, restrictedPrincipalPieceMeasure_def,
    Measure.prod_prod, Measure.pi_pi, measure_univ, mul_one,
    Finset.prod_coe_sort T fun i ↦ μ i (C i)]

/-- `restrictedHaar` evaluates on any coordinate box `box C` agreeing cofinitely with `B i` as the
finitary product `∏ᶠ i, μ i (C i)`. -/
@[to_additive restrictedAddHaar_box_eq_finprod
/-- `restrictedAddHaar` evaluates on any coordinate box `box C` agreeing cofinitely with `B i` as
the finitary product `∏ᶠ i, μ i (C i)`. -/]
theorem restrictedHaar_box_eq_finprod {C : ∀ i, Set (G i)} (hCB : ∀ᶠ i in cofinite, C i = B i) :
    restrictedHaar B μ hμB (box C) = ∏ᶠ i, μ i (C i) := by
  classical
  let T : Finset ι := (mem_cofinite.mp (hμB.and hCB)).toFinset
  have hT (i : ι) (hi : i ∉ T) : μ i (B i) = 1 ∧ C i = B i :=
    Classical.byContradiction fun hnot ↦ hi ((Set.Finite.mem_toFinset _).mpr hnot)
  rw [restrictedHaar_box B μ hμB (fun i hi ↦ (hT i hi).1) (fun i hi ↦ (hT i hi).2)]
  exact (finprod_eq_prod_of_mulSupport_subset _ (s := T) fun i hi ↦
    Classical.byContradiction fun hiT ↦ hi (by rw [(hT i hiT).2, (hT i hiT).1])).symm

/-- The everywhere-integral box `box B` has `restrictedHaar` measure `∏ᶠ i, μ i (B i)`. -/
@[to_additive (attr := simp) /-- The everywhere-integral box `box B` has `restrictedAddHaar`
measure `∏ᶠ i, μ i (B i)`. -/]
theorem restrictedHaar_box_self :
    restrictedHaar B μ hμB (box fun i ↦ (B i : Set (G i))) = ∏ᶠ i, μ i (B i) :=
  restrictedHaar_box_eq_finprod B μ hμB (.of_forall fun _ ↦ rfl)

/-- `restrictedHaar` is a regular measure on `Πʳ i, [G i, B i]`. -/
@[to_additive /-- `restrictedAddHaar` is a regular measure on `Πʳ i, [G i, B i]`. -/]
instance regular_restrictedHaar : (restrictedHaar B μ hμB).Regular := by
  have _ : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    locallyCompactSpace_of_group G (eventually_isCompact_of_eventually_measure_eq_one B μ hμB)
  rw [isMulLeftInvariant_eq_smul (restrictedHaar B μ hμB) haar]
  infer_instance

/-- `restrictedHaar` is a locally finite measure on `Πʳ i, [G i, B i]`. -/
@[to_additive /-- `restrictedAddHaar` is a locally finite measure on `Πʳ i, [G i, B i]`. -/]
instance isLocallyFiniteMeasure_restrictedHaar :
    IsLocallyFiniteMeasure (restrictedHaar B μ hμB) := by
  have _ : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    locallyCompactSpace_of_group G (eventually_isCompact_of_eventually_measure_eq_one B μ hμB)
  infer_instance

/-- `restrictedHaar` is a σ-finite measure on `Πʳ i, [G i, B i]`. -/
@[to_additive /-- `restrictedAddHaar` is a σ-finite measure on `Πʳ i, [G i, B i]`. -/]
instance sigmaFinite_restrictedHaar : SigmaFinite (restrictedHaar B μ hμB) := by
  have _ : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
    locallyCompactSpace_of_group G (eventually_isCompact_of_eventually_measure_eq_one B μ hμB)
  infer_instance

/-- For any finite set `T` outside which `μ i (B i) = 1`, `levelMonoidHom B T` is
measure-preserving from `restrictedPrincipalPieceMeasure B T μ` onto the restriction of
`restrictedHaar` to the principal piece `{x | ∀ i ∉ T, x i ∈ B i}`. -/
@[to_additive /-- For any finite set `T` outside which `μ i (B i) = 1`, `levelAddMonoidHom B T` is
measure-preserving from `restrictedPrincipalPieceMeasure B T μ` onto the restriction of
`restrictedAddHaar` to the principal piece `{x | ∀ i ∉ T, x i ∈ B i}`. -/]
theorem measurePreserving_restrictedHaar_levelMonoidHom {T : Finset ι}
    (hT : ∀ i ∉ T, μ i (B i) = 1) :
    MeasurePreserving (levelMonoidHom B T) (restrictedPrincipalPieceMeasure B T μ)
      ((restrictedHaar B μ hμB).restrict {x | ∀ i ∉ T, x i ∈ B i}) := by
  have hemb := (isOpenEmbedding_levelMonoidHom B T).measurableEmbedding
  refine ⟨hemb.measurable, ?_⟩
  rw [← comap_levelMonoidHom_restrictedHaar B μ hμB hT, hemb.map_comap, range_levelMonoidHom]

/-- **Uniqueness of `restrictedHaar` among all measures.** Any measure on `Πʳ i, [G i, B i]` (not
assumed left-invariant or finite on compacts) giving every open coordinate box `box C` with
`C i = B i` cofinitely the mass `∏ᶠ i, μ i (C i)` equals `restrictedHaar`. -/
@[to_additive /-- **Uniqueness of `restrictedAddHaar` among all measures.** Any measure on
`Πʳ i, [G i, B i]` (not assumed left-invariant or finite on compacts) giving every open coordinate
box `box C` with `C i = B i` cofinitely the mass `∏ᶠ i, μ i (C i)` equals `restrictedAddHaar`. -/]
theorem eq_restrictedHaar_of_box {ν : Measure (Πʳ i, [G i, B i])}
    (hν : ∀ C : ∀ i, Set (G i), (∀ i, IsOpen (C i)) → (∀ᶠ i in cofinite, C i = B i) →
      ν (box C) = ∏ᶠ i, μ i (C i)) :
    ν = restrictedHaar B μ hμB := by
  classical
  have h_eq (s) (hs : s ∈ cofiniteOpenBoxes G fun i ↦ (B i : Set (G i))) :
      ν s = restrictedHaar B μ hμB s := by
    obtain ⟨C, hC, hCB, rfl⟩ := mem_cofiniteOpenBoxes_iff.mp hs
    rw [hν C hC hCB, restrictedHaar_box_eq_finprod B μ hμB hCB]
  -- Cover `Πʳ i, [G i, B i]` by open coordinate boxes of finite `ν`-measure.
  let T₀ : Set (Set (Πʳ i, [G i, B i])) :=
    {s ∈ cofiniteOpenBoxes G fun i ↦ (B i : Set (G i)) | ν s ≠ ∞}
  have hT₀_open (s) (hs : s ∈ T₀) : IsOpen s := by
    obtain ⟨C, hC, hCB, rfl⟩ := mem_cofiniteOpenBoxes_iff.mp (mem_sep_iff.mp hs).1
    exact isOpen_box_of_eventually_eq hC hCB
  have hT₀_univ : ⋃₀ T₀ = univ := by
    refine eq_univ_iff_forall.mpr fun x ↦ mem_sUnion.mpr ?_
    have hfin := mem_cofinite.mp (x.eventually.and hμB)
    let F : Finset ι := hfin.toFinset
    have hF (i : ι) (hi : i ∉ F) : x i ∈ (B i : Set (G i)) ∧ μ i (B i) = 1 :=
      Classical.byContradiction fun h ↦ hi (hfin.mem_toFinset.mpr h)
    choose L hLcomp hLnhds using fun i ↦ exists_compact_mem_nhds (x i)
    let C : ∀ i, Set (G i) := fun i ↦ if i ∈ F then interior (L i) else B i
    have hCopen (i : ι) : IsOpen (C i) := by
      by_cases hi : i ∈ F
      · simpa only [C, hi, ↓reduceIte] using isOpen_interior
      · simpa only [C, hi, ↓reduceIte] using hBopen.out i
    have hCB : ∀ᶠ i in cofinite, C i = B i :=
      Filter.Eventually.mono F.finite_toSet.compl_mem_cofinite fun i hi ↦
        ite_eq_right (Finset.mem_coe.not.mp hi)
    have hfp : ∏ᶠ i, μ i (C i) = ∏ i ∈ F, μ i (C i) :=
      finprod_eq_prod_of_mulSupport_subset _ fun i hi ↦ Classical.byContradiction fun hiF ↦
        hi (by simp only [C, ite_eq_right (Finset.mem_coe.not.mp hiF),
          (hF i (Finset.mem_coe.not.mp hiF)).2])
    refine ⟨box C, mem_sep_iff.mpr ⟨mem_cofiniteOpenBoxes_iff.mpr ⟨C, hCopen, hCB, rfl⟩, ?_⟩,
      mem_box.mpr fun i ↦ ?_⟩
    · rw [hν C hCopen hCB, hfp]
      refine (ENNReal.prod_lt_top fun i hi ↦ ?_).ne
      simpa only [C, hi, ↓reduceIte] using
        (measure_mono interior_subset).trans_lt (hLcomp i).measure_lt_top
    · by_cases hi : i ∈ F
      · simpa only [C, hi, ↓reduceIte] using mem_interior_iff_mem_nhds.mpr (hLnhds i)
      · simpa only [C, hi, ↓reduceIte] using (hF i hi).1
  -- Extract a countable subcover by second countability and apply the π-λ uniqueness theorem.
  obtain ⟨T, hTc, hTsub, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable T₀ hT₀_open
  exact ext_of_generateFrom_of_cover_subset
    (measurableSpace_eq_generateFrom_cofiniteOpenBoxes (.of_forall hBopen.out))
    isPiSystem_cofiniteOpenBoxes (hTsub.trans fun _ h ↦ (mem_sep_iff.mp h).1) hTc
    (hTU.trans hT₀_univ) (fun s hs ↦ (mem_sep_iff.mp (hTsub hs)).2) h_eq

/-- If every local Haar measure `μ i` is inversion-invariant, then `restrictedHaar` is also
inversion-invariant. -/
@[to_additive /-- If every local additive Haar measure `μ i` is negation-invariant, then
`restrictedAddHaar` is also negation-invariant. -/]
instance isInvInvariant_restrictedHaar [∀ i, (μ i).IsInvInvariant] :
    (restrictedHaar B μ hμB).IsInvInvariant where
  inv_eq_self := by
    refine eq_restrictedHaar_of_box B μ hμB fun C _ hCB ↦ ?_
    have hCB' : ∀ᶠ i in cofinite, (C i)⁻¹ = B i := by
      filter_upwards [hCB] with i hiC
      ext y
      simp [hiC]
    rw [Measure.inv_apply, inv_box, restrictedHaar_box_eq_finprod B μ hμB hCB']
    simp_rw [measure_inv]

/-- If every local Haar measure `μ i` is right-invariant (i.e. each `G i` is unimodular), then
`restrictedHaar` is also right-invariant. -/
@[to_additive /-- If every local additive Haar measure `μ i` is right-translation-invariant, then
`restrictedAddHaar` is also right-translation-invariant. -/]
instance isMulRightInvariant_restrictedHaar [∀ i, (μ i).IsMulRightInvariant] :
    (restrictedHaar B μ hμB).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    have _ : LocallyCompactSpace (Πʳ i, [G i, B i]) :=
      locallyCompactSpace_of_group G (eventually_isCompact_of_eventually_measure_eq_one B μ hμB)
    refine restrictedHaar_unique B μ hμB fun C hCmeas hCB ↦ ?_
    have hCB' : ∀ᶠ i in cofinite, (· * g i) ⁻¹' C i = B i := by
      filter_upwards [hCB, g.eventually] with i hiC hig
      ext x
      simpa [hiC] using mul_mem_cancel_right hig
    rw [map_apply (measurable_mul_const g) (measurableSet_box hCmeas), preimage_mul_right_box,
      restrictedHaar_box_eq_finprod B μ hμB hCB']
    exact finprod_congr fun i ↦ measure_preimage_mul_right (μ i) (g i) (C i)

end

/-- **Independence of the integral model for `restrictedHaar`.** If two families of open subgroups
`U` and `U'` agree cofinitely, then `restrictedProductCongr U U' h` pushes `restrictedHaar` for `U`
directly to `restrictedHaar` for `U'` with no scalar factor. -/
@[to_additive map_addRestrictedProductCongr_restrictedAddHaar
/-- **Independence of the integral model for `restrictedAddHaar`.** If two families of open additive
subgroups `U` and `U'` agree cofinitely, then `addRestrictedProductCongr U U' h` pushes
`restrictedAddHaar` for `U` directly to `restrictedAddHaar` for `U'` with no scalar factor. -/]
theorem map_restrictedProductCongr_restrictedHaar (U U' : ∀ i, Subgroup (G i))
    [Fact (∀ i, IsOpen (U i : Set (G i)))] [Fact (∀ i, IsOpen (U' i : Set (G i)))]
    (h : ∀ᶠ i in cofinite, U i = U' i)
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμU : ∀ᶠ i in cofinite, μ i (U i) = 1) (hμU' : ∀ᶠ i in cofinite, μ i (U' i) = 1) :
    (restrictedHaar U μ hμU).map (restrictedProductCongr U U' h) =
      restrictedHaar U' μ hμU' := by
  have _ : LocallyCompactSpace (Πʳ i, [G i, (U' i : Set (G i))]) :=
    locallyCompactSpace_of_group G (eventually_isCompact_of_eventually_measure_eq_one U' μ hμU')
  have _ : ((restrictedHaar U μ hμU).map
      (restrictedProductCongr U U' h)).IsHaarMeasure :=
    (restrictedProductCongr U U' h).isHaarMeasure_map (restrictedHaar U μ hμU)
      (continuous_restrictedProductCongr U U' h) (continuous_restrictedProductCongr_symm U U' h)
  refine restrictedHaar_unique U' μ hμU' fun C hCmeas hCU' ↦ ?_
  rw [map_apply (continuous_restrictedProductCongr U U' h).measurable (measurableSet_box hCmeas),
    preimage_restrictedProductCongr_box,
    restrictedHaar_box_eq_finprod U μ hμU
      (by filter_upwards [hCU', h] with i h1 h2; rw [h1, h2])]

end NormalizedRestrictedHaar

/-! ### Convergent restricted products of local Haar measures -/

section ConvergentHaarProduct

section
variable (B : ∀ i, K i) [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
  (S : Finset ι) (hBcompact : ∀ i ∉ S, IsCompact (B i : Set (G i)))
  (μ : ∀ i, Measure (G i)) [hμ : ∀ i, (μ i).IsHaarMeasure]
include hBopen hBcompact hμ

omit [Countable ι] [∀ i, LocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)] in
/-- Rescale local Haar measures `μ i` outside `S` by `((μ i (B i)).toNNReal)⁻¹` so that `μ' i`
has `μ' i (B i) = 1` outside `S`, agrees with `μ i` on `S`, and preserves right invariance. -/
@[to_additive]
private theorem exists_normalized_localHaar :
    ∃ (μ' : ∀ i, Measure (G i)) (_ : ∀ i, (μ' i).IsHaarMeasure),
      (∀ i, [IsMulRightInvariant (μ i)] → IsMulRightInvariant (μ' i)) ∧
      (∀ i ∈ S, μ' i = μ i) ∧ (∀ i ∉ S, μ' i = ((μ i (B i)).toNNReal)⁻¹ • μ i) ∧
      (∀ i ∉ S, μ' i (B i) = 1) ∧ (∀ᶠ i in cofinite, IsCompact (B i : Set (G i))) ∧
      (∀ᶠ i in cofinite, μ' i (B i) = 1) := by
  classical
  have hB_pos (i : ι) : 0 < μ i (B i) := (hBopen.out i).measure_pos (μ i) ⟨1, one_mem (B i)⟩
  let μ' : ∀ i, Measure (G i) := fun i ↦ if i ∈ S then μ i else ((μ i (B i)).toNNReal)⁻¹ • μ i
  have hμ'_haar (i : ι) : (μ' i).IsHaarMeasure := by
    by_cases hi : i ∈ S
    · simp only [μ', hi, ↓reduceIte]; infer_instance
    · simp only [μ', hi, ↓reduceIte]
      exact IsHaarMeasure.nnreal_smul (μ i)
        (inv_ne_zero (ENNReal.toNNReal_pos (hB_pos i).ne' (hBcompact i hi).measure_lt_top.ne).ne')
  have hμ'_right (i : ι) [IsMulRightInvariant (μ i)] : IsMulRightInvariant (μ' i) := by
    by_cases hi : i ∈ S <;> simp only [μ', hi, ↓reduceIte] <;> infer_instance
  have hμ'B_out (i : ι) (hi : i ∉ S) : μ' i (B i) = 1 := by
    have hlt : μ i (B i) < ⊤ := (hBcompact i hi).measure_lt_top
    simp only [μ', hi, ↓reduceIte, coe_nnreal_smul_apply,
      ENNReal.coe_inv (ENNReal.toNNReal_pos (hB_pos i).ne' hlt.ne).ne',
      ENNReal.coe_toNNReal hlt.ne]
    exact ENNReal.inv_mul_cancel (hB_pos i).ne' hlt.ne
  exact ⟨μ', hμ'_haar, hμ'_right, fun i hi ↦ by simp [μ', hi], fun i hi ↦ by simp [μ', hi],
    hμ'B_out,
    Filter.Eventually.mono S.finite_toSet.compl_mem_cofinite fun i hi ↦
      hBcompact i (Finset.mem_coe.not.mp hi),
    Filter.Eventually.mono S.finite_toSet.compl_mem_cofinite fun i hi ↦
      hμ'B_out i (Finset.mem_coe.not.mp hi)⟩

section
variable (hconv : Summable fun i : {i // i ∉ S} ↦ |(μ i.val (B i.val)).toReal - 1|)
include hconv

/-- Evaluate the rescaled `restrictedHaar` measure on any coordinate box `box C` agreeing with `B`
outside `T ⊇ S`, without measurability assumptions on `C`. -/
@[to_additive smul_restrictedAddHaar_box]
private theorem smul_restrictedHaar_box (μ' : ∀ i, Measure (G i)) [∀ i, (μ' i).IsHaarMeasure]
    (hμ'_mem : ∀ i ∈ S, μ' i = μ i) (hμ'_notMem : ∀ i ∉ S, μ' i = ((μ i (B i)).toNNReal)⁻¹ • μ i)
    (hμ'B : ∀ᶠ i in cofinite, μ' i (B i) = 1)
    {T : Finset ι} (hST : S ⊆ T) {C : ∀ i, Set (G i)} (hCB : ∀ i ∉ T, C i = B i) :
    (Real.toNNReal (∏' i : {i // i ∉ S}, (μ i.val (B i.val)).toReal) •
      restrictedHaar B μ' hμ'B) (box C) =
      (∏ i ∈ T, μ i (C i)) * ENNReal.ofReal (∏' i : {i // i ∉ T}, (μ i.val (B i.val)).toReal) := by
  classical
  have hB_pos (i : ι) : 0 < μ i (B i) := (hBopen.out i).measure_pos (μ i) ⟨1, one_mem (B i)⟩
  have hB_lt_top {i : ι} (hi : i ∉ S) : μ i (B i) < ⊤ := (hBcompact i hi).measure_lt_top
  have hB_toReal_pos {i : ι} (hi : i ∉ S) : 0 < (μ i (B i)).toReal :=
    ENNReal.toReal_pos (hB_pos i).ne' (hB_lt_top hi).ne
  have hμ'_apply {i : ι} (hi : i ∉ S) (s : Set (G i)) : μ' i s = (μ i (B i))⁻¹ * μ i s := by
    rw [hμ'_notMem i hi, coe_nnreal_smul_apply,
      ENNReal.coe_inv (ENNReal.toNNReal_pos (hB_pos i).ne' (hB_lt_top hi).ne).ne',
      ENNReal.coe_toNNReal (hB_lt_top hi).ne]
  have hT_one (i : ι) (hi : i ∉ T) : μ' i (B i) = 1 := by
    have hiS : i ∉ S := fun h ↦ hi (hST h)
    rw [hμ'_apply hiS, ENNReal.inv_mul_cancel (hB_pos i).ne' (hB_lt_top hiS).ne]
  -- Split the Euler factor outside `S` across `T \ S` and the tail outside `T`.
  have hcS : (Real.toNNReal (∏' i : {i // i ∉ S}, (μ i.val (B i.val)).toReal) : ℝ≥0∞) =
      (∏ i ∈ T \ S, μ i (B i)) *
        ENNReal.ofReal (∏' i : {i // i ∉ T}, (μ i.val (B i.val)).toReal) := by
    rw [ENNReal.ofNNReal_toNNReal,
      tprod_split_finset hST (fun i ↦ (μ i (B i)).toReal) (fun _ hi ↦ hB_toReal_pos hi) hconv,
      ENNReal.ofReal_mul
        (Finset.prod_nonneg fun i hi ↦ (hB_toReal_pos (Finset.mem_sdiff.mp hi).2).le),
      ENNReal.ofReal_prod_of_nonneg fun i hi ↦ (hB_toReal_pos (Finset.mem_sdiff.mp hi).2).le]
    congr 1
    exact Finset.prod_congr rfl fun i hi ↦
      ENNReal.ofReal_toReal (hB_lt_top (Finset.mem_sdiff.mp hi).2).ne
  -- Split `∏ i ∈ T, μ' i (C i)` across `S` and `T \ S` and cancel `μ i (B i)`.
  have hprod : (∏ i ∈ T \ S, μ i (B i)) * (∏ i ∈ T, μ' i (C i)) = ∏ i ∈ T, μ i (C i) := by
    have hT_split : (∏ i ∈ T, μ' i (C i)) =
        (∏ i ∈ S, μ' i (C i)) * (∏ i ∈ T \ S, μ' i (C i)) := by
      rw [← Finset.prod_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hST]
    have hS : (∏ i ∈ S, μ' i (C i)) = ∏ i ∈ S, μ i (C i) :=
      Finset.prod_congr rfl fun i hi ↦ by rw [hμ'_mem i hi]
    have hTS : (∏ i ∈ T \ S, μ i (B i) * μ' i (C i)) = ∏ i ∈ T \ S, μ i (C i) :=
      Finset.prod_congr rfl fun i hi ↦ by
        have hiS := (Finset.mem_sdiff.mp hi).2
        rw [hμ'_apply hiS, ← mul_assoc,
          ENNReal.mul_inv_cancel (hB_pos i).ne' (hB_lt_top hiS).ne, one_mul]
    rw [hT_split, ← mul_assoc, mul_comm (∏ i ∈ T \ S, _), mul_assoc, ← Finset.prod_mul_distrib,
      hS, hTS, ← Finset.prod_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hST]
  rw [coe_nnreal_smul_apply, restrictedHaar_box B μ' hμ'B hT_one hCB, hcS]
  calc ((∏ i ∈ T \ S, μ i (B i)) *
          ENNReal.ofReal (∏' i : {i // i ∉ T}, (μ i.val (B i.val)).toReal)) * (∏ i ∈ T, μ' i (C i))
      = ((∏ i ∈ T \ S, μ i (B i)) * (∏ i ∈ T, μ' i (C i))) *
          ENNReal.ofReal (∏' i : {i // i ∉ T}, (μ i.val (B i.val)).toReal) := by ac_rfl
    _ = (∏ i ∈ T, μ i (C i)) *
          ENNReal.ofReal (∏' i : {i // i ∉ T}, (μ i.val (B i.val)).toReal) := by rw [hprod]

/-- **Convergent restricted product of local Haar measures.**
Given a finite exceptional set `S : Finset ι`, open subgroups `B i` that are compact outside `S`,
and local Haar measures `μ i` whose integral masses satisfy
`Summable fun i : {i // i ∉ S} ↦ |(μ i.1 (B i.1)).toReal - 1|`, there exists a unique left Haar
measure `ν` on `Πʳ i, [G i, B i]` such that for every finite set `T ⊇ S` and every family of
measurable sets `C i` agreeing with `B i` outside `T`,
`ν (box C) = (∏ i ∈ T, μ i (C i)) * ENNReal.ofReal (∏' i : {i // i ∉ T}, (μ i.1 (B i.1)).toReal)`.
-/
@[to_additive
/-- **Convergent restricted product of local additive Haar measures.**
Given a finite exceptional set `S : Finset ι`, open additive subgroups `B i` that are compact
outside `S`, and local additive Haar measures `μ i` whose integral masses satisfy
`Summable fun i : {i // i ∉ S} ↦ |(μ i.1 (B i.1)).toReal - 1|`, there exists a unique
left-invariant additive Haar measure `ν` on `Πʳ i, [G i, B i]` such that for every finite set
`T ⊇ S` and every family of measurable sets `C i` agreeing with `B i` outside `T`,
`ν (box C) = (∏ i ∈ T, μ i (C i)) * ENNReal.ofReal (∏' i : {i // i ∉ T}, (μ i.1 (B i.1)).toReal)`.
-/]
theorem exists_unique_convergentHaarProduct :
    ∃! ν : Measure (Πʳ i, [G i, B i]),
      ν.IsHaarMeasure ∧
      ∀ (T : Finset ι), S ⊆ T → ∀ C : ∀ i, Set (G i),
        (∀ i, MeasurableSet (C i)) → (∀ i ∉ T, C i = B i) →
        ν (box C) = (∏ i ∈ T, μ i (C i)) *
          ENNReal.ofReal (∏' i : {i // i ∉ T}, (μ i.val (B i.val)).toReal) := by
  classical
  obtain ⟨μ', _, -, hμ'_mem, hμ'_notMem, -, hBcompact', hμ'B⟩ :=
    exists_normalized_localHaar B S hBcompact μ
  have _ : LocallyCompactSpace (Πʳ i, [G i, B i]) := locallyCompactSpace_of_group G hBcompact'
  have hcS_pos : 0 < ∏' i : {i // i ∉ S}, (μ i.val (B i.val)).toReal :=
    tprod_pos_of_summable_abs_sub_one
      (fun i ↦ ENNReal.toReal_pos
        ((hBopen.out i.val).measure_pos (μ i.val) ⟨1, one_mem (B i.val)⟩).ne'
        (hBcompact i.val i.property).measure_lt_top.ne) hconv
  let ν : Measure (Πʳ i, [G i, B i]) :=
    Real.toNNReal (∏' i : {i // i ∉ S}, (μ i.val (B i.val)).toReal) •
      restrictedHaar B μ' hμ'B
  have _ : ν.IsHaarMeasure := IsHaarMeasure.nnreal_smul _ (Real.toNNReal_pos.mpr hcS_pos).ne'
  have hν_box (T : Finset ι) (hST : S ⊆ T) (C : ∀ i, Set (G i))
      (_ : ∀ i, MeasurableSet (C i)) (hCB : ∀ i ∉ T, C i = B i) :
      ν (box C) = (∏ i ∈ T, μ i (C i)) *
        ENNReal.ofReal (∏' i : {i // i ∉ T}, (μ i.val (B i.val)).toReal) :=
    smul_restrictedHaar_box B S hBcompact μ hconv μ' hμ'_mem hμ'_notMem hμ'B hST hCB
  refine ⟨ν, ⟨inferInstance, hν_box⟩, fun ν' ⟨_, hν'_box⟩ ↦ ?_⟩
  obtain ⟨C, -, hCmeas, hCB, -, hpos, hlt⟩ := exists_compact_measurable_one_mem_interior B S μ
  have hνC := hν_box S Finset.Subset.rfl C hCmeas hCB
  exact isMulLeftInvariant_eq_of_apply_eq ν' ν
    (hνC ▸ mul_ne_zero hpos.ne' (ENNReal.ofReal_pos.mpr hcS_pos).ne')
    (hνC ▸ (ENNReal.mul_lt_top hlt ENNReal.ofReal_lt_top).ne)
    ((hν'_box S Finset.Subset.rfl C hCmeas hCB).trans hνC.symm)

/-- The canonical convergent restricted Haar product measure on `Πʳ i, [G i, B i]` attached to local
Haar measures `μ i` whose integral masses converge absolutely outside `S`. -/
@[to_additive /-- The canonical convergent restricted additive Haar product measure on
`Πʳ i, [G i, B i]` attached to local additive Haar measures `μ i` whose integral masses converge
absolutely outside `S`. -/]
def convergentHaarProduct : Measure (Πʳ i, [G i, B i]) :=
  (exists_unique_convergentHaarProduct B S hBcompact μ hconv).choose

/-- `convergentHaarProduct` is a left Haar measure on `Πʳ i, [G i, B i]`. -/
@[to_additive /-- `convergentAddHaarProduct` is a left-invariant additive Haar measure on
`Πʳ i, [G i, B i]`. -/]
instance isHaarMeasure_convergentHaarProduct :
    (convergentHaarProduct B S hBcompact μ hconv).IsHaarMeasure :=
  (exists_unique_convergentHaarProduct B S hBcompact μ hconv).choose_spec.1.1

/-- Uniqueness of `convergentHaarProduct`: any left Haar measure satisfying the box formula above
`S` coincides with `convergentHaarProduct`. -/
@[to_additive /-- Uniqueness of `convergentAddHaarProduct`: any left-invariant additive Haar measure
satisfying the box formula above `S` coincides with `convergentAddHaarProduct`. -/]
theorem convergentHaarProduct_unique {ν : Measure (Πʳ i, [G i, B i])} [ν.IsHaarMeasure]
    (hν : ∀ (T : Finset ι), S ⊆ T → ∀ C : ∀ i, Set (G i),
      (∀ i, MeasurableSet (C i)) → (∀ i ∉ T, C i = B i) →
      ν (box C) = (∏ i ∈ T, μ i (C i)) *
        ENNReal.ofReal (∏' i : {i // i ∉ T}, (μ i.val (B i.val)).toReal)) :
    ν = convergentHaarProduct B S hBcompact μ hconv :=
  (exists_unique_convergentHaarProduct B S hBcompact μ hconv).choose_spec.2 ν ⟨inferInstance, hν⟩

/-- `convergentHaarProduct` equals `restrictedHaar` for local Haar measures `μ'` normalized by
`((μ i (B i)).toNNReal)⁻¹ • μ i` outside `S`, scaled by the convergent Euler product
`∏' i : {i // i ∉ S}, (μ i.1 (B i.1)).toReal`. -/
@[to_additive convergentAddHaarProduct_eq_smul_restrictedAddHaar
/-- `convergentAddHaarProduct` equals `restrictedAddHaar` for local additive Haar measures `μ'`
normalized by `((μ i (B i)).toNNReal)⁻¹ • μ i` outside `S`, scaled by the convergent product
`∏' i : {i // i ∉ S}, (μ i.1 (B i.1)).toReal`. -/]
theorem convergentHaarProduct_eq_smul_restrictedHaar
    (μ' : ∀ i, Measure (G i)) [∀ i, (μ' i).IsHaarMeasure]
    (hμ'_mem : ∀ i ∈ S, μ' i = μ i) (hμ'_notMem : ∀ i ∉ S, μ' i = ((μ i (B i)).toNNReal)⁻¹ • μ i)
    (hμ'B : ∀ᶠ i in cofinite, μ' i (B i) = 1) :
    convergentHaarProduct B S hBcompact μ hconv =
      Real.toNNReal (∏' i : {i // i ∉ S}, (μ i.val (B i.val)).toReal) •
        restrictedHaar B μ' hμ'B := by
  have hcS_pos : 0 < ∏' i : {i // i ∉ S}, (μ i.val (B i.val)).toReal :=
    tprod_pos_of_summable_abs_sub_one
      (fun i ↦ ENNReal.toReal_pos
        ((hBopen.out i.val).measure_pos (μ i.val) ⟨1, one_mem (B i.val)⟩).ne'
        (hBcompact i.val i.property).measure_lt_top.ne) hconv
  have _ : (Real.toNNReal (∏' i : {i // i ∉ S}, (μ i.val (B i.val)).toReal) •
      restrictedHaar B μ' hμ'B).IsHaarMeasure :=
    IsHaarMeasure.nnreal_smul _ (Real.toNNReal_pos.mpr hcS_pos).ne'
  exact (convergentHaarProduct_unique B S hBcompact μ hconv fun _ hST _ _ hCB ↦
    smul_restrictedHaar_box B S hBcompact μ hconv μ' hμ'_mem hμ'_notMem hμ'B hST
      hCB).symm

/-- Value of `convergentHaarProduct` on any coordinate box `box C` agreeing with `B i` outside a
finite set `T ⊇ S`. No measurability assumption on `C i` is needed. -/
@[to_additive /-- Value of `convergentAddHaarProduct` on any coordinate box `box C` agreeing with
`B i` outside a finite set `T ⊇ S`. No measurability assumption on `C i` is needed. -/]
theorem convergentHaarProduct_box {T : Finset ι} (hST : S ⊆ T) {C : ∀ i, Set (G i)}
    (hCB : ∀ i ∉ T, C i = B i) :
    convergentHaarProduct B S hBcompact μ hconv (box C) =
      (∏ i ∈ T, μ i (C i)) * ENNReal.ofReal (∏' i : {i // i ∉ T}, (μ i.val (B i.val)).toReal) := by
  obtain ⟨μ', _, -, hμ'_mem, hμ'_notMem, -, -, hμ'B⟩ :=
    exists_normalized_localHaar B S hBcompact μ
  rw [convergentHaarProduct_eq_smul_restrictedHaar B S hBcompact μ hconv μ' hμ'_mem
    hμ'_notMem hμ'B]
  exact smul_restrictedHaar_box B S hBcompact μ hconv μ' hμ'_mem hμ'_notMem hμ'B hST hCB

/-- If every local Haar measure `μ i` is right-invariant, then `convergentHaarProduct` is also
right-invariant. -/
@[to_additive /-- If every local additive Haar measure `μ i` is right-translation-invariant, then
`convergentAddHaarProduct` is also right-translation-invariant. -/]
instance isMulRightInvariant_convergentHaarProduct [∀ i, (μ i).IsMulRightInvariant] :
    (convergentHaarProduct B S hBcompact μ hconv).IsMulRightInvariant := by
  obtain ⟨μ', _, hμ'_right, hμ'_mem, hμ'_notMem, -, -, hμ'B⟩ :=
    exists_normalized_localHaar B S hBcompact μ
  have _ (i : ι) : (μ' i).IsMulRightInvariant := hμ'_right i
  rw [convergentHaarProduct_eq_smul_restrictedHaar B S hBcompact μ hconv μ' hμ'_mem
    hμ'_notMem hμ'B]
  infer_instance

end
end

/-- Enlarging the finite exceptional set `S` to `S' ⊇ S` leaves `convergentHaarProduct`
unchanged. -/
@[to_additive /-- Enlarging the finite exceptional set `S` to `S' ⊇ S` leaves
`convergentAddHaarProduct` unchanged. -/]
theorem convergentHaarProduct_eq_of_subset (B : ∀ i, K i) [Fact (∀ i, IsOpen (B i : Set (G i)))]
    {S S' : Finset ι} (hSS' : S ⊆ S')
    (hBcompact : ∀ i ∉ S, IsCompact (B i : Set (G i)))
    (hBcompact' : ∀ i ∉ S', IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hconv : Summable fun i : {i // i ∉ S} ↦ |(μ i.val (B i.val)).toReal - 1|)
    (hconv' : Summable fun i : {i // i ∉ S'} ↦ |(μ i.val (B i.val)).toReal - 1|) :
    convergentHaarProduct B S hBcompact μ hconv =
      convergentHaarProduct B S' hBcompact' μ hconv' :=
  convergentHaarProduct_unique B S' hBcompact' μ hconv' fun _ hS'T _ _ hCB ↦
    convergentHaarProduct_box B S hBcompact μ hconv (hSS'.trans hS'T) hCB

/-- **Independence of the finite exceptional set.** The convergent restricted Haar product depends
only on `(B, μ)` and not on the choice of finite set `S` outside which compactness and convergence
are witnessed. -/
@[to_additive /-- **Independence of the finite exceptional set.** The convergent restricted additive
Haar product depends only on `(B, μ)` and not on the choice of finite set `S` outside which
compactness and convergence are witnessed. -/]
theorem convergentHaarProduct_congr_finset (B : ∀ i, K i) [Fact (∀ i, IsOpen (B i : Set (G i)))]
    (S S' : Finset ι)
    (hBcompact : ∀ i ∉ S, IsCompact (B i : Set (G i)))
    (hBcompact' : ∀ i ∉ S', IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hconv : Summable fun i : {i // i ∉ S} ↦ |(μ i.val (B i.val)).toReal - 1|)
    (hconv' : Summable fun i : {i // i ∉ S'} ↦ |(μ i.val (B i.val)).toReal - 1|) :
    convergentHaarProduct B S hBcompact μ hconv =
      convergentHaarProduct B S' hBcompact' μ hconv' := by
  classical
  have hBcompactU (i : ι) (hi : i ∉ S ∪ S') : IsCompact (B i : Set (G i)) :=
    hBcompact i fun h ↦ hi (Finset.subset_union_left h)
  have hconvU := summable_notMem_of_subset (T := S ∪ S') Finset.subset_union_left
    (fun i ↦ |(μ i (B i)).toReal - 1|) hconv
  exact (convergentHaarProduct_eq_of_subset B Finset.subset_union_left hBcompact hBcompactU μ
    hconv hconvU).trans
    (convergentHaarProduct_eq_of_subset B Finset.subset_union_right hBcompact' hBcompactU μ
      hconv' hconvU).symm

/-- When `μ i (B i) = 1` cofinitely, `convergentHaarProduct` agrees with `restrictedHaar`. -/
@[to_additive /-- When `μ i (B i) = 1` cofinitely, `convergentAddHaarProduct` agrees with
`restrictedAddHaar`. -/]
theorem convergentHaarProduct_eq_restrictedHaar (B : ∀ i, K i)
    [Fact (∀ i, IsOpen (B i : Set (G i)))]
    (S : Finset ι) (hBcompact : ∀ i ∉ S, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμB : ∀ᶠ i in cofinite, μ i (B i) = 1)
    (hconv : Summable fun i : {i // i ∉ S} ↦ |(μ i.val (B i.val)).toReal - 1|) :
    convergentHaarProduct B S hBcompact μ hconv = restrictedHaar B μ hμB := by
  classical
  let S₁ : Finset ι := S ∪ (mem_cofinite.mp hμB).toFinset
  have hSS₁ : S ⊆ S₁ := Finset.subset_union_left
  have hBcompact₁ (i : ι) (hi : i ∉ S₁) : IsCompact (B i : Set (G i)) :=
    hBcompact i fun h ↦ hi (hSS₁ h)
  have hconv₁ := summable_notMem_of_subset hSS₁ (fun i ↦ |(μ i (B i)).toReal - 1|) hconv
  have hμB₁ (i : ι) (hi : i ∉ S₁) : μ i (B i) = 1 := Classical.byContradiction fun hnot ↦
    hi (Finset.subset_union_right ((Set.Finite.mem_toFinset _).mpr hnot))
  rw [convergentHaarProduct_eq_of_subset B hSS₁ hBcompact hBcompact₁ μ hconv hconv₁]
  refine (convergentHaarProduct_unique B S₁ hBcompact₁ μ hconv₁ fun T hS₁T C _ hCB ↦ ?_).symm
  rw [restrictedHaar_box B μ hμB (fun i hiT ↦ hμB₁ i fun h ↦ hiT (hS₁T h)) hCB]
  have htail : (∏' i : {i // i ∉ T}, (μ i.val (B i.val)).toReal) = 1 := by
    simp [fun i : {i // i ∉ T} ↦ hμB₁ i.val fun h ↦ i.property (hS₁T h)]
  simp [htail]

/-- Pulling `convergentHaarProduct` back along `levelMonoidHom B T` for any finite set `T ⊇ S`
yields the product of the finite product Haar measure on `Π i : T, G i` with Kolmogorov's infinite
product of normalized probability Haar measures `(μ i.1 (B i.1))⁻¹ • (μ i.1).comap Subtype.val` on
`Π i : {i // i ∉ T}, B i`, scaled by the convergent tail product outside `T`. -/
@[to_additive /-- Pulling `convergentAddHaarProduct` back along `levelAddMonoidHom B T` for any
finite set `T ⊇ S` yields the product of the finite product additive Haar measure on `Π i : T, G i`
with Kolmogorov's infinite product of normalized probability additive Haar measures
`(μ i.1 (B i.1))⁻¹ • (μ i.1).comap Subtype.val` on `Π i : {i // i ∉ T}, B i`, scaled by the
convergent tail product outside `T`. -/]
theorem comap_levelMonoidHom_convergentHaarProduct (B : ∀ i, K i)
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    (S : Finset ι) (hBcompact : ∀ i ∉ S, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hconv : Summable fun i : {i // i ∉ S} ↦ |(μ i.val (B i.val)).toReal - 1|)
    {T : Finset ι} (hST : S ⊆ T) :
    (convergentHaarProduct B S hBcompact μ hconv).comap (levelMonoidHom B T) =
      ENNReal.ofReal (∏' i : {i // i ∉ T}, (μ i.val (B i.val)).toReal) •
        (Measure.pi fun i : T ↦ μ i.val).prod
          (Measure.infinitePi fun i : {i // i ∉ T} ↦
            (μ i.val (B i.val))⁻¹ • (μ i.val).comap Subtype.val) := by
  have hBcompactT (i : ι) (hi : i ∉ T) : IsCompact (B i : Set (G i)) :=
    hBcompact i fun h ↦ hi (hST h)
  have hconvT := summable_notMem_of_subset hST (fun i ↦ |(μ i (B i)).toReal - 1|) hconv
  obtain ⟨μ', _, -, hμ'_mem, hμ'_notMem, hμ'B_out, -, hμ'B⟩ :=
    exists_normalized_localHaar B T hBcompactT μ
  rw [convergentHaarProduct_eq_of_subset B hST hBcompact hBcompactT μ hconv hconvT,
    convergentHaarProduct_eq_smul_restrictedHaar B T hBcompactT μ hconvT μ' hμ'_mem
      hμ'_notMem hμ'B,
    ← Measure.coe_nnreal_smul, ENNReal.ofNNReal_toNNReal, Measure.comap_smul,
    comap_levelMonoidHom_restrictedHaar B μ' hμ'B hμ'B_out, restrictedPrincipalPieceMeasure_def]
  congr 2
  · exact congrArg Measure.pi (funext fun i ↦ hμ'_mem i.val i.property)
  · refine congrArg Measure.infinitePi (funext fun i ↦ ?_)
    have hpos := (hBopen.out i.val).measure_pos (μ i.val) ⟨1, one_mem (B i.val)⟩
    have hlt : μ i.val (B i.val) < ⊤ := (hBcompactT i.val i.property).measure_lt_top
    rw [hμ'_notMem i.val i.property, ← Measure.coe_nnreal_smul,
      ENNReal.coe_inv (ENNReal.toNNReal_pos hpos.ne' hlt.ne).ne',
      ENNReal.coe_toNNReal hlt.ne, Measure.comap_smul]

/-- **Independence of the integral model.** If two families of open subgroups `U` and `U'` agree
cofinitely, then `restrictedProductCongr U U' h` pushes `convergentHaarProduct` for `U` directly to
`convergentHaarProduct` for `U'` with no scalar factor. -/
@[to_additive map_addRestrictedProductCongr_convergentAddHaarProduct
/-- **Independence of the integral model.** If two families of open additive subgroups `U` and `U'`
agree cofinitely, then `addRestrictedProductCongr U U' h` pushes `convergentAddHaarProduct` for `U`
directly to `convergentAddHaarProduct` for `U'` with no scalar factor. -/]
theorem map_restrictedProductCongr_convergentHaarProduct (U U' : ∀ i, Subgroup (G i))
    [Fact (∀ i, IsOpen (U i : Set (G i)))] [Fact (∀ i, IsOpen (U' i : Set (G i)))]
    (S S' : Finset ι) (h : ∀ᶠ i in cofinite, U i = U' i)
    (hUcompact : ∀ i ∉ S, IsCompact (U i : Set (G i)))
    (hU'compact : ∀ i ∉ S', IsCompact (U' i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hconv : Summable fun i : {i // i ∉ S} ↦ |(μ i.val (U i.val)).toReal - 1|)
    (hconv' : Summable fun i : {i // i ∉ S'} ↦ |(μ i.val (U' i.val)).toReal - 1|) :
    (convergentHaarProduct U S hUcompact μ hconv).map (restrictedProductCongr U U' h) =
      convergentHaarProduct U' S' hU'compact μ hconv' := by
  classical
  let S₀ : Finset ι := (S ∪ S') ∪ (mem_cofinite.mp h).toFinset
  have hSS₀ : S ⊆ S₀ := Finset.subset_union_left.trans Finset.subset_union_left
  have hS'S₀ : S' ⊆ S₀ := Finset.subset_union_right.trans Finset.subset_union_left
  have hUU' (i : ι) (hi : i ∉ S₀) : U i = U' i := Classical.byContradiction fun hnot ↦
    hi (Finset.subset_union_right ((Set.Finite.mem_toFinset _).mpr hnot))
  have hUcompact₀ (i : ι) (hi : i ∉ S₀) : IsCompact (U i : Set (G i)) :=
    hUcompact i fun h ↦ hi (hSS₀ h)
  have hU'compact₀ (i : ι) (hi : i ∉ S₀) : IsCompact (U' i : Set (G i)) :=
    hU'compact i fun h ↦ hi (hS'S₀ h)
  have hconv₀ := summable_notMem_of_subset hSS₀ (fun i ↦ |(μ i (U i)).toReal - 1|) hconv
  have hconv'₀ := summable_notMem_of_subset hS'S₀ (fun i ↦ |(μ i (U' i)).toReal - 1|) hconv'
  obtain ⟨μ', _, -, hμ'_mem, hμ'_notMem, hμ'U_out, -, hμ'U⟩ :=
    exists_normalized_localHaar U S₀ hUcompact₀ μ
  have hμ'U' : ∀ᶠ i in cofinite, μ' i (U' i) = 1 :=
    Filter.Eventually.mono S₀.finite_toSet.compl_mem_cofinite fun i hi ↦
      hUU' i (Finset.mem_coe.not.mp hi) ▸ hμ'U_out i (Finset.mem_coe.not.mp hi)
  rw [convergentHaarProduct_eq_of_subset U hSS₀ hUcompact hUcompact₀ μ hconv hconv₀,
    convergentHaarProduct_eq_of_subset U' hS'S₀ hU'compact hU'compact₀ μ hconv' hconv'₀,
    convergentHaarProduct_eq_smul_restrictedHaar U S₀ hUcompact₀ μ hconv₀ μ' hμ'_mem
      hμ'_notMem hμ'U,
    convergentHaarProduct_eq_smul_restrictedHaar U' S₀ hU'compact₀ μ hconv'₀ μ'
      hμ'_mem (fun i hi ↦ hUU' i hi ▸ hμ'_notMem i hi) hμ'U',
    Measure.map_smul _ (continuous_restrictedProductCongr U U' h).measurable.aemeasurable,
    map_restrictedProductCongr_restrictedHaar U U' h μ' hμ'U hμ'U']
  exact congrArg (· • _) (congrArg Real.toNNReal
      (tprod_congr fun i ↦ by rw [hUU' i.val i.property]))

end ConvergentHaarProduct

end TauCeti

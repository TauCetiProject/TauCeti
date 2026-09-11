/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Valuation.CofinalIdeal.Greatest
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
public import TauCeti.RingTheory.Huber.Continuous.Coarsen
import TauCeti.RingTheory.Huber.Continuous.PowerBounded
public import TauCeti.RingTheory.Huber.LocalizationTopology.Completion
public import TauCeti.RingTheory.Huber.OpenIdeal
public import TauCeti.RingTheory.Valuation.Microbial

/-!
# Analytic points and the analytic locus of `Spa(A, A⁺)`

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Definition 7.39, Remark 7.40(2), (3), (5),
Remark 7.42(2), and Proposition 7.49.**

This file formalizes the analytic locus of the adic spectrum `Spa(A, A⁺)`.

## Main definitions

* `TauCeti.ValuationSpectrum.IsAnalyticPoint` : extends Wedhorn's analytic-point predicate from
  `Cont A` to `Spv A`; on continuous points it is Definition 7.39.
* `TauCeti.ValuationSpectrum.spaAnalytic` : **Wedhorn's `Spa(A, A⁺)ᵃ`**, the analytic locus of
  `Spa(A, A⁺)` as a `Set (Spv A)`.
* `TauCeti.ValuationSpectrum.spaAnalytic_def` : the analytic locus as a set intersection.

## Main results

* `TauCeti.ValuationSpectrum.isAnalyticPoint_of_isTateRing` : over a Tate ring every point of
  `Spv A` (and hence `Spa(A, A⁺)`) is analytic.
* `TauCeti.ValuationSpectrum.spaAnalytic_eq_spa_of_isTateRing` : **Wedhorn Remark 7.40(3)**,
  for a Tate ring `A`, the analytic locus is the entire adic spectrum.
* `TauCeti.ValuationSpectrum.isOpen_val_preimage_spaAnalytic` : the analytic locus is open.
* `TauCeti.ValuationSpectrum.isCompact_val_preimage_spaAnalytic` : **Wedhorn Remark 7.40(2)**,
  the analytic locus is quasi-compact; with the previous result, open and quasi-compact.
* `TauCeti.ValuationSpectrum.IsAnalyticPoint.isMicrobial` : **Wedhorn Remark 7.40(5)**, every
  continuous analytic point of a Huber ring is microbial.
* `TauCeti.ValuationSpectrum.IsAnalyticPoint.exists_coarsenByUnits_mem_spaAnalytic` :
  **Wedhorn Remark 7.42(2)**, an analytic point has a height-one vertical generization in every
  adic spectrum containing it.
* `TauCeti.ValuationSpectrum.spaAnalytic_eq_biUnion_rationalSubset` : generators of an ideal of
  definition give a finite rational cover of the analytic locus.
* `TauCeti.ValuationSpectrum.isTateRing_completion_locTopology_of_mem_generators` : the completed
  coordinate ring of each chart in that cover is Tate.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 7.39, Remark 7.40(2), (3), (5),
  Remark 7.42(2), and Proposition 7.49.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti TauCeti.Huber TauCeti.Huber.PairOfDefinition Valuation

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- **Analytic points of `Spv A`.** A point `v : Spv A` is *analytic* if its support `v.supp` is
not an open ideal of `A`. This extends Wedhorn's Definition 7.39 from `Cont A` to all of `Spv A`;
its restriction to continuous points is his predicate. -/
def IsAnalyticPoint (v : Spv A) : Prop :=
  ¬ IsOpen (v.supp : Set A)

/-- A point of `Spv A` is analytic exactly when its support is not open. -/
@[simp]
theorem isAnalyticPoint_def (v : Spv A) :
    IsAnalyticPoint v ↔ ¬ IsOpen (v.supp : Set A) :=
  Iff.rfl

/-- **Wedhorn's Analytic Locus `Spa(A, A⁺)ᵃ`**: the subset of `spa Aplus` consisting of analytic
points (Definition 7.39). -/
def spaAnalytic (Aplus : Subring A) : Set (Spv A) :=
  spa Aplus ∩ {v : Spv A | IsAnalyticPoint v}

/-- The analytic locus as a set intersection. -/
theorem spaAnalytic_def (Aplus : Subring A) :
    spaAnalytic Aplus = spa Aplus ∩ {v : Spv A | IsAnalyticPoint v} := (rfl)

/-- Membership in the analytic locus: `v ∈ Spa(A, A⁺)ᵃ` iff `v ∈ Spa(A, A⁺)` and `v` is an
analytic point. -/
@[simp]
theorem mem_spaAnalytic_iff (Aplus : Subring A) (v : Spv A) :
    v ∈ spaAnalytic Aplus ↔ v ∈ spa Aplus ∧ IsAnalyticPoint v :=
  Iff.rfl

/-- The analytic locus is contained in the adic spectrum. -/
theorem spaAnalytic_subset_spa (Aplus : Subring A) :
    spaAnalytic Aplus ⊆ spa Aplus :=
  Set.inter_subset_left

/-- Enlarging the plus ring shrinks the analytic locus. -/
theorem spaAnalytic_antitone : Antitone (spaAnalytic (A := A)) := fun _ _ hle ↦
  Set.inter_subset_inter_left _ (spa_antitone hle)

section TopologicalRing

variable [IsTopologicalRing A]

/-- A point is analytic exactly when some element of the extended ideal of definition is outside
its support. This is Wedhorn Proposition 7.49(2)(i), expressed using Lemma 6.6. -/
theorem isAnalyticPoint_iff_exists_mem_extendedIdealOfDefinition_notMem_supp
    (P : PairOfDefinition A) (v : Spv A) :
    IsAnalyticPoint v ↔ ∃ a ∈ P.extendedIdealOfDefinition, a ∉ v.supp := by
  rw [isAnalyticPoint_def, P.isOpen_iff_le_radical]
  have hsupp : v.supp.radical = v.supp :=
    (inferInstance : v.supp.IsPrime).isRadical.radical
  rw [hsupp]
  exact Set.not_subset

/-- An analytic point supplies an element of an ideal of definition which is outside its
support. Unlike an arbitrary element of the extended ideal, this witness is topologically
nilpotent because it comes from the ring of definition itself. -/
theorem IsAnalyticPoint.exists_mem_idealOfDefinition_notMem_supp
    (P : PairOfDefinition A) {v : Spv A} (hv : IsAnalyticPoint v) :
    ∃ b : P.ringOfDefinition, b ∈ P.idealOfDefinition ∧ (b : A) ∉ v.supp := by
  obtain ⟨a, haI, ha⟩ :=
    (isAnalyticPoint_iff_exists_mem_extendedIdealOfDefinition_notMem_supp P v).mp hv
  by_contra! h
  apply ha
  have hsupp : P.extendedIdealOfDefinition ≤ v.supp := by
    rw [P.extendedIdealOfDefinition_def, Ideal.map_le_iff_le_comap]
    exact fun b hb ↦ h b hb
  exact hsupp haI

/-- **Wedhorn Remark 7.40(5).** Every continuous analytic point of a Huber ring is microbial. -/
theorem IsAnalyticPoint.isMicrobial [IsHuberRing A] {v : Spv A} (hana : IsAnalyticPoint v)
    (hcont : v.IsContinuous) : v.valuation.IsMicrobial := by
  obtain ⟨P⟩ := IsHuberRing.nonempty_pairOfDefinition (A := A)
  obtain ⟨b, hbI, hbSupp⟩ := hana.exists_mem_idealOfDefinition_notMem_supp P
  have hb0 : (MonoidWithZeroHom.ofClass v.valuation) (b : A) ≠ 0 := by
    intro hb0
    exact hbSupp (v.supp_eq_valuation_supp ▸ (v.valuation.mem_supp_iff _).mpr hb0)
  have hb0' : v.valuation.restrict (b : A) ≠ 0 :=
    fun h ↦ hb0 (v.valuation.restrict_eq_zero_iff.mp h)
  have hblt : v.valuation.restrict (b : A) < 1 := by
    rw [← MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.lt_iff_lt,
      Valuation.embedding_restrict, map_one]
    exact ((isContinuous_def v).mp hcont).lt_one_of_isTopologicallyNilpotent
      (P.isTopologicallyNilpotent_of_mem_idealOfDefinition hbI)
  have hcof := ((isContinuous_def v).mp hcont).cofinalValue_of_isTopologicallyNilpotent
    (P.isTopologicallyNilpotent_of_mem_idealOfDefinition hbI)
  let u : (MonoidWithZeroHom.ValueGroup₀ (.ofClass v.valuation))ˣ :=
    Units.mk0 (v.valuation.restrict (b : A)) hb0'
  have hu : u ≠ 1 := by
    intro hu
    have : v.valuation.restrict (b : A) = 1 := by
      simpa [u] using congrArg Units.val hu
    exact ne_of_lt hblt this
  have hult : u < 1 := by
    rw [← Units.val_lt_val]
    simpa [u] using hblt
  have hcofFor : Valuation.CofinalValueFor v.valuation ⊤ (b : A) :=
    Valuation.cofinalValueFor_top_iff.mpr hcof
  have huImage : OrderMonoidIso.unitsWithZero u =
      MonoidWithZeroHom.valueGroup.mk (.ofClass v.valuation) 1 (b : A) (by simp) hb0 := by
    apply WithZero.coe_injective
    calc
      ((OrderMonoidIso.unitsWithZero u :
          MonoidWithZeroHom.valueGroup (.ofClass v.valuation)) :
          MonoidWithZeroHom.ValueGroup₀ (.ofClass v.valuation)) =
          ((u : (MonoidWithZeroHom.ValueGroup₀ (.ofClass v.valuation))ˣ) :
            MonoidWithZeroHom.ValueGroup₀ (.ofClass v.valuation)) :=
        WithZero.coe_unitsWithZeroEquiv_eq_units_val _
      _ = v.valuation.restrict (b : A) := by simp only [u, Units.val_mk0]
      _ = _ := v.valuation.restrict_eq_mk hb0
  have huCofImage : TauCeti.IsCofinalElement ⊤ (OrderMonoidIso.unitsWithZero u) := by
    rw [huImage]
    exact (Valuation.cofinalValueFor_iff_isCofinalElement hb0).mp hcofFor
  have huCof : TauCeti.IsCofinalElement ⊤ u := by
    rw [TauCeti.isCofinalElement_def]
    intro x _
    obtain ⟨n, hn⟩ := TauCeti.isCofinalElement_def.mp huCofImage
      (OrderMonoidIso.unitsWithZero x) (by simp)
    have hmap : OrderMonoidIso.unitsWithZero (u ^ n) <
        OrderMonoidIso.unitsWithZero x := by
      simpa only [map_pow] using hn
    exact ⟨n, (OrderIso.lt_iff_lt OrderMonoidIso.unitsWithZero.toOrderIso).mp hmap⟩
  have hclosure : TauCeti.ConvexSubgroup.closure ({u} : Set _) = ⊤ := by
    apply top_unique
    exact (TauCeti.isCofinalElement_iff_subset_closure hult).mp huCof
  exact Valuation.isMicrobial_iff.mpr
    ⟨TauCeti.ConvexSubgroup.maxAvoid hu,
      TauCeti.ConvexSubgroup.nontrivial_quotient_maxAvoid hu,
      TauCeti.ConvexSubgroup.mulArchimedean_quotient_maxAvoid hu hclosure⟩

/-- **Wedhorn Remark 7.42(2).** A continuous analytic point has a height-one vertical
generization in `Spa(A, A⁺)` whenever `A⁺` consists of power-bounded elements; in particular,
this applies to every ring of integral elements. -/
theorem IsAnalyticPoint.exists_coarsenByUnits_mem_spaAnalytic [IsHuberRing A]
    (Aplus : Subring A) (hAplus : Aplus ≤ powerBoundedSubring A) {v : Spv A}
    (hana : IsAnalyticPoint v) (hcont : v.IsContinuous) :
    ∃ H : TauCeti.ConvexSubgroup
        (MonoidWithZeroHom.ValueGroup₀ (.ofClass v.valuation))ˣ,
      Nontrivial
          ((MonoidWithZeroHom.ValueGroup₀ (.ofClass v.valuation))ˣ ⧸ H.toSubgroup) ∧
        MulArchimedean
          ((MonoidWithZeroHom.ValueGroup₀ (.ofClass v.valuation))ˣ ⧸ H.toSubgroup) ∧
        ofValuation (v.valuation.restrict.coarsenByUnits H) ∈ spaAnalytic Aplus ∧
        (ofValuation (v.valuation.restrict.coarsenByUnits H)).supp = v.supp := by
  obtain ⟨H, hHnontrivial, hHarch⟩ := Valuation.isMicrobial_iff.mp (hana.isMicrobial hcont)
  have hH : H ≠ ⊤ := by
    intro htop
    apply QuotientGroup.nontrivial_iff.mp hHnontrivial
    simpa only [TauCeti.ConvexSubgroup.top_toSubgroup] using
      TauCeti.ConvexSubgroup.toSubgroup_inj.mpr htop
  let w := v.valuation.restrict.coarsenByUnits H
  have hwcont : w.IsContinuous :=
    ((isContinuous_def v).mp hcont).coarsenByUnits_restrict hH
  have hsupp : (ofValuation w).supp = v.supp := by
    rw [supp_ofValuation]
    dsimp [w]
    rw [Valuation.coarsenByUnits_supp]
    ext a
    rw [v.supp_eq_valuation_supp]
    simp only [Valuation.mem_supp_iff, Valuation.restrict_eq_zero_iff]
  obtain ⟨P⟩ := IsHuberRing.nonempty_pairOfDefinition (A := A)
  obtain ⟨b, hbI, hbSupp⟩ := hana.exists_mem_idealOfDefinition_notMem_supp P
  have hwb0 : w (b : A) ≠ 0 := by
    intro hwb0
    apply hbSupp
    rw [← hsupp, supp_ofValuation, Valuation.mem_supp_iff]
    exact hwb0
  let _ : MulArchimedean
      ((MonoidWithZeroHom.ValueGroup₀ (.ofClass v.valuation))ˣ ⧸ H.toSubgroup) := hHarch
  let _ : MulArchimedean (MonoidWithZeroHom.ValueGroup₀ (.ofClass w)) :=
    MulArchimedean.comap MonoidWithZeroHom.ValueGroup₀.embedding.toMonoidHom
      MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
  refine ⟨H, hHnontrivial, hHarch, ?_, hsupp⟩
  rw [mem_spaAnalytic_iff]
  refine ⟨(mem_spa_iff Aplus (ofValuation w)).mpr ⟨?_, ?_⟩, ?_⟩
  · exact (isContinuous_ofValuation_iff w).mpr hwcont
  · intro a ha
    rw [vle_ofValuation, map_one]
    exact hwcont.le_one_of_isPowerBounded
      (P.isTopologicallyNilpotent_of_mem_idealOfDefinition hbI) hwb0
      (mem_powerBoundedSubring.mp (hAplus ha))
  · rw [isAnalyticPoint_def, hsupp]
    exact hana

/-- The analytic locus is open in the adic spectrum. It is the union, over the extended ideal of
definition, of the loci on which an element does not vanish. -/
theorem isOpen_val_preimage_spaAnalytic (P : PairOfDefinition A) (Aplus : Subring A) :
    IsOpen (Subtype.val ⁻¹' spaAnalytic Aplus : Set (spa Aplus)) := by
  have hset : (Subtype.val ⁻¹' spaAnalytic Aplus : Set (spa Aplus)) =
      ⋃ a ∈ P.extendedIdealOfDefinition,
        Subtype.val ⁻¹' basicOpen a a := by
    ext v
    simp only [Set.mem_preimage, mem_spaAnalytic_iff, v.property, true_and, Set.mem_iUnion,
      mem_basicOpen_iff, exists_prop, ValuativeRel.vle_refl]
    rw [isAnalyticPoint_iff_exists_mem_extendedIdealOfDefinition_notMem_supp P]
    simp only [mem_supp_iff]
  rw [hset]
  exact isOpen_biUnion fun a _ ↦ (isOpen_basicOpen a a).preimage continuous_subtype_val

/-- A rational subset whose denominator belongs to the extended ideal of definition consists of
analytic points. -/
theorem rationalSubset_subset_spaAnalytic_of_mem_extendedIdealOfDefinition
    (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) {s : A}
    (hs : s ∈ P.extendedIdealOfDefinition) :
    rationalSubset Aplus T s ⊆ spaAnalytic Aplus := by
  intro v hv
  have hmem := (mem_rationalSubset_iff Aplus T s v).mp hv
  refine (mem_spaAnalytic_iff Aplus v).mpr ⟨hmem.1, ?_⟩
  rw [isAnalyticPoint_iff_exists_mem_extendedIdealOfDefinition_notMem_supp P]
  exact ⟨s, hs, fun hsupp ↦ hmem.2.2 ((mem_supp_iff v s).mp hsupp)⟩

open scoped Classical in
/-- **A finite rational cover of the analytic locus.** If `T` generates the extended ideal of
definition, then the rational subsets `R(T/t)`, for `t ∈ T`, cover exactly the analytic locus.
This is the cover in Wedhorn Proposition 7.49(2). -/
theorem spaAnalytic_eq_biUnion_rationalSubset_of_span_eq_extendedIdealOfDefinition
    (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A)
    (hspan : Ideal.span (T : Set A) = P.extendedIdealOfDefinition) :
    spaAnalytic Aplus =
      ⋃ t ∈ T, rationalSubset Aplus T t := by
  apply Set.Subset.antisymm
  · intro v hv
    have hvSpa := spaAnalytic_subset_spa Aplus hv
    obtain ⟨a, haI, haSupp⟩ :=
      (isAnalyticPoint_iff_exists_mem_extendedIdealOfDefinition_notMem_supp P v).mp
        ((mem_spaAnalytic_iff Aplus v).mp hv).2
    have ha0 : (MonoidWithZeroHom.ofClass v.valuation) a ≠ 0 := by
      intro ha0
      apply haSupp
      rw [v.supp_eq_valuation_supp, v.valuation.mem_supp_iff]
      exact ha0
    obtain ⟨t, htT, ht0, hmax⟩ :=
      Valuation.exists_mem_max_restrict_ne_zero (v := v.valuation)
        (I := P.extendedIdealOfDefinition) hspan rfl haI ha0
    refine Set.mem_iUnion₂_of_mem htT
      ((mem_rationalSubset_iff Aplus T t v).mpr ⟨hvSpa, ?_, ?_⟩)
    · intro u huT
      exact (valuation_le_iff v u t).mp (v.valuation.restrict_le_iff.mp (hmax u huT))
    · intro hzero
      exact ht0 (by simpa using (valuation_le_iff v t 0).mpr hzero)
  · refine Set.iUnion₂_subset fun t ht ↦ ?_
    apply rationalSubset_subset_spaAnalytic_of_mem_extendedIdealOfDefinition P Aplus
    rw [← hspan]
    exact Ideal.subset_span (Finset.mem_coe.mpr ht)

open scoped Classical in
/-- **The finite standard rational cover of the analytic locus.** If `G` generates an ideal of
definition, then the rational subsets `R(G/g)`, for `g ∈ G`, cover exactly the analytic locus.
This is the cover in Wedhorn Proposition 7.49(2). -/
theorem spaAnalytic_eq_biUnion_rationalSubset (P : PairOfDefinition A) (Aplus : Subring A)
    (G : Finset P.ringOfDefinition)
    (hG : Ideal.span (G : Set P.ringOfDefinition) = P.idealOfDefinition) :
    spaAnalytic Aplus =
      ⋃ g ∈ G, rationalSubset Aplus
        (G.image ((↑) : P.ringOfDefinition → A)) (g : A) := by
  let T : Finset A := G.image ((↑) : P.ringOfDefinition → A)
  have hspan : Ideal.span (T : Set A) = P.extendedIdealOfDefinition :=
    P.span_image_eq_extendedIdealOfDefinition G hG
  rw [spaAnalytic_eq_biUnion_rationalSubset_of_span_eq_extendedIdealOfDefinition
    P Aplus T hspan]
  apply Set.Subset.antisymm
  · refine Set.iUnion₂_subset fun t ht ↦ ?_
    have ht' : t ∈ G.image ((↑) : P.ringOfDefinition → A) := by
      simpa only [T] using ht
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp ht'
    exact Set.subset_iUnion₂_of_subset g hg Set.Subset.rfl
  · refine Set.iUnion₂_subset fun g hg ↦ ?_
    have hg' : (g : A) ∈ T := by
      simpa only [T] using Finset.mem_image.mpr ⟨g, hg, rfl⟩
    exact Set.subset_iUnion₂_of_subset (g : A) hg' Set.Subset.rfl

open scoped Classical in
/-- Every set in the standard analytic cover is a member of the rational basis: its numerator
ideal is the extended ideal of definition, hence open. -/
theorem val_preimage_rationalSubset_mem_spaRationalFamily_of_span_eq_idealOfDefinition
    (P : PairOfDefinition A) (Aplus : Subring A) (G : Finset P.ringOfDefinition)
    (hG : Ideal.span (G : Set P.ringOfDefinition) = P.idealOfDefinition)
    (g : P.ringOfDefinition) :
    (Subtype.val ⁻¹' rationalSubset Aplus
      (G.image ((↑) : P.ringOfDefinition → A)) (g : A) : Set (spa Aplus)) ∈
        spaRationalFamily Aplus := by
  refine mem_spaRationalFamily_iff.mpr ⟨_, (g : A), ?_, rfl⟩
  rw [P.span_image_eq_extendedIdealOfDefinition G hG]
  exact (P.isOpen_iff_le_radical P.extendedIdealOfDefinition).mpr Ideal.le_radical

open scoped Classical in
/-- The completed coordinate ring of a chart in the standard analytic cover is a Tate ring.
The denominator belongs to the ideal of definition, hence is topologically nilpotent, and
localization makes it a unit. The localization's standing hypothesis is constructed from the
same generating set. -/
theorem isTateRing_completion_locTopology_of_mem_generators (P : PairOfDefinition A)
    (G : Finset P.ringOfDefinition)
    (hG : Ideal.span (G : Set P.ringOfDefinition) = P.idealOfDefinition)
    {g : P.ringOfDefinition} (hg : g ∈ G)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away (g : A) S] :
    let hden := hasDenominatorPower_of_idealOfDefinition_le_span P
      (G.image ((↑) : P.ringOfDefinition → A))
      (fun _ hx ↦ Finset.mem_image_of_mem _ (Finset.mem_coe.mp hx)) hG.ge g S
    letI := locUniformSpace P (G.image ((↑) : P.ringOfDefinition → A)) (g : A) S hden
    letI := isUniformAddGroup_locUniformSpace P
      (G.image ((↑) : P.ringOfDefinition → A)) (g : A) S hden
    letI := isTopologicalRing_locUniformSpace P
      (G.image ((↑) : P.ringOfDefinition → A)) (g : A) S hden
    IsTateRing (UniformSpace.Completion S) := by
  let hden := hasDenominatorPower_of_idealOfDefinition_le_span P
    (G.image ((↑) : P.ringOfDefinition → A))
    (fun _ hx ↦ Finset.mem_image_of_mem _ (Finset.mem_coe.mp hx)) hG.ge g S
  exact isTateRing_completion_locTopology_of_isTopologicallyNilpotent P _ (g : A) S hden
    (P.isTopologicallyNilpotent_of_mem_idealOfDefinition
      (hG ▸ Ideal.subset_span (Finset.mem_coe.mpr hg)))

/-- **Wedhorn Remark 7.40(2).** The analytic locus is quasi-compact. A finite generating set of
the extended ideal of definition gives a finite rational cover of it, and each rational subset in
that cover is quasi-compact, so their union is. Together with `isOpen_val_preimage_spaAnalytic`
this is the whole of 7.40(2): the analytic locus is an open quasi-compact subset of `Spa(A, A⁺)`.

Stated for the preimage in `spa Aplus` rather than for `spaAnalytic Aplus : Set (Spv A)`, matching
`isOpen_val_preimage_spaAnalytic`, because quasi-compactness of a rational subset is available in
that form. -/
theorem isCompact_val_preimage_spaAnalytic (P : PairOfDefinition A) (Aplus : Subring A) :
    IsCompact (Subtype.val ⁻¹' spaAnalytic Aplus : Set (spa Aplus)) := by
  obtain ⟨T, hT⟩ := P.fg_extendedIdealOfDefinition
  have hopen : IsOpen (Ideal.span (T : Set A) : Set A) := by
    rw [hT]
    exact (P.isOpen_iff_exists_pow_le _).mpr ⟨1, by simp⟩
  rw [spaAnalytic_eq_biUnion_rationalSubset_of_span_eq_extendedIdealOfDefinition P Aplus T hT,
    Set.preimage_iUnion₂]
  exact T.isCompact_biUnion fun t _ ↦
    isCompact_of_mem_spaRationalFamily_of_pairOfDefinition P
      (mem_spaRationalFamily_iff.mpr ⟨T, t, hopen, rfl⟩)

end TopologicalRing

section TateRing

variable [IsTopologicalRing A] [IsTateRing A]

/-- Over a Tate ring, every point of `Spv A` is analytic, extending Wedhorn Remark 7.40(3) beyond
continuous points. -/
theorem isAnalyticPoint_of_isTateRing (v : Spv A) : IsAnalyticPoint v :=
  fun h ↦ (instIsPrimeSupp v).ne_top (IsTateRing.eq_top_of_isOpen h)

/-- **Wedhorn Remark 7.40(3).** Over a Tate ring, the analytic locus is the entire adic
spectrum: `Spa (A, A⁺)ᵃ = Spa (A, A⁺)`. -/
@[simp]
theorem spaAnalytic_eq_spa_of_isTateRing (Aplus : Subring A) :
    spaAnalytic Aplus = spa Aplus := by
  ext v
  rw [mem_spaAnalytic_iff]
  exact and_iff_left (isAnalyticPoint_of_isTateRing v)

end TateRing

end TauCeti.ValuationSpectrum

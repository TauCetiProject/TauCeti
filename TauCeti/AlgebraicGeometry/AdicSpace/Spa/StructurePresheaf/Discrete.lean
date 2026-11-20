/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.Discrete
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.IsSheafFor
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.KanExtension
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.SheafyRing

import TauCeti.RingTheory.Localization.Away.Gluing
import TauCeti.Topology.Category.TopCommRingCat.Sheaf

/-!
# Discrete Huber pairs are sheafy

Let `A` be a ring with the discrete topology and `A⁺ ⊆ A` a subring. Then the presentation-limit
structure presheaf of `X = Spa(A, A⁺)` is a sheaf of complete separated topological rings, and a
discrete Huber ring is sheafy in the sense of Wedhorn's Definition 8.26. This is Wedhorn's
Theorem 8.28 in case (c).

On a rational subset `R(T/s)` the sections are the localisation `A_s`, with the discrete topology
(`presentationLimitRingEquivOfDiscreteTopology`, `discreteTopology_presentationLimit_spaBasicOpen`),
and restriction to a smaller rational subset `R(T'/s')` is the localisation map `A_s → A_{s'}`
(`presentationLimitRingEquivOfDiscreteTopology_presentationLimitMap`), which exists because `s`
is a unit of `A_{s'}`. If rational subsets `R(Tᵢ/σᵢ)` cover `R(T/s)`, then the `σᵢ` generate the
unit ideal of `A_s`, since every prime of a discrete ring is open and its trivial valuation is a
point of `X` (`TauCeti.ValuationSpectrum.span_eq_top_of_rationalSubset_subset_iUnion`). So the
gluing condition for this cover is the sheaf property of the structure sheaf of `Spec A_s` for
the cover by the basic opens `D(σᵢ)`
(`IsLocalization.Away.existsUnique_forall_eq_of_span_eq_top`). For the topology, a rational
subset is quasi-compact, so finitely many members of the cover already separate sections; as all
the rings of sections are discrete, the sections over `R(T/s)` then carry the topology induced by
restriction to the cover. Gluing along rational covers of rational subsets is the sheaf condition
on the basis of rational subsets, and so on all opens
(`TauCeti.ValuationSpectrum.isSheaf_rational_comp_of_isSheafFor_ofArrows`,
`TauCeti.ValuationSpectrum.isSheaf_presentationLimitPresheaf_of_isSheaf_rational`).

No noetherian or finiteness hypothesis is needed: unlike the Tate case, no completion occurs.

## Main definitions

* `TauCeti.ValuationSpectrum.presentationLimitRingEquivOfDiscreteTopology`: over a discrete ring,
  the sections over `R(T/s)` are the localisation `A_s`.

## Main results

* `TauCeti.ValuationSpectrum.presentationLimitRingEquivOfDiscreteTopology_presentationLimitMap`:
  under these identifications, restriction between rational subsets is the localisation map.
* `TauCeti.ValuationSpectrum.discreteTopology_presentationLimit_spaBasicOpen`: the sections over
  `R(T/s)` form a discrete ring.
* `TauCeti.ValuationSpectrum.isSheaf_presentationLimitPresheaf_of_discreteTopology`: over a
  discrete ring, the presentation-limit structure presheaf is a sheaf of complete separated
  topological rings.
* `TauCeti.Huber.isSheafyForEveryPresentation_of_discreteTopology`: every ring of integral elements
  of a discrete ring satisfies `TauCeti.Huber.IsSheafyForEveryPresentation`.
* `TauCeti.Huber.isSheafyRing_of_discreteTopology`: a discrete Huber ring is sheafy.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 8.2(1), Definition
  8.26 and Theorem 8.28, case (c).
-/

public section

open CategoryTheory TopologicalSpace Opposite TauCeti.Huber TauCeti.Huber.PairOfDefinition

open scoped Pointwise

universe v

namespace TauCeti.ValuationSpectrum

variable {A : Type v} [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
  (P : PairOfDefinition A) (Aplus : Subring A)

/-! ### Sections over a rational subset -/

/-- **Over a discrete ring, the sections over `R(T/s)` are `A_s`.** The presentation limit over
the rational subset `R(T/s)` of `Spa(A, A⁺)` is the completed localisation `A⟨T/s⟩`
(`presentationLimitRationalIso`), which for a discrete ring is the localisation `A_s` itself
(`TauCeti.Huber.PairOfDefinition.completionLocEquivOfDiscreteTopology`). -/
noncomputable def presentationLimitRingEquivOfDiscreteTopology (T : Finset A) (s : A) :
    presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s) ≃+* Localization.Away s :=
  let p : Presentation P := ⟨T, s, hasDenominatorPower_of_discreteTopology P T s _⟩
  letI := locUniformSpace P T s _ p.hasDenominatorPower
  letI := isUniformAddGroup_locUniformSpace P T s _ p.hasDenominatorPower
  letI := isTopologicalRing_locUniformSpace P T s _ p.hasDenominatorPower
  let iso := presentationLimitRationalIso Aplus
    (fun _ _ ↦ isPowerBounded_iff.mpr (isBounded_of_discreteTopology _)) p (isOpen_discrete _)
  let f : presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s) →+* Localization.Away s :=
    (completionLocEquivOfDiscreteTopology P T s _ p.hasDenominatorPower).symm.toRingHom.comp
      ((eqToHom (completionLocObj_obj P T s _ p.hasDenominatorPower)).1.comp iso.hom.hom.1)
  RingEquiv.ofBijective f <|
    (completionLocEquivOfDiscreteTopology P T s _ p.hasDenominatorPower).symm.bijective.comp
      (bijective_presentationLimitRationalIso_hom Aplus
        (fun _ _ ↦ isPowerBounded_iff.mpr (isBounded_of_discreteTopology _)) p
        (isOpen_discrete _))

/-- **Over a discrete ring, restriction is the localisation map.** If `R(T'/s') ⊆ R(T/s)`, then
`s` is a unit of `A_{s'}`, and under `presentationLimitRingEquivOfDiscreteTopology` restriction of
sections from `R(T/s)` to `R(T'/s')` is the localisation map `A_s → A_{s'}`. This is Wedhorn's
comparison map of Proposition 8.2(1) for a discrete ring. -/
theorem presentationLimitRingEquivOfDiscreteTopology_presentationLimitMap {T T' : Finset A}
    {s s' : A} (h : spaBasicOpen Aplus T' s' ≤ spaBasicOpen Aplus T s)
    (x : presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s)) :
    presentationLimitRingEquivOfDiscreteTopology P Aplus T' s' ((presentationLimitMap h).hom.1 x) =
      IsLocalization.Away.lift s (isUnit_algebraMap_of_rationalSubset_subset _
        (fun _ _ ↦ isOpen_discrete _) (spaBasicOpen_le_spaBasicOpen_iff.mp h))
        (presentationLimitRingEquivOfDiscreteTopology P Aplus T s x) := by
  have hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a :=
    fun _ _ ↦ isPowerBounded_iff.mpr (isBounded_of_discreteTopology _)
  simp only [presentationLimitRingEquivOfDiscreteTopology, RingEquiv.ofBijective_apply,
    RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  set p : Presentation P := ⟨T, s, hasDenominatorPower_of_discreteTopology P T s _⟩
  set q : Presentation P := ⟨T', s', hasDenominatorPower_of_discreteTopology P T' s' _⟩
  let _ := locUniformSpace P T s _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P T s _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P T s _ p.hasDenominatorPower
  let _ := locUniformSpace P T' s' _ q.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P T' s' _ q.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P T' s' _ q.hasDenominatorPower
  -- Restriction is the comparison map of completed localisations, read through the projections.
  have H := presentationLimitRationalIso_inv_comp_map_comp_hom Aplus hAplus p q
    (isOpen_discrete _) (isOpen_discrete _) h
  rw [Iso.inv_comp_eq] at H
  have Hx : (presentationLimitRationalIso Aplus hAplus q (isOpen_discrete _)).hom.hom.1
      ((presentationLimitMap h).hom.1 x) =
      (homOfRationalSubsetSubset Aplus hAplus (spaBasicOpen_le_spaBasicOpen_iff.mp h)).hom.1
        ((presentationLimitRationalIso Aplus hAplus p (isOpen_discrete _)).hom.hom.1 x) :=
    congrArg (fun f ↦ f.hom.1 x) H
  rw [Hx]
  -- Read through the transports, the comparison morphism is the comparison ring homomorphism.
  have hY := congrArg (fun f ↦ f.hom ((presentationLimitRationalIso Aplus hAplus p
      (isOpen_discrete _)).hom.hom.1 x))
    (map_homOfRationalSubsetSubset_comp_completionLocObjCommRingCatIso_hom (p := p) (q := q)
      hAplus (spaBasicOpen_le_spaBasicOpen_iff.mp h))
  simp only [Presentation.completionLocObjCommRingCatIso_hom] at hY
  have hY' : (eqToHom (completionLocObj_obj P T' s' _ q.hasDenominatorPower)).1
      ((homOfRationalSubsetSubset (p := p) (q := q) Aplus hAplus
        (spaBasicOpen_le_spaBasicOpen_iff.mp h)).hom.1
          ((presentationLimitRationalIso Aplus hAplus p (isOpen_discrete _)).hom.hom.1 x)) =
      ringHomOfRationalSubsetSubset P Aplus hAplus T s _ p.hasDenominatorPower T' s' _
        q.hasDenominatorPower (spaBasicOpen_le_spaBasicOpen_iff.mp h)
        ((eqToHom (completionLocObj_obj P T s _ p.hasDenominatorPower)).1
          ((presentationLimitRationalIso Aplus hAplus p (isOpen_discrete _)).hom.hom.1 x)) :=
    hY
  rw [hY']
  -- Over a discrete ring the comparison ring homomorphism is the localisation map.
  obtain ⟨w, hw⟩ := (completionLocEquivOfDiscreteTopology P T s _ p.hasDenominatorPower).surjective
    ((eqToHom (completionLocObj_obj P T s _ p.hasDenominatorPower)).1
      ((presentationLimitRationalIso Aplus hAplus p (isOpen_discrete _)).hom.hom.1 x))
  rw [← hw, RingEquiv.symm_apply_apply, completionLocEquivOfDiscreteTopology_apply]
  exact (congrArg _ (ringHomOfRationalSubsetSubset_coe_of_discreteTopology P Aplus hAplus T s _
    p.hasDenominatorPower T' s' _ q.hasDenominatorPower (spaBasicOpen_le_spaBasicOpen_iff.mp h)
      w)).trans (completionLocEquivOfDiscreteTopology_symm_coe P T' s' _ q.hasDenominatorPower _)

/-- **Over a discrete ring, the sections over `R(T/s)` form a discrete ring.** They are
homeomorphic to `A⟨T/s⟩`, which is discrete
(`TauCeti.Huber.PairOfDefinition.discreteTopology_completion_locUniformSpace`). -/
theorem discreteTopology_presentationLimit_spaBasicOpen (T : Finset A) (s : A) :
    DiscreteTopology (presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s)) := by
  let p : Presentation P := ⟨T, s, hasDenominatorPower_of_discreteTopology P T s _⟩
  let _ := locUniformSpace P T s _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P T s _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P T s _ p.hasDenominatorPower
  have _ := discreteTopology_completion_locUniformSpace P T s _ p.hasDenominatorPower
  have hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a :=
    fun _ _ ↦ isPowerBounded_iff.mpr (isBounded_of_discreteTopology _)
  let iso := presentationLimitRationalIso Aplus hAplus p (isOpen_discrete _)
  let e := eqToHom (completionLocObj_obj P T s _ p.hasDenominatorPower)
  exact DiscreteTopology.of_continuous_injective (e.2.comp iso.hom.hom.2)
    (bijective_presentationLimitRationalIso_hom Aplus hAplus p (isOpen_discrete _)).1

/-! ### Gluing along rational covers -/

/-- Over a discrete ring, if rational subsets `R(T'ᵢ/σᵢ)` cover `R(T/s)`, the `σᵢ` generate the
unit ideal of `A_s`: this is `span_eq_top_of_rationalSubset_subset_iUnion` for opens. -/
private theorem span_eq_top_of_iSup_spaBasicOpen_eq {T : Finset A} {s : A} {ι : Type*}
    {T' : ι → Finset A} {σ : ι → A}
    (hcov : ⨆ i, spaBasicOpen Aplus (T' i) (σ i) = spaBasicOpen Aplus T s) :
    Ideal.span (Set.range fun i ↦ algebraMap A (Localization.Away s) (σ i)) = ⊤ := by
  refine span_eq_top_of_rationalSubset_subset_iUnion (Aplus := Aplus) (T := T) (s := s)
    (T' := T') _ (fun _ _ ↦ isOpen_discrete _) fun v hv ↦ ?_
  have hv' : (⟨v, rationalSubset_subset_spa Aplus T s hv⟩ : spa Aplus) ∈
      spaBasicOpen Aplus T s := mem_spaBasicOpen.mpr hv
  rw [← hcov, Opens.mem_iSup] at hv'
  obtain ⟨i, hi⟩ := hv'
  exact Set.mem_iUnion.mpr ⟨i, mem_spaBasicOpen.mp hi⟩

/-- Over a discrete ring, sections over the members of a cover of `R(T/s)` by rational subsets
`R(T'ᵢ/σᵢ)` that agree on the pairwise overlaps are the restrictions of a unique section over
`R(T/s)`. -/
private theorem existsUnique_presentationLimitMap_eq {T : Finset A} {s : A} {ι : Type*}
    {T' : ι → Finset A} {σ : ι → A}
    (hcov : ⨆ i, spaBasicOpen Aplus (T' i) (σ i) = spaBasicOpen Aplus T s)
    (x : ∀ i, presentationLimit (P := P) Aplus (spaBasicOpen Aplus (T' i) (σ i)))
    (hx : ∀ i j, (presentationLimitMap (P := P) (inf_le_left :
        spaBasicOpen Aplus (T' i) (σ i) ⊓ spaBasicOpen Aplus (T' j) (σ j) ≤ _)).hom.1 (x i) =
      (presentationLimitMap (P := P) (inf_le_right :
        spaBasicOpen Aplus (T' i) (σ i) ⊓ spaBasicOpen Aplus (T' j) (σ j) ≤ _)).hom.1 (x j)) :
    ∃! a : presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s), ∀ i,
      (presentationLimitMap (P := P) ((le_iSup _ i).trans_eq hcov)).hom.1 a = x i := by
  classical
  let U (i : ι) := spaBasicOpen Aplus (T' i) (σ i)
  have hle (i : ι) : U i ≤ spaBasicOpen Aplus T s := (le_iSup _ i).trans_eq hcov
  -- The pairwise overlaps are the rational subsets with denominators `σ i * σ j`.
  let T'' (i j : ι) : Finset A := insert (σ i) (T' i) * insert (σ j) (T' j)
  have hinter (i j : ι) : spaBasicOpen Aplus (T'' i j) (σ i * σ j) = U i ⊓ U j := by
    ext v
    simp only [U, T'', SetLike.mem_coe, Opens.mem_inf, mem_spaBasicOpen]
    rw [← Set.mem_inter_iff, rationalSubset_inter]
  have hl (i j : ι) : spaBasicOpen Aplus (T'' i j) (σ i * σ j) ≤ U i := (hinter i j).le.trans
    inf_le_left
  have hr (i j : ι) : spaBasicOpen Aplus (T'' i j) (σ i * σ j) ≤ U j := (hinter i j).le.trans
    inf_le_right
  let e := presentationLimitRingEquivOfDiscreteTopology P Aplus T s
  let ei (i : ι) := presentationLimitRingEquivOfDiscreteTopology P Aplus (T' i) (σ i)
  let eij (i j : ι) := presentationLimitRingEquivOfDiscreteTopology P Aplus (T'' i j) (σ i * σ j)
  have hopen : ∀ 𝔭 : Ideal A, 𝔭.IsPrime → IsOpen (𝔭 : Set A) := fun _ _ ↦ isOpen_discrete _
  -- The restriction maps, read on localisations.
  let ρ (i : ι) : Localization.Away s →+* Localization.Away (σ i) :=
    IsLocalization.Away.lift s (isUnit_algebraMap_of_rationalSubset_subset _ hopen
      (spaBasicOpen_le_spaBasicOpen_iff.mp (hle i)))
  let ρl (i j : ι) : Localization.Away (σ i) →+* Localization.Away (σ i * σ j) :=
    IsLocalization.Away.lift (σ i) (isUnit_algebraMap_of_rationalSubset_subset _ hopen
      (spaBasicOpen_le_spaBasicOpen_iff.mp (hl i j)))
  let ρr (i j : ι) : Localization.Away (σ j) →+* Localization.Away (σ i * σ j) :=
    IsLocalization.Away.lift (σ j) (isUnit_algebraMap_of_rationalSubset_subset _ hopen
      (spaBasicOpen_le_spaBasicOpen_iff.mp (hr i j)))
  have hρ (i : ι) (a : presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s)) :
      ei i ((presentationLimitMap (P := P) (hle i)).hom.1 a) = ρ i (e a) :=
    presentationLimitRingEquivOfDiscreteTopology_presentationLimitMap P Aplus (hle i) a
  -- The family of sections becomes a compatible family of elements of the localisations.
  have hcompat (i j : ι) : ρl i j (ei i (x i)) = ρr i j (ei j (x j)) := by
    have := congrArg (fun z ↦ eij i j ((presentationLimitMap (P := P) (hinter i j).le).hom.1 z))
      (hx i j)
    simp only [presentationLimitMap_apply_presentationLimitMap_apply] at this
    rwa [presentationLimitRingEquivOfDiscreteTopology_presentationLimitMap,
      presentationLimitRingEquivOfDiscreteTopology_presentationLimitMap] at this
  obtain ⟨b, hb, hbu⟩ := IsLocalization.Away.existsUnique_forall_eq_of_span_eq_top s
    (span_eq_top_of_iSup_spaBasicOpen_eq Aplus hcov)
    (ρ := ρ) (fun i r ↦ IsLocalization.Away.lift_eq _ _ r) (ρl := ρl) (ρr := ρr)
    (fun i j r ↦ IsLocalization.Away.lift_eq _ _ r) (fun i j r ↦ IsLocalization.Away.lift_eq _ _ r)
    (fun i ↦ ei i (x i)) hcompat
  refine ⟨e.symm b, fun i ↦ (ei i).injective ?_, fun a ha ↦ e.injective ?_⟩
  · rw [hρ, RingEquiv.apply_symm_apply, hb]
  · rw [RingEquiv.apply_symm_apply]
    exact hbu _ fun i ↦ by rw [← hρ, ha]

/-- Over a discrete ring, sections over `R(T/s)` carry the topology induced by restriction to a
cover by rational subsets. As `R(T/s)` is quasi-compact, finitely many members of the cover already
separate sections, and all the rings of sections are discrete. -/
private theorem isInducing_presentationLimitMap {T : Finset A} {s : A} {ι : Type*}
    {T' : ι → Finset A} {σ : ι → A}
    (hcov : ⨆ i, spaBasicOpen Aplus (T' i) (σ i) = spaBasicOpen Aplus T s) :
    Topology.IsInducing fun (a : presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s))
      (i : ι) ↦ (presentationLimitMap (P := P) ((le_iSup _ i).trans_eq hcov)).hom.1 a := by
  classical
  have _ : IsHuberRing A := ⟨⟨P⟩⟩
  let U (i : ι) := spaBasicOpen Aplus (T' i) (σ i)
  have hle (i : ι) : U i ≤ spaBasicOpen Aplus T s := (le_iSup _ i).trans_eq hcov
  -- A finite subcover, by quasi-compactness of `R(T/s)`.
  have hcpt : IsCompact (spaBasicOpen Aplus T s : Set (spa Aplus)) :=
    isCompact_of_mem_spaRationalFamily (mem_spaRationalOpens.mp
      (spaBasicOpen_mem_spaRationalOpens (isOpen_discrete _)))
  obtain ⟨J, hJ⟩ := hcpt.elim_finite_subcover (fun i ↦ (U i : Set (spa Aplus)))
    (fun i ↦ (U i).isOpen) (by rw [← hcov, Opens.coe_iSup])
  have hcovJ : ⨆ j : J, spaBasicOpen Aplus (T' j) (σ j) = spaBasicOpen Aplus T s := by
    refine le_antisymm (iSup_le fun j ↦ hle j) fun v hv ↦ ?_
    obtain ⟨i, hi, hvi⟩ := Set.mem_iUnion₂.mp (hJ hv)
    exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hvi⟩
  -- Restriction to the finite subcover is injective.
  have hinj (a b : presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s))
      (hab : ∀ j ∈ J, (presentationLimitMap (P := P) (hle j)).hom.1 a =
        (presentationLimitMap (P := P) (hle j)).hom.1 b) : a = b := by
    obtain ⟨c, -, hc⟩ := existsUnique_presentationLimitMap_eq P Aplus hcovJ
      (fun j ↦ (presentationLimitMap (P := P) (hle j)).hom.1 a) fun j k ↦ by
        simp only [presentationLimitMap_apply_presentationLimitMap_apply]
    exact (hc a fun _ ↦ rfl).trans (hc b fun j ↦ (hab j j.2).symm).symm
  -- A section is the only one with its restrictions to the finite subcover, and these
  -- restrictions are isolated points.
  have _ := discreteTopology_presentationLimit_spaBasicOpen P Aplus T s
  have _ (i : ι) := discreteTopology_presentationLimit_spaBasicOpen P Aplus (T' i) (σ i)
  refine ⟨DiscreteTopology.eq_bot.trans (eq_bot_of_singletons_open fun a ↦ ?_).symm⟩
  refine ⟨(J : Set ι).pi fun j ↦ {(presentationLimitMap (P := P) (hle j)).hom.1 a},
    isOpen_set_pi J.finite_toSet fun _ _ ↦ isOpen_discrete _, Set.ext fun b ↦ ?_⟩
  simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_singleton_iff]
  exact ⟨fun hb ↦ hinj b a hb, fun hb _ _ ↦ hb ▸ rfl⟩

/-- Over a discrete ring, compatible continuous ring homomorphisms into the sections over the
members of a cover of a rational subset by rational subsets glue uniquely to a continuous ring
homomorphism into the sections over the rational subset. -/
private theorem isSheafFor_ofArrows_spaRationalOpens {W : Opens ↥(spa Aplus)}
    (hW : W ∈ spaRationalOpens Aplus) {ι : Type*} {U : ι → Opens ↥(spa Aplus)}
    (hU : ∀ i, U i ∈ spaRationalOpens Aplus) (hcov : ⨆ i, U i = W)
    (E : _root_.TopCommRingCat.{v}) :
    (Presieve.ofArrows U fun i ↦ homOfLE ((le_iSup U i).trans_eq hcov)).IsSheafFor
      (presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι ⋙
        coyoneda.obj (op E)) := by
  obtain ⟨T, s, -, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hW
  choose T' σ _ hUeq using fun i ↦ mem_spaRationalOpens_iff_exists_spaBasicOpen.mp (hU i)
  obtain rfl : U = fun i ↦ spaBasicOpen Aplus (T' i) (σ i) := funext hUeq
  rw [Presieve.isSheafFor_iff_generate]
  refine TopCommRingCat.isSheafFor_of_isSheafFor_forget
    (presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι)
    (Sieve.ofArrows _ _).arrows ((Presieve.isSheafFor_iff_generate _).mp ?_)
    ((TopCommRingCat.isInducing_restrictionMap_ofArrows_iff _ _ _).mpr ?_) E
  · exact (isSheafFor_ofArrows_iff_existsUnique_presentationLimitMap P _).mpr
      (existsUnique_presentationLimitMap_eq P Aplus hcov)
  · exact (isInducing_restrictionMap_iff_isInducing_presentationLimitMap P _).mpr
      (isInducing_presentationLimitMap P Aplus hcov)

/-! ### Sheafiness -/

/-- **Wedhorn's Theorem 8.28(c) for a pair: the structure presheaf of a discrete Huber pair is a
sheaf.** Let `A` be a ring with the discrete topology, `P` a pair of definition and `A⁺` any
subring of `A`. Then the presentation-limit structure presheaf of `Spa(A, A⁺)` is a sheaf of
complete separated topological rings on all opens. -/
theorem isSheaf_presentationLimitPresheaf_of_discreteTopology :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus) := by
  refine isSheaf_presentationLimitPresheaf_of_isSheaf_rational <|
    Presheaf.isSheaf_of_isSheaf_comp _ _ TopCommRingCat.isCompleteSeparated.ι fun E ↦ ?_
  -- a sheaf of topological rings is one whose continuous homomorphisms out of each `E` glue
  exact isSheaf_rational_comp_of_isSheafFor_ofArrows P _ fun hW hU hcov ↦
    isSheafFor_ofArrows_spaRationalOpens P Aplus hW hU hcov E

end TauCeti.ValuationSpectrum

namespace TauCeti.Huber

open TauCeti.ValuationSpectrum

/-- **Discrete Huber pairs are sheafy**: every ring of integral elements `A⁺` of a discrete ring
`A` satisfies `TauCeti.Huber.IsSheafyForEveryPresentation`, so the structure presheaf of
`Spa(A, A⁺)` is a sheaf of complete separated topological rings. This is Wedhorn's
Theorem 8.28(c) for the pair `(A, A⁺)`. -/
theorem isSheafyForEveryPresentation_of_discreteTopology {A : Type v} [CommRing A]
    [TopologicalSpace A] [DiscreteTopology A] {Aplus : Subring A}
    (hAplus : IsRingOfIntegralElements Aplus) : IsSheafyForEveryPresentation Aplus :=
  ⟨hAplus, fun P _ ↦ isSheaf_presentationLimitPresheaf_of_discreteTopology P Aplus⟩

/-- **A discrete Huber ring is sheafy** in the sense of Wedhorn's Definition 8.26
(`TauCeti.Huber.IsSheafyRing`). This is Wedhorn's Theorem 8.28(c). -/
theorem isSheafyRing_of_discreteTopology {A : Type v} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [DiscreteTopology A] : IsSheafyRing A := by
  have _ : DiscreteUniformity A := IsRightUniformAddGroup.discreteUniformity
  exact isSheafyRing_iff_forall_isSheafyForEveryPresentation.mpr fun _ ↦
    isSheafyForEveryPresentation_of_discreteTopology

end TauCeti.Huber

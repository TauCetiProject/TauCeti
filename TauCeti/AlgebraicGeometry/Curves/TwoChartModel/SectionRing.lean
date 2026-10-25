/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Basic
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.SectionRing.Basic

import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# The two-chart model is `Proj` of a section ring

Let `F / k` be an algebraic function field and let `z ∈ Fˣ`. The degree-one sections `1` and
`z` of the pole divisor `(z)_∞` define two standard opens in `Proj` of its section ring
`⨁ₙ L(n (z)_∞)`. This file identifies their homogeneous coordinate rings with the holomorphy rings
used to construct the two-chart model:

* localization at `X` gives the finite chart, where `z` is regular;
* localization at `z X` gives the infinity chart, where `z⁻¹` is regular.

Thus each standard open is canonically isomorphic to the corresponding affine chart of
`TauCeti.AlgebraicGeometry.twoChartModel`. The ring identifications are
`TauCeti.Divisor.sectionRingAwayOneEquiv` and `TauCeti.Divisor.sectionRingAwayGeneratorEquiv`;
this file composes them with Mathlib's `AlgebraicGeometry.Proj.basicOpenIsoSpec`.

The two chart isomorphisms glue to an isomorphism of `Proj` of the section ring with the whole
two-chart model. On the overlap `Spec 𝒪_{z, z⁻¹}` both charts give the point of `Proj` whose
homogeneous coordinates send `∑ fₙ Xⁿ` to `∑ fₙ`, so they define a morphism out of the pushout
of the two charts. Each chart maps isomorphically onto its standard open, the two standard opens
cover `Proj`, and a point of the chart at infinity landing in `D₊(X)` lies where `X / (z X) = z⁻¹`
is invertible, that is, in the overlap; so the morphism is a bijective open immersion.

## Main definitions

* `TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjFiniteChartIso`: the resulting
  isomorphism from the standard open `D₊(X)` to the finite chart.
* `TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjInfinityChartIso`: the resulting
  isomorphism from the standard open `D₊(z X)` to the infinity chart.
* `TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjIso`: the isomorphism of `Proj` of the
  section ring of `(z)_∞` with the two-chart model built from `z`.

## Main results

* `TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjFiniteChartIso_hom` and
  `TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjInfinityChartIso_hom`: the chart
  isomorphisms are the canonical maps `D₊(f) ⟶ Spec A₍f₎` followed by the ring identifications.
* `TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjChart_cover`: the two standard opens
  cover `Proj`.
* `TauCeti.AlgebraicGeometry.twoChartModel.ιFinite_sectionRingProjIso_inv` and
  `TauCeti.AlgebraicGeometry.twoChartModel.ιInfinity_sectionRingProjIso_inv`: on each chart, the
  isomorphism with `Proj` is the inverse of the chart isomorphism.
* `TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjIso_hom_over`: the isomorphism with
  `Proj` lies over `Spec k`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Section II.2.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.2 and Appendix B.
-/

public section

open CategoryTheory Polynomial HomogeneousLocalization

namespace TauCeti

open _root_.AlgebraicGeometry

universe u

variable {k F : Type u} [Field k] [Field F] [Algebra k F]

namespace AlgebraicGeometry.twoChartModel

open Divisor

/-- The standard open `D₊(X)` of `Proj` of the section ring of `(z)_∞` is the finite affine
chart of the two-chart model. -/
noncomputable def sectionRingProjFiniteChartIso (hF : IsFunctionField k F) (z : Fˣ) :
    (Proj.basicOpen (sectionRingGrade (poles hF z))
      (polesSectionOne hF z)).toScheme ≅
      Spec (.of (holomorphyRing {P : Place k F | (z : F) ∈ P.integers})) :=
  Proj.basicOpenIsoSpec (sectionRingGrade (poles hF z))
      (polesSectionOne hF z) (monomialDegreeOne_mem_sectionRingGrade _) (by simp) ≪≫
    Scheme.Spec.mapIso (sectionRingAwayOneEquiv hF z).toRingEquiv.toCommRingCatIso.symm.op

/-- The chart isomorphism `TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjFiniteChartIso`
is Mathlib's isomorphism `D₊(X) ≅ Spec A₍X₎` followed by the map induced by
`TauCeti.Divisor.sectionRingAwayOneEquiv`. -/
theorem sectionRingProjFiniteChartIso_hom (hF : IsFunctionField k F) (z : Fˣ) :
    (sectionRingProjFiniteChartIso hF z).hom =
      (Proj.basicOpenIsoSpec (sectionRingGrade (poles hF z)) (polesSectionOne hF z)
          (monomialDegreeOne_mem_sectionRingGrade _) Nat.one_pos).hom ≫
        Spec.map (CommRingCat.ofHom (sectionRingAwayOneEquiv hF z).symm.toRingHom) := by
  rfl

/-- The standard open `D₊(z X)` of `Proj` of the section ring of `(z)_∞` is the affine chart
at infinity of the two-chart model. -/
noncomputable def sectionRingProjInfinityChartIso (hF : IsFunctionField k F) (z : Fˣ) :
    (Proj.basicOpen (sectionRingGrade (poles hF z))
      (polesSectionGenerator hF z)).toScheme ≅
      Spec (.of (holomorphyRing {P : Place k F | (z : F)⁻¹ ∈ P.integers})) :=
  Proj.basicOpenIsoSpec (sectionRingGrade (poles hF z))
      (polesSectionGenerator hF z) (monomialDegreeOne_mem_sectionRingGrade _) (by simp) ≪≫
    Scheme.Spec.mapIso (sectionRingAwayGeneratorEquiv hF z).toRingEquiv.toCommRingCatIso.symm.op

/-- The chart isomorphism
`TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjInfinityChartIso` is Mathlib's isomorphism
`D₊(z X) ≅ Spec A₍z X₎` followed by the map induced by
`TauCeti.Divisor.sectionRingAwayGeneratorEquiv`. -/
theorem sectionRingProjInfinityChartIso_hom (hF : IsFunctionField k F) (z : Fˣ) :
    (sectionRingProjInfinityChartIso hF z).hom =
      (Proj.basicOpenIsoSpec (sectionRingGrade (poles hF z)) (polesSectionGenerator hF z)
          (monomialDegreeOne_mem_sectionRingGrade _) Nat.one_pos).hom ≫
        Spec.map (CommRingCat.ofHom (sectionRingAwayGeneratorEquiv hF z).symm.toRingHom) := by
  rfl

/-- The standard opens `D₊(X)` and `D₊(z X)` cover `Proj` of the section ring of `(z)_∞`. -/
theorem sectionRingProjChart_cover (hF : IsFunctionField k F) (z : Fˣ) :
    Proj.basicOpen (sectionRingGrade (poles hF z)) (polesSectionOne hF z) ⊔
      Proj.basicOpen (sectionRingGrade (poles hF z)) (polesSectionGenerator hF z) = ⊤ := by
  apply top_unique
  intro x _
  rw [TopologicalSpace.Opens.mem_sup, Proj.mem_basicOpen, Proj.mem_basicOpen]
  by_contra h
  push Not at h
  apply x.not_irrelevant_le
  refine (irrelevant_le_radical_span_monomialDegreeOne_poles hF z).trans ?_
  apply x.isPrime.radical_le_iff.mpr
  rw [Ideal.span_le]
  rintro y (rfl | rfl)
  · exact h.1
  · exact h.2

/-! ### The global isomorphism -/

/-- The inverse of `TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjFiniteChartIso`,
followed by the inclusion of `D₊(X)`, is Mathlib's chart `Spec A₍X₎ ⟶ Proj` precomposed with the
map induced by `TauCeti.Divisor.sectionRingAwayOneEquiv`. -/
theorem sectionRingProjFiniteChartIso_inv_ι (hF : IsFunctionField k F) (z : Fˣ) :
    (sectionRingProjFiniteChartIso hF z).inv ≫
        (Proj.basicOpen (sectionRingGrade (poles hF z)) (polesSectionOne hF z)).ι =
      Spec.map (CommRingCat.ofHom (sectionRingAwayOneEquiv hF z).toRingHom) ≫
        Proj.awayι _ _ (monomialDegreeOne_mem_sectionRingGrade _) Nat.one_pos := by
  -- The chart isomorphism is defined as `Proj.basicOpenIsoSpec` followed by `Spec` of the ring
  -- identification, and `Proj.awayι` as the inverse of `Proj.basicOpenIsoSpec` followed by `ι`.
  rfl

/-- The inverse of `TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjInfinityChartIso`,
followed by the inclusion of `D₊(z X)`, is Mathlib's chart `Spec A₍z X₎ ⟶ Proj` precomposed with
the map induced by `TauCeti.Divisor.sectionRingAwayGeneratorEquiv`. -/
theorem sectionRingProjInfinityChartIso_inv_ι (hF : IsFunctionField k F) (z : Fˣ) :
    (sectionRingProjInfinityChartIso hF z).inv ≫
        (Proj.basicOpen (sectionRingGrade (poles hF z)) (polesSectionGenerator hF z)).ι =
      Spec.map (CommRingCat.ofHom (sectionRingAwayGeneratorEquiv hF z).toRingHom) ≫
        Proj.awayι _ _ (monomialDegreeOne_mem_sectionRingGrade _) Nat.one_pos := by
  -- The chart isomorphism is defined as `Proj.basicOpenIsoSpec` followed by `Spec` of the ring
  -- identification, and `Proj.awayι` as the inverse of `Proj.basicOpenIsoSpec` followed by `ι`.
  rfl

/-- Evaluation at `X = 1`, `TauCeti.Divisor.evalOne`, on the section ring of `(z)_∞`, viewed as
landing in the functions regular wherever `z` is a unit: each `fₙ ∈ L(n (z)_∞)` is regular
wherever `z` is. These are the homogeneous coordinates of the overlap of the two charts. -/
private noncomputable def overlapEvalOne (hF : IsFunctionField k F) (z : Fˣ) :
    sectionRing (poles hF z) →ₐ[k]
      holomorphyRing ({P : Place k F | (z : F) ∈ P.integers} ∩
        {P : Place k F | (z : F)⁻¹ ∈ P.integers}) :=
  (evalOne (poles hF z)).codRestrict _ fun g ↦ mem_holomorphyRing_iff.mpr fun P hP ↦ by
    have hP0 : (poles hF z).coeff P = 0 := (coeff_poles_eq_zero_iff hF z P).mpr hP.1
    rw [evalOne_apply, Polynomial.eval_eq_sum_range]
    simp only [one_pow, mul_one]
    refine sum_mem fun n _ ↦ ?_
    have hn := mem_riemannRochSpace_iff.mp (mem_coeffSubalgebra_iff.mp g.2 n) P
    rw [WeilDivisor.coeff_nsmul, hP0, mul_zero, WithZero.exp_zero] at hn
    exact P.mem_integers_iff.mpr hn

private theorem coe_overlapEvalOne (hF : IsFunctionField k F) (z : Fˣ)
    (g : sectionRing (poles hF z)) : (overlapEvalOne hF z g : F) = evalOne (poles hF z) g :=
  AlgHom.coe_codRestrict _ _ _ g

private theorem overlapEvalOne_polesSectionOne (hF : IsFunctionField k F) (z : Fˣ) :
    overlapEvalOne hF z (polesSectionOne hF z) = 1 := by
  apply Subtype.ext
  rw [coe_overlapEvalOne, evalOne_of_mem (monomialDegreeOne_mem_sectionRingGrade _),
    coe_monomialDegreeOne]
  simp

private theorem coe_overlapEvalOne_polesSectionGenerator (hF : IsFunctionField k F) (z : Fˣ) :
    (overlapEvalOne hF z (polesSectionGenerator hF z) : F) = z := by
  rw [coe_overlapEvalOne, evalOne_of_mem (monomialDegreeOne_mem_sectionRingGrade _),
    coe_monomialDegreeOne]
  simp

private theorem isUnit_overlapEvalOne_polesSectionOne (hF : IsFunctionField k F) (z : Fˣ) :
    IsUnit (overlapEvalOne hF z (polesSectionOne hF z)) := by
  rw [overlapEvalOne_polesSectionOne]
  exact isUnit_one

private theorem isUnit_overlapEvalOne_polesSectionGenerator (hF : IsFunctionField k F) (z : Fˣ) :
    IsUnit (overlapEvalOne hF z (polesSectionGenerator hF z)) :=
  isUnit_iff_exists_inv.mpr ⟨⟨(z : F)⁻¹, mem_holomorphyRing_iff.mpr fun _ hP ↦ hP.2⟩,
    Subtype.ext (by simp [coe_overlapEvalOne_polesSectionGenerator])⟩

/-- On the overlap, the finite chart `A₍X₎ ≅ 𝒪_z` is read through the homogeneous coordinates
`overlapEvalOne`. -/
private theorem finiteChartRestriction_comp_sectionRingAwayOneEquiv (hF : IsFunctionField k F)
    (z : Fˣ) :
    (finiteChartRestriction (k := k) (z : F)).toRingHom.comp
        (sectionRingAwayOneEquiv hF z).toRingHom =
      Away.lift _ (overlapEvalOne hF z).toRingHom
        (isUnit_overlapEvalOne_polesSectionOne hF z) := by
  ext w
  obtain ⟨r, g, hg, rfl⟩ := Away.mk_surjective _ (monomialDegreeOne_mem_sectionRingGrade _) w
  have hg' : g ∈ sectionRingGrade (poles hF z) r := by simpa using hg
  have hu : (isUnit_overlapEvalOne_polesSectionOne hF z).unit = 1 :=
    Units.ext (overlapEvalOne_polesSectionOne hF z)
  rw [Away.lift_mk, hu]
  simp [sectionRingAwayOneEquiv_mk hF z r g hg', coe_overlapEvalOne, evalOne_of_mem hg']

/-- On the overlap, the chart at infinity `A₍z X₎ ≅ 𝒪_{z⁻¹}` is read through the homogeneous
coordinates `overlapEvalOne`. -/
private theorem infinityChartRestriction_comp_sectionRingAwayGeneratorEquiv
    (hF : IsFunctionField k F) (z : Fˣ) :
    (infinityChartRestriction (k := k) (z : F)).toRingHom.comp
        (sectionRingAwayGeneratorEquiv hF z).toRingHom =
      Away.lift _ (overlapEvalOne hF z).toRingHom
        (isUnit_overlapEvalOne_polesSectionGenerator hF z) := by
  ext w
  obtain ⟨r, g, hg, rfl⟩ := Away.mk_surjective _ (monomialDegreeOne_mem_sectionRingGrade _) w
  have hg' : g ∈ sectionRingGrade (poles hF z) r := by simpa using hg
  have hinv := map_units_inv (holomorphyRing ({P : Place k F | (z : F) ∈ P.integers} ∩
    {P : Place k F | (z : F)⁻¹ ∈ P.integers})).val
    ((isUnit_overlapEvalOne_polesSectionGenerator hF z).unit ^ r)
  simp only [Subalgebra.coe_val, Units.val_pow_eq_pow_val, IsUnit.unit_spec,
    SubmonoidClass.coe_pow, coe_overlapEvalOne_polesSectionGenerator] at hinv
  rw [Away.lift_mk, MulMemClass.coe_mul, hinv]
  simp [sectionRingAwayGeneratorEquiv_mk hF z r g hg', coe_overlapEvalOne, evalOne_of_mem hg']

/-- The inverses of the two chart isomorphisms agree on the overlap `Spec 𝒪_{z, z⁻¹}` of the
two-chart model: both give the point of `Proj` with homogeneous coordinates `overlapEvalOne`. -/
private theorem specMap_chartIso_inv_ι_condition (hF : IsFunctionField k F) (z : Fˣ) :
    Spec.map (CommRingCat.ofHom (finiteChartRestriction (k := k) (z : F)).toRingHom) ≫
        (sectionRingProjFiniteChartIso hF z).inv ≫
          (Proj.basicOpen (sectionRingGrade (poles hF z)) (polesSectionOne hF z)).ι =
      Spec.map (CommRingCat.ofHom (infinityChartRestriction (k := k) (z : F)).toRingHom) ≫
        (sectionRingProjInfinityChartIso hF z).inv ≫
          (Proj.basicOpen (sectionRingGrade (poles hF z)) (polesSectionGenerator hF z)).ι := by
  rw [sectionRingProjFiniteChartIso_inv_ι, sectionRingProjInfinityChartIso_inv_ι,
    ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, finiteChartRestriction_comp_sectionRingAwayOneEquiv,
    infinityChartRestriction_comp_sectionRingAwayGeneratorEquiv]
  exact Proj.SpecMap_awayLift_awayι_eq _ _ Nat.one_pos _ Nat.one_pos _ _

/-- The morphism from the two-chart model to `Proj` of the section ring of `(z)_∞`, given on
each chart by the inverse of the corresponding chart isomorphism. -/
private noncomputable def toSectionRingProj (hF : IsFunctionField k F) (z : Fˣ) :
    twoChartModel hF z.ne_zero ⟶ Proj (sectionRingGrade (poles hF z)) :=
  (isPushout hF z.ne_zero).desc
    ((sectionRingProjFiniteChartIso hF z).inv ≫
      (Proj.basicOpen (sectionRingGrade (poles hF z)) (polesSectionOne hF z)).ι)
    ((sectionRingProjInfinityChartIso hF z).inv ≫
      (Proj.basicOpen (sectionRingGrade (poles hF z)) (polesSectionGenerator hF z)).ι)
    (specMap_chartIso_inv_ι_condition hF z)

private theorem ιFinite_toSectionRingProj (hF : IsFunctionField k F) (z : Fˣ) :
    ιFinite hF z.ne_zero ≫ toSectionRingProj hF z =
      (sectionRingProjFiniteChartIso hF z).inv ≫
        (Proj.basicOpen (sectionRingGrade (poles hF z)) (polesSectionOne hF z)).ι :=
  (isPushout hF z.ne_zero).inl_desc _ _ _

private theorem ιInfinity_toSectionRingProj (hF : IsFunctionField k F) (z : Fˣ) :
    ιInfinity hF z.ne_zero ≫ toSectionRingProj hF z =
      (sectionRingProjInfinityChartIso hF z).inv ≫
        (Proj.basicOpen (sectionRingGrade (poles hF z)) (polesSectionGenerator hF z)).ι :=
  (isPushout hF z.ne_zero).inr_desc _ _ _

private theorem range_ιFinite_toSectionRingProj (hF : IsFunctionField k F) (z : Fˣ) :
    Set.range (ιFinite hF z.ne_zero ≫ toSectionRingProj hF z) =
      Proj.basicOpen (sectionRingGrade (poles hF z)) (polesSectionOne hF z) := by
  rw [ιFinite_toSectionRingProj]
  exact congrArg SetLike.coe
    ((Scheme.Hom.opensRange_comp_of_isIso _ _).trans (Scheme.Opens.opensRange_ι _))

private theorem range_ιInfinity_toSectionRingProj (hF : IsFunctionField k F) (z : Fˣ) :
    Set.range (ιInfinity hF z.ne_zero ≫ toSectionRingProj hF z) =
      Proj.basicOpen (sectionRingGrade (poles hF z)) (polesSectionGenerator hF z) := by
  rw [ιInfinity_toSectionRingProj]
  exact congrArg SetLike.coe
    ((Scheme.Hom.opensRange_comp_of_isIso _ _).trans (Scheme.Opens.opensRange_ι _))

/-- A point of the chart at infinity which is sent into `D₊(X)` lies in the overlap of the two
charts: on the chart at infinity, `D₊(X)` is the locus where `X / (z X) = z⁻¹` is invertible. -/
private theorem mem_range_specMap_infinityChartRestriction (hF : IsFunctionField k F) (z : Fˣ)
    {b : Spec (.of (holomorphyRing {P : Place k F | (z : F)⁻¹ ∈ P.integers}))}
    (hb : (ιInfinity hF z.ne_zero ≫ toSectionRingProj hF z) b ∈
      Proj.basicOpen (sectionRingGrade (poles hF z)) (polesSectionOne hF z)) :
    b ∈ Set.range
      (Spec.map (CommRingCat.ofHom (infinityChartRestriction (k := k) (z : F)).toRingHom)) := by
  have hz : (z : F)⁻¹ ∈ holomorphyRing {P : Place k F | (z : F)⁻¹ ∈ P.integers} :=
    mem_holomorphyRing_iff.mpr fun _ hP ↦ hP
  rw [← Scheme.Hom.mem_preimage, ιInfinity_toSectionRingProj,
    sectionRingProjInfinityChartIso_inv_ι, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen _ _ _ (monomialDegreeOne_mem_sectionRingGrade _) Nat.one_pos,
    SpecMap_preimage_basicOpen] at hb
  -- On the chart at infinity, `X / (z X)` is `z⁻¹`.
  have he : sectionRingAwayGeneratorEquiv hF z (Away.isLocalizationElem
      (monomialDegreeOne_mem_sectionRingGrade (mem_riemannRochSpace_poles hF z))
      (monomialDegreeOne_mem_sectionRingGrade
        (one_mem_riemannRochSpace_iff.mpr (isEffective_poles hF z).zero_le))) =
        ⟨(z : F)⁻¹, hz⟩ := by
    have h1 : polesSectionOne hF z ^ 1 ∈ sectionRingGrade (poles hF z) 1 := by
      rw [pow_one]
      exact monomialDegreeOne_mem_sectionRingGrade _
    apply Subtype.ext
    simp [sectionRingAwayGeneratorEquiv_mk hF z 1 _ h1]
  simp only [CommRingCat.hom_ofHom, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_toRingEquiv, he] at hb
  -- The restriction from the chart at infinity to the overlap is the localization away from `z⁻¹`.
  let := (infinityChartRestriction (k := k) (z : F)).toRingHom.toAlgebra
  have : IsScalarTower (holomorphyRing {P : Place k F | (z : F)⁻¹ ∈ P.integers})
      (holomorphyRing ({P : Place k F | (z : F) ∈ P.integers} ∩
        {P : Place k F | (z : F)⁻¹ ∈ P.integers})) F :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have := isLocalization_away_holomorphyRing_inter hF ⟨(z : F)⁻¹, hz⟩ (inv_ne_zero z.ne_zero)
    (T := {P : Place k F | (z : F) ∈ P.integers} ∩ {P : Place k F | (z : F)⁻¹ ∈ P.integers})
    (by rw [inv_inv, Set.inter_comm])
  exact (PrimeSpectrum.localization_away_comap_range (holomorphyRing
    ({P : Place k F | (z : F) ∈ P.integers} ∩ {P : Place k F | (z : F)⁻¹ ∈ P.integers})) _).ge hb

private theorem toSectionRingProj_injective (hF : IsFunctionField k F) (z : Fˣ) :
    Function.Injective (toSectionRingProj hF z) := by
  have hinjFinite : Function.Injective (ιFinite hF z.ne_zero ≫ toSectionRingProj hF z) := by
    rw [ιFinite_toSectionRingProj]
    exact (Scheme.Hom.isOpenEmbedding _).injective
  have hinjInfinity : Function.Injective (ιInfinity hF z.ne_zero ≫ toSectionRingProj hF z) := by
    rw [ιInfinity_toSectionRingProj]
    exact (Scheme.Hom.isOpenEmbedding _).injective
  -- A point of the finite chart and a point of the chart at infinity with the same image are
  -- the same point of the overlap.
  have key (a b) (h : toSectionRingProj hF z (ιFinite hF z.ne_zero a) =
      toSectionRingProj hF z (ιInfinity hF z.ne_zero b)) :
      ιFinite hF z.ne_zero a = ιInfinity hF z.ne_zero b := by
    have hb : (ιInfinity hF z.ne_zero ≫ toSectionRingProj hF z) b ∈
        Proj.basicOpen (sectionRingGrade (poles hF z)) (polesSectionOne hF z) := by
      rw [← SetLike.mem_coe, ← range_ιFinite_toSectionRingProj, Scheme.Hom.comp_apply, ← h]
      exact ⟨a, rfl⟩
    obtain ⟨c, rfl⟩ := mem_range_specMap_infinityChartRestriction hF z hb
    have hc := congrArg (· c) (condition hF z.ne_zero)
    simp only [Scheme.Hom.comp_apply] at hc
    rw [← hc] at h ⊢
    exact congrArg (ιFinite hF z.ne_zero)
      (hinjFinite (by simpa only [Scheme.Hom.comp_apply] using h))
  intro p q hpq
  rcases (Set.ext_iff.mp (range_ιFinite_union_range_ιInfinity hF z.ne_zero) p).mpr trivial with
    ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
  rcases (Set.ext_iff.mp (range_ιFinite_union_range_ιInfinity hF z.ne_zero) q).mpr trivial with
    ⟨b, rfl⟩ | ⟨b, rfl⟩
  · exact congrArg (ιFinite hF z.ne_zero)
      (hinjFinite (by simpa only [Scheme.Hom.comp_apply] using hpq))
  · exact key a b hpq
  · exact (key b a hpq.symm).symm
  · exact congrArg (ιInfinity hF z.ne_zero)
      (hinjInfinity (by simpa only [Scheme.Hom.comp_apply] using hpq))

private theorem toSectionRingProj_surjective (hF : IsFunctionField k F) (z : Fˣ) :
    Function.Surjective (toSectionRingProj hF z) := by
  intro y
  have hy : y ∈ Proj.basicOpen (sectionRingGrade (poles hF z)) (polesSectionOne hF z) ⊔
      Proj.basicOpen (sectionRingGrade (poles hF z)) (polesSectionGenerator hF z) := by
    rw [sectionRingProjChart_cover]
    trivial
  rcases hy with hy | hy
  · rw [← range_ιFinite_toSectionRingProj] at hy
    obtain ⟨a, rfl⟩ := hy
    exact ⟨_, rfl⟩
  · rw [← range_ιInfinity_toSectionRingProj] at hy
    obtain ⟨a, rfl⟩ := hy
    exact ⟨_, rfl⟩

private instance (hF : IsFunctionField k F) (z : Fˣ) : IsIso (toSectionRingProj hF z) := by
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨IsOpenImmersion.of_forall_source_exists _ (toSectionRingProj_injective hF z)
    fun p ↦ ?_, ⟨toSectionRingProj_surjective hF z⟩⟩
  rcases (Set.ext_iff.mp (range_ιFinite_union_range_ιInfinity hF z.ne_zero) p).mpr trivial with
    ⟨a, rfl⟩ | ⟨a, rfl⟩
  · refine ⟨_, ιFinite hF z.ne_zero, inferInstance, ⟨a, rfl⟩, ?_⟩
    rw [ιFinite_toSectionRingProj]
    infer_instance
  · refine ⟨_, ιInfinity hF z.ne_zero, inferInstance, ⟨a, rfl⟩, ?_⟩
    rw [ιInfinity_toSectionRingProj]
    infer_instance

/-- **The two-chart model is `Proj` of the section ring of a pole divisor.** For `z ∈ Fˣ`, the
scheme glued from `Spec 𝒪_z` and `Spec 𝒪_{z⁻¹}` along `Spec 𝒪_{z, z⁻¹}` is isomorphic to `Proj`
of the section ring `⨁ₙ L(n (z)_∞)`, compatibly with the chart isomorphisms
`D₊(X) ≅ Spec 𝒪_z` and `D₊(z X) ≅ Spec 𝒪_{z⁻¹}`
(`TauCeti.AlgebraicGeometry.twoChartModel.ιFinite_sectionRingProjIso_inv` and
`TauCeti.AlgebraicGeometry.twoChartModel.ιInfinity_sectionRingProjIso_inv`). -/
noncomputable def sectionRingProjIso (hF : IsFunctionField k F) (z : Fˣ) :
    Proj (sectionRingGrade (poles hF z)) ≅ twoChartModel hF z.ne_zero :=
  (asIso (toSectionRingProj hF z)).symm

/-- On the finite chart, the inverse of `TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjIso`
is the inverse of the chart isomorphism `D₊(X) ≅ Spec 𝒪_z`. -/
@[reassoc (attr := simp)]
theorem ιFinite_sectionRingProjIso_inv (hF : IsFunctionField k F) (z : Fˣ) :
    ιFinite hF z.ne_zero ≫ (sectionRingProjIso hF z).inv =
      (sectionRingProjFiniteChartIso hF z).inv ≫
        (Proj.basicOpen (sectionRingGrade (poles hF z)) (polesSectionOne hF z)).ι :=
  ιFinite_toSectionRingProj hF z

/-- On the chart at infinity, the inverse of
`TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjIso` is the inverse of the chart
isomorphism `D₊(z X) ≅ Spec 𝒪_{z⁻¹}`. -/
@[reassoc (attr := simp)]
theorem ιInfinity_sectionRingProjIso_inv (hF : IsFunctionField k F) (z : Fˣ) :
    ιInfinity hF z.ne_zero ≫ (sectionRingProjIso hF z).inv =
      (sectionRingProjInfinityChartIso hF z).inv ≫
        (Proj.basicOpen (sectionRingGrade (poles hF z)) (polesSectionGenerator hF z)).ι :=
  ιInfinity_toSectionRingProj hF z

/-- On `D₊(X)`, `TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjIso` is the chart
isomorphism `D₊(X) ≅ Spec 𝒪_z` followed by the finite chart. -/
@[reassoc (attr := simp)]
theorem basicOpen_polesSectionOne_ι_sectionRingProjIso_hom (hF : IsFunctionField k F) (z : Fˣ) :
    (Proj.basicOpen (sectionRingGrade (poles hF z)) (polesSectionOne hF z)).ι ≫
        (sectionRingProjIso hF z).hom =
      (sectionRingProjFiniteChartIso hF z).hom ≫ ιFinite hF z.ne_zero := by
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← ιFinite_sectionRingProjIso_inv, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- On `D₊(z X)`, `TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjIso` is the chart
isomorphism `D₊(z X) ≅ Spec 𝒪_{z⁻¹}` followed by the chart at infinity. -/
@[reassoc (attr := simp)]
theorem basicOpen_polesSectionGenerator_ι_sectionRingProjIso_hom (hF : IsFunctionField k F)
    (z : Fˣ) :
    (Proj.basicOpen (sectionRingGrade (poles hF z)) (polesSectionGenerator hF z)).ι ≫
        (sectionRingProjIso hF z).hom =
      (sectionRingProjInfinityChartIso hF z).hom ≫ ιInfinity hF z.ne_zero := by
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← ιInfinity_sectionRingProjIso_inv, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- **The isomorphism with `Proj` lies over `k`**: under
`TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjIso`, the structure morphism of the
two-chart model to `Spec k` is the coefficient morphism of `Proj` of the section ring. -/
@[reassoc (attr := simp)]
theorem sectionRingProjIso_hom_over (hF : IsFunctionField k F) (z : Fˣ) :
    (sectionRingProjIso hF z).hom ≫ (twoChartModel hF z.ne_zero ↘ Spec (.of k)) =
      Proj.toSpecCoeff (sectionRingGrade (poles hF z)) := by
  rw [← Iso.eq_inv_comp]
  refine (isPushout hF z.ne_zero).hom_ext ?_ ?_
  · rw [ιFinite_over, ιFinite_sectionRingProjIso_inv_assoc, ← Category.assoc,
      sectionRingProjFiniteChartIso_inv_ι, Category.assoc, Proj.awayι_toSpecCoeff,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (sectionRingAwayOneEquiv hF z).toAlgHom.comp_algebraMap.symm
  · rw [ιInfinity_over, ιInfinity_sectionRingProjIso_inv_assoc, ← Category.assoc,
      sectionRingProjInfinityChartIso_inv_ι, Category.assoc, Proj.awayι_toSpecCoeff,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (sectionRingAwayGeneratorEquiv hF z).toAlgHom.comp_algebraMap.symm

end AlgebraicGeometry.twoChartModel

end TauCeti

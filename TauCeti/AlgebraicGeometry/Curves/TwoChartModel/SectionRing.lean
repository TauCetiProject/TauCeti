/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Basic
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.SectionRing

/-!
# The two-chart model is `Proj` of a section ring

Let `F / k` be an algebraic function field and let `z ∈ Fˣ`. The degree-one sections `1` and
`z` of the pole divisor `(z)_∞` define two standard opens in `Proj` of its section ring
`⨁ₙ L(n (z)_∞)`. This file identifies their homogeneous coordinate rings with the holomorphy
rings used to construct the two-chart model:

* localization at `X` gives the finite chart, where `z` is regular;
* localization at `z X` gives the infinity chart, where `z⁻¹` is regular.

Thus each standard open is canonically isomorphic to the corresponding affine chart of
`TauCeti.AlgebraicGeometry.twoChartModel`. The ring identifications are
`TauCeti.Divisor.sectionRingAwayOneEquiv` and `TauCeti.Divisor.sectionRingAwayGeneratorEquiv`;
this file composes them with Mathlib's `AlgebraicGeometry.Proj.basicOpenIsoSpec`.

The two standard opens cover `Proj`, and they meet in `D₊(X · z X)`, whose homogeneous
coordinate ring is the holomorphy ring of the places at which `z` is a unit
(`TauCeti.Divisor.sectionRingAwayOneMulGeneratorEquiv`). Under these identifications the
restrictions to the overlap are the inclusions of holomorphy rings along which the two-chart
model is glued. So the chart isomorphisms glue to an isomorphism of `Proj` of the section ring
with the two-chart model: **the scheme glued from the normalizations of `k[z]` and `k[z⁻¹]` in
`F` is `Proj ⨁ₙ L(n (z)_∞)`**. This is the comparison of the gluing construction of the
normalization of the projective line in `F` with its description as `Proj` of a graded ring of
sections, through which projective embeddings of the curve are built.

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
  isomorphisms are the canonical maps `D₊(f) ⟶ Spec A₍f₎` followed by the ring identifications;
  `TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjFiniteChartIso_inv` and
  `TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjInfinityChartIso_inv` describe their
  inverses.
* `TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjChart_cover`: the two standard opens
  cover `Proj`.
* `TauCeti.AlgebraicGeometry.twoChartModel.ιFinite_sectionRingProjIso_inv` and
  `TauCeti.AlgebraicGeometry.twoChartModel.ιInfinity_sectionRingProjIso_inv`: on each chart of
  the two-chart model, the inverse of the isomorphism with `Proj` is the inverse chart
  isomorphism followed by the inclusion of the standard open.
* `basicOpen_polesSectionOne_ι_sectionRingProjIso_hom` and
  `basicOpen_polesSectionGenerator_ι_sectionRingProjIso_hom`, in the namespace
  `TauCeti.AlgebraicGeometry.twoChartModel`: on each standard open, the isomorphism is the chart
  isomorphism followed by the inclusion of the chart.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Section II.2 and Section IV.3.
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

/-- The inverse of `TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjFiniteChartIso` is the
map induced by `TauCeti.Divisor.sectionRingAwayOneEquiv` followed by Mathlib's isomorphism
`Spec A₍X₎ ≅ D₊(X)`. -/
theorem sectionRingProjFiniteChartIso_inv (hF : IsFunctionField k F) (z : Fˣ) :
    (sectionRingProjFiniteChartIso hF z).inv =
      Spec.map (CommRingCat.ofHom (sectionRingAwayOneEquiv hF z).toRingHom) ≫
        (Proj.basicOpenIsoSpec (sectionRingGrade (poles hF z)) (polesSectionOne hF z)
          (monomialDegreeOne_mem_sectionRingGrade _) Nat.one_pos).inv := by
  rfl

/-- The inverse of `TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjInfinityChartIso` is
the map induced by `TauCeti.Divisor.sectionRingAwayGeneratorEquiv` followed by Mathlib's
isomorphism `Spec A₍z X₎ ≅ D₊(z X)`. -/
theorem sectionRingProjInfinityChartIso_inv (hF : IsFunctionField k F) (z : Fˣ) :
    (sectionRingProjInfinityChartIso hF z).inv =
      Spec.map (CommRingCat.ofHom (sectionRingAwayGeneratorEquiv hF z).toRingHom) ≫
        (Proj.basicOpenIsoSpec (sectionRingGrade (poles hF z)) (polesSectionGenerator hF z)
          (monomialDegreeOne_mem_sectionRingGrade _) Nat.one_pos).inv := by
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

/-! ### The two-chart model is `Proj` of the section ring -/

section Proj

variable (hF : IsFunctionField k F) (z : Fˣ)

/-- On the overlap, the chart `D₊(X)` restricts as the ring `𝒪_z` does: the restriction
`A₍X₎ → A₍X · z X₎` and the inclusion `𝒪_z → 𝒪_{z, z⁻¹}` correspond under the ring
identifications. -/
private theorem finiteChart_awayMap :
    CommRingCat.ofHom (sectionRingAwayOneEquiv hF z).toRingHom ≫
        CommRingCat.ofHom (finiteChartRestriction (k := k) (z : F)).toRingHom =
      CommRingCat.ofHom (awayMap (sectionRingGrade (poles hF z))
          (monomialDegreeOne_mem_sectionRingGrade (mem_riemannRochSpace_poles hF z)) rfl) ≫
        CommRingCat.ofHom (sectionRingAwayOneMulGeneratorEquiv hF z).toRingHom := by
  ext w
  simp [sectionRingAwayOneMulGeneratorEquiv_awayMap_one]

/-- On the overlap, the chart `D₊(z X)` restricts as the ring `𝒪_{z⁻¹}` does. -/
private theorem infinityChart_awayMap :
    CommRingCat.ofHom (sectionRingAwayGeneratorEquiv hF z).toRingHom ≫
        CommRingCat.ofHom (infinityChartRestriction (k := k) (z : F)).toRingHom =
      CommRingCat.ofHom (awayMap (sectionRingGrade (poles hF z))
          (monomialDegreeOne_mem_sectionRingGrade
            (one_mem_riemannRochSpace_iff.mpr (isEffective_poles hF z).zero_le))
          (mul_comm _ _)) ≫
        CommRingCat.ofHom (sectionRingAwayOneMulGeneratorEquiv hF z).toRingHom := by
  ext w
  simp [sectionRingAwayOneMulGeneratorEquiv_awayMap_generator]

/-- The inverse form of `finiteChart_awayMap`. -/
private theorem finiteChart_awayMap_symm :
    CommRingCat.ofHom (sectionRingAwayOneEquiv hF z).symm.toRingHom ≫
        CommRingCat.ofHom (awayMap (sectionRingGrade (poles hF z))
          (monomialDegreeOne_mem_sectionRingGrade (mem_riemannRochSpace_poles hF z)) rfl) =
      CommRingCat.ofHom (finiteChartRestriction (k := k) (z : F)).toRingHom ≫
        CommRingCat.ofHom (sectionRingAwayOneMulGeneratorEquiv hF z).symm.toRingHom := by
  refine CommRingCat.hom_ext (RingHom.ext fun u ↦ ?_)
  apply (sectionRingAwayOneMulGeneratorEquiv hF z).injective
  apply Subtype.ext
  simp [sectionRingAwayOneMulGeneratorEquiv_awayMap_one]

/-- The inverse form of `infinityChart_awayMap`. -/
private theorem infinityChart_awayMap_symm :
    CommRingCat.ofHom (sectionRingAwayGeneratorEquiv hF z).symm.toRingHom ≫
        CommRingCat.ofHom (awayMap (sectionRingGrade (poles hF z))
          (monomialDegreeOne_mem_sectionRingGrade
            (one_mem_riemannRochSpace_iff.mpr (isEffective_poles hF z).zero_le))
          (mul_comm _ _)) =
      CommRingCat.ofHom (infinityChartRestriction (k := k) (z : F)).toRingHom ≫
        CommRingCat.ofHom (sectionRingAwayOneMulGeneratorEquiv hF z).symm.toRingHom := by
  refine CommRingCat.hom_ext (RingHom.ext fun u ↦ ?_)
  apply (sectionRingAwayOneMulGeneratorEquiv hF z).injective
  apply Subtype.ext
  simp [sectionRingAwayOneMulGeneratorEquiv_awayMap_generator]

/-- The chart `D₊(X) ≅ Spec 𝒪_z`, read on `Spec A₍X₎`, followed by the inclusion of the finite
chart. -/
private noncomputable abbrev sectionRingProjFiniteChart :
    Spec (.of (Away (sectionRingGrade (poles hF z)) (polesSectionOne hF z))) ⟶
      twoChartModel hF z.ne_zero :=
  Spec.map (CommRingCat.ofHom (sectionRingAwayOneEquiv hF z).symm.toRingHom) ≫
    ιFinite hF z.ne_zero

/-- The chart `D₊(z X) ≅ Spec 𝒪_{z⁻¹}`, read on `Spec A₍z X₎`, followed by the inclusion of the
chart at infinity. -/
private noncomputable abbrev sectionRingProjInfinityChart :
    Spec (.of (Away (sectionRingGrade (poles hF z)) (polesSectionGenerator hF z))) ⟶
      twoChartModel hF z.ne_zero :=
  Spec.map (CommRingCat.ofHom (sectionRingAwayGeneratorEquiv hF z).symm.toRingHom) ≫
    ιInfinity hF z.ne_zero

/-- The two charts `D₊(X)` and `D₊(z X)` agree on their intersection `D₊(X · z X)`. -/
private theorem pullback_fst_sectionRingProjFiniteChart :
    Limits.pullback.fst
        (Proj.awayι _ (polesSectionOne hF z) (monomialDegreeOne_mem_sectionRingGrade _)
          Nat.one_pos)
        (Proj.awayι _ (polesSectionGenerator hF z) (monomialDegreeOne_mem_sectionRingGrade _)
          Nat.one_pos) ≫ sectionRingProjFiniteChart hF z =
      Limits.pullback.snd _ _ ≫ sectionRingProjInfinityChart hF z := by
  rw [← cancel_epi (Proj.pullbackAwayιIso _ (monomialDegreeOne_mem_sectionRingGrade _)
    Nat.one_pos (monomialDegreeOne_mem_sectionRingGrade _) Nat.one_pos rfl).inv,
    Proj.pullbackAwayιIso_inv_fst_assoc, Proj.pullbackAwayιIso_inv_snd_assoc,
    ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, finiteChart_awayMap_symm hF z,
    infinityChart_awayMap_symm hF z]
  simp only [Spec.map_comp, Category.assoc, condition hF z.ne_zero]

/-- The two charts `D₊(z X)` and `D₊(X)` agree on their intersection `D₊(X · z X)`. -/
private theorem pullback_fst_sectionRingProjInfinityChart :
    Limits.pullback.fst
        (Proj.awayι _ (polesSectionGenerator hF z) (monomialDegreeOne_mem_sectionRingGrade _)
          Nat.one_pos)
        (Proj.awayι _ (polesSectionOne hF z) (monomialDegreeOne_mem_sectionRingGrade _)
          Nat.one_pos) ≫ sectionRingProjInfinityChart hF z =
      Limits.pullback.snd _ _ ≫ sectionRingProjFiniteChart hF z := by
  rw [← cancel_epi (Proj.pullbackAwayιIso _ (monomialDegreeOne_mem_sectionRingGrade _)
    Nat.one_pos (monomialDegreeOne_mem_sectionRingGrade _) Nat.one_pos
    (mul_comm (polesSectionOne hF z) _)).inv,
    Proj.pullbackAwayιIso_inv_fst_assoc, Proj.pullbackAwayιIso_inv_snd_assoc,
    ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, finiteChart_awayMap_symm hF z,
    infinityChart_awayMap_symm hF z]
  simp only [Spec.map_comp, Category.assoc, condition hF z.ne_zero]

/-- The cover of `Proj` of the section ring of `(z)_∞` by its standard opens `D₊(X)` (for
`true`) and `D₊(z X)` (for `false`). -/
private noncomputable def sectionRingProjOpenCover :
    (Proj (sectionRingGrade (poles hF z))).OpenCover :=
  Scheme.Cover.mkOfCovers Bool
    (fun b ↦ b.rec (Spec (.of (Away (sectionRingGrade (poles hF z)) (polesSectionGenerator hF z))))
      (Spec (.of (Away (sectionRingGrade (poles hF z)) (polesSectionOne hF z)))))
    (fun b ↦ match b with
      | false => Proj.awayι _ (polesSectionGenerator hF z)
          (monomialDegreeOne_mem_sectionRingGrade _) Nat.one_pos
      | true => Proj.awayι _ (polesSectionOne hF z)
          (monomialDegreeOne_mem_sectionRingGrade _) Nat.one_pos)
    (fun p ↦ by
      have hp := (sectionRingProjChart_cover hF z).ge (Set.mem_univ p)
      rcases TopologicalSpace.Opens.mem_sup.mp hp with h | h
      · rw [← Proj.opensRange_awayι _ _ (monomialDegreeOne_mem_sectionRingGrade _)
          Nat.one_pos] at h
        obtain ⟨q, rfl⟩ := h
        exact ⟨true, q, rfl⟩
      · rw [← Proj.opensRange_awayι _ _ (monomialDegreeOne_mem_sectionRingGrade _)
          Nat.one_pos] at h
        obtain ⟨q, rfl⟩ := h
        exact ⟨false, q, rfl⟩)
    (fun b ↦ by cases b <;> infer_instance)

/-- The morphism from `Proj` of the section ring to the two-chart model, glued from the chart
identifications `D₊(X) ≅ Spec 𝒪_z` and `D₊(z X) ≅ Spec 𝒪_{z⁻¹}`. -/
private noncomputable def fromSectionRingProj :
    Proj (sectionRingGrade (poles hF z)) ⟶ twoChartModel hF z.ne_zero :=
  (sectionRingProjOpenCover hF z).glueMorphisms
    (fun b ↦ match b with
      | false => sectionRingProjInfinityChart hF z
      | true => sectionRingProjFiniteChart hF z)
    (by
      rintro (_ | _) (_ | _)
      · exact congr($(Limits.fst_eq_snd_of_mono_eq (Proj.awayι _ (polesSectionGenerator hF z)
          (monomialDegreeOne_mem_sectionRingGrade _) Nat.one_pos)) ≫ _)
      · exact pullback_fst_sectionRingProjInfinityChart hF z
      · exact pullback_fst_sectionRingProjFiniteChart hF z
      · exact congr($(Limits.fst_eq_snd_of_mono_eq (Proj.awayι _ (polesSectionOne hF z)
          (monomialDegreeOne_mem_sectionRingGrade _) Nat.one_pos)) ≫ _))

/-- On `Spec A₍X₎`, the chart isomorphism of `D₊(X)` with `Spec 𝒪_z` is `Spec` of the
identification `A₍X₎ ≃ 𝒪_z`. -/
@[reassoc]
private theorem basicOpenIsoSpec_inv_sectionRingProjFiniteChartIso_hom :
    (Proj.basicOpenIsoSpec _ (polesSectionOne hF z) (monomialDegreeOne_mem_sectionRingGrade _)
        Nat.one_pos).inv ≫ (sectionRingProjFiniteChartIso hF z).hom =
      Spec.map (CommRingCat.ofHom (sectionRingAwayOneEquiv hF z).symm.toRingHom) := by
  rw [sectionRingProjFiniteChartIso_hom, Iso.inv_hom_id_assoc]

/-- On `Spec A₍z X₎`, the chart isomorphism of `D₊(z X)` with `Spec 𝒪_{z⁻¹}` is `Spec` of the
identification `A₍z X₎ ≃ 𝒪_{z⁻¹}`. -/
@[reassoc]
private theorem basicOpenIsoSpec_inv_sectionRingProjInfinityChartIso_hom :
    (Proj.basicOpenIsoSpec _ (polesSectionGenerator hF z)
        (monomialDegreeOne_mem_sectionRingGrade _) Nat.one_pos).inv ≫
        (sectionRingProjInfinityChartIso hF z).hom =
      Spec.map (CommRingCat.ofHom (sectionRingAwayGeneratorEquiv hF z).symm.toRingHom) := by
  rw [sectionRingProjInfinityChartIso_hom, Iso.inv_hom_id_assoc]

/-- The morphism from the two-chart model to `Proj` of the section ring, glued from the inverse
chart identifications `Spec 𝒪_z ≅ D₊(X)` and `Spec 𝒪_{z⁻¹} ≅ D₊(z X)`. -/
private noncomputable def toSectionRingProj :
    twoChartModel hF z.ne_zero ⟶ Proj (sectionRingGrade (poles hF z)) :=
  (isPushout hF z.ne_zero).desc
    ((sectionRingProjFiniteChartIso hF z).inv ≫ (Proj.basicOpen _ (polesSectionOne hF z)).ι)
    ((sectionRingProjInfinityChartIso hF z).inv ≫
      (Proj.basicOpen _ (polesSectionGenerator hF z)).ι)
    (by
      rw [sectionRingProjFiniteChartIso_inv, sectionRingProjInfinityChartIso_inv,
        Category.assoc, Category.assoc, Proj.basicOpenIsoSpec_inv_ι, Proj.basicOpenIsoSpec_inv_ι,
        ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, finiteChart_awayMap hF z,
        infinityChart_awayMap hF z]
      simp only [Spec.map_comp, Category.assoc, Proj.SpecMap_awayMap_awayι])

/-- `fromSectionRingProj` restricts on `D₊(X)` to the chart identification with `Spec 𝒪_z`. -/
@[reassoc]
private theorem awayι_one_fromSectionRingProj :
    Proj.awayι _ (polesSectionOne hF z) (monomialDegreeOne_mem_sectionRingGrade _) Nat.one_pos ≫
      fromSectionRingProj hF z = sectionRingProjFiniteChart hF z :=
  (sectionRingProjOpenCover hF z).ι_glueMorphisms _ _ true

/-- `fromSectionRingProj` restricts on `D₊(z X)` to the chart identification with
`Spec 𝒪_{z⁻¹}`. -/
@[reassoc]
private theorem awayι_generator_fromSectionRingProj :
    Proj.awayι _ (polesSectionGenerator hF z) (monomialDegreeOne_mem_sectionRingGrade _)
        Nat.one_pos ≫ fromSectionRingProj hF z = sectionRingProjInfinityChart hF z :=
  (sectionRingProjOpenCover hF z).ι_glueMorphisms _ _ false

/-- `fromSectionRingProj` restricts on the open `D₊(X)` to the chart isomorphism with
`Spec 𝒪_z`. -/
private theorem basicOpen_polesSectionOne_ι_fromSectionRingProj :
    (Proj.basicOpen _ (polesSectionOne hF z)).ι ≫ fromSectionRingProj hF z =
      (sectionRingProjFiniteChartIso hF z).hom ≫ ιFinite hF z.ne_zero := by
  rw [← cancel_epi (Proj.basicOpenIsoSpec _ (polesSectionOne hF z)
    (monomialDegreeOne_mem_sectionRingGrade _) Nat.one_pos).inv,
    Proj.basicOpenIsoSpec_inv_ι_assoc, awayι_one_fromSectionRingProj,
    basicOpenIsoSpec_inv_sectionRingProjFiniteChartIso_hom_assoc]

/-- `fromSectionRingProj` restricts on the open `D₊(z X)` to the chart isomorphism with
`Spec 𝒪_{z⁻¹}`. -/
private theorem basicOpen_polesSectionGenerator_ι_fromSectionRingProj :
    (Proj.basicOpen _ (polesSectionGenerator hF z)).ι ≫ fromSectionRingProj hF z =
      (sectionRingProjInfinityChartIso hF z).hom ≫ ιInfinity hF z.ne_zero := by
  rw [← cancel_epi (Proj.basicOpenIsoSpec _ (polesSectionGenerator hF z)
    (monomialDegreeOne_mem_sectionRingGrade _) Nat.one_pos).inv,
    Proj.basicOpenIsoSpec_inv_ι_assoc, awayι_generator_fromSectionRingProj,
    basicOpenIsoSpec_inv_sectionRingProjInfinityChartIso_hom_assoc]

/-- `toSectionRingProj` is a left inverse of `fromSectionRingProj` on `D₊(X)`. -/
private theorem awayι_one_fromSectionRingProj_toSectionRingProj :
    Proj.awayι _ (polesSectionOne hF z) (monomialDegreeOne_mem_sectionRingGrade _) Nat.one_pos ≫
        fromSectionRingProj hF z ≫ toSectionRingProj hF z =
      Proj.awayι _ (polesSectionOne hF z) (monomialDegreeOne_mem_sectionRingGrade _)
        Nat.one_pos ≫ 𝟙 _ := by
  rw [awayι_one_fromSectionRingProj_assoc, toSectionRingProj, (isPushout hF z.ne_zero).inl_desc,
    ← basicOpenIsoSpec_inv_sectionRingProjFiniteChartIso_hom, Category.assoc,
    Iso.hom_inv_id_assoc, Proj.basicOpenIsoSpec_inv_ι, Category.comp_id]

/-- `toSectionRingProj` is a left inverse of `fromSectionRingProj` on `D₊(z X)`. -/
private theorem awayι_generator_fromSectionRingProj_toSectionRingProj :
    Proj.awayι _ (polesSectionGenerator hF z) (monomialDegreeOne_mem_sectionRingGrade _)
        Nat.one_pos ≫ fromSectionRingProj hF z ≫ toSectionRingProj hF z =
      Proj.awayι _ (polesSectionGenerator hF z) (monomialDegreeOne_mem_sectionRingGrade _)
        Nat.one_pos ≫ 𝟙 _ := by
  rw [awayι_generator_fromSectionRingProj_assoc, toSectionRingProj,
    (isPushout hF z.ne_zero).inr_desc,
    ← basicOpenIsoSpec_inv_sectionRingProjInfinityChartIso_hom, Category.assoc,
    Iso.hom_inv_id_assoc, Proj.basicOpenIsoSpec_inv_ι, Category.comp_id]

/-- **The two-chart model of `F` built from `z` is `Proj` of the section ring of `(z)_∞`**:
the isomorphism of `Proj ⨁ₙ L(n (z)_∞)` with the scheme glued from `Spec 𝒪_z` and
`Spec 𝒪_{z⁻¹}`. It restricts on the standard opens `D₊(X)` and `D₊(z X)` to the chart
isomorphisms `sectionRingProjFiniteChartIso` and `sectionRingProjInfinityChartIso`
(`basicOpen_polesSectionOne_ι_sectionRingProjIso_hom`,
`basicOpen_polesSectionGenerator_ι_sectionRingProjIso_hom`). -/
noncomputable def sectionRingProjIso :
    Proj (sectionRingGrade (poles hF z)) ≅ twoChartModel hF z.ne_zero where
  hom := fromSectionRingProj hF z
  inv := toSectionRingProj hF z
  hom_inv_id := (sectionRingProjOpenCover hF z).hom_ext _ _ fun b ↦ by
    cases b
    exacts [awayι_generator_fromSectionRingProj_toSectionRingProj hF z,
      awayι_one_fromSectionRingProj_toSectionRingProj hF z]
  inv_hom_id := by
    refine (isPushout hF z.ne_zero).hom_ext ?_ ?_
    · rw [toSectionRingProj, (isPushout hF z.ne_zero).inl_desc_assoc, Category.assoc,
        basicOpen_polesSectionOne_ι_fromSectionRingProj, Iso.inv_hom_id_assoc, Category.comp_id]
    · rw [toSectionRingProj, (isPushout hF z.ne_zero).inr_desc_assoc, Category.assoc,
        basicOpen_polesSectionGenerator_ι_fromSectionRingProj, Iso.inv_hom_id_assoc,
        Category.comp_id]

/-- On the finite chart, the inverse of `sectionRingProjIso` is the chart identification
`Spec 𝒪_z ≅ D₊(X)` followed by the inclusion of `D₊(X)` into `Proj`. -/
@[reassoc (attr := simp)]
theorem ιFinite_sectionRingProjIso_inv :
    ιFinite hF z.ne_zero ≫ (sectionRingProjIso hF z).inv =
      (sectionRingProjFiniteChartIso hF z).inv ≫
        (Proj.basicOpen _ (polesSectionOne hF z)).ι :=
  (isPushout hF z.ne_zero).inl_desc _ _ _

/-- On the chart at infinity, the inverse of `sectionRingProjIso` is the chart identification
`Spec 𝒪_{z⁻¹} ≅ D₊(z X)` followed by the inclusion of `D₊(z X)` into `Proj`. -/
@[reassoc (attr := simp)]
theorem ιInfinity_sectionRingProjIso_inv :
    ιInfinity hF z.ne_zero ≫ (sectionRingProjIso hF z).inv =
      (sectionRingProjInfinityChartIso hF z).inv ≫
        (Proj.basicOpen _ (polesSectionGenerator hF z)).ι :=
  (isPushout hF z.ne_zero).inr_desc _ _ _

/-- On the standard open `D₊(X)`, the isomorphism `sectionRingProjIso` is the chart isomorphism
`D₊(X) ≅ Spec 𝒪_z` followed by the inclusion of the finite chart. -/
@[reassoc (attr := simp)]
theorem basicOpen_polesSectionOne_ι_sectionRingProjIso_hom :
    (Proj.basicOpen _ (polesSectionOne hF z)).ι ≫ (sectionRingProjIso hF z).hom =
      (sectionRingProjFiniteChartIso hF z).hom ≫ ιFinite hF z.ne_zero :=
  basicOpen_polesSectionOne_ι_fromSectionRingProj hF z

/-- On the standard open `D₊(z X)`, the isomorphism `sectionRingProjIso` is the chart isomorphism
`D₊(z X) ≅ Spec 𝒪_{z⁻¹}` followed by the inclusion of the chart at infinity. -/
@[reassoc (attr := simp)]
theorem basicOpen_polesSectionGenerator_ι_sectionRingProjIso_hom :
    (Proj.basicOpen _ (polesSectionGenerator hF z)).ι ≫ (sectionRingProjIso hF z).hom =
      (sectionRingProjInfinityChartIso hF z).hom ≫ ιInfinity hF z.ne_zero :=
  basicOpen_polesSectionGenerator_ι_fromSectionRingProj hF z

end Proj

end AlgebraicGeometry.twoChartModel

end TauCeti

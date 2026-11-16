/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Adjunction
public import TauCeti.Algebra.Homology.ModuleCat.KFlat.DerivedTensor
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import TauCeti.Algebra.Category.ModuleCat.Monoidal.ChangeOfRings
import TauCeti.Algebra.Homology.Bifunctor.TwoTermSupport
import TauCeti.Algebra.Homology.Monoidal.Braiding
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# Derived extension of scalars and its adjunction with restriction

For a homomorphism `f : R →+* S` of commutative rings, extension of scalars followed by
restriction of scalars is naturally isomorphic to tensoring with `S` viewed as an `R`-module.
Since restriction of scalars is exact and reflects isomorphisms, termwise extension of scalars
sends every quasi-isomorphism between K-flat complexes of `R`-modules to a quasi-isomorphism of
complexes of `S`-modules (`CochainComplex.quasiIso_mapHomologicalComplex_extendScalars_of_isKFlat`).

Using the K-flat left derivability structure on `CochainComplex (ModuleCat R) ℤ`, it follows that
termwise extension of scalars admits a left derived functor
`− ⊗^L_R S : DerivedCategory (ModuleCat R) ⥤ DerivedCategory (ModuleCat S)`
(`CochainComplex.hasLeftDerivedFunctor_extendScalars`), whose comparison map is an isomorphism on
every K-flat complex (`CochainComplex.isIso_derivedExtendScalarsCounit_of_isKFlat`) and in
particular on every bounded-above complex of flat `R`-modules. Moreover, any left derived functor
of extension of scalars is left adjoint to the exact restriction-of-scalars functor
`(ModuleCat.restrictScalars f).mapDerivedCategory` (`ModuleCat.derivedExtendRestrictScalarsAdj`).

## Main results

* `CochainComplex.quasiIso_id_tensorHom_of_isKFlat`: tensoring an arbitrary complex on the left
  with a quasi-isomorphism between K-flat complexes yields a quasi-isomorphism.
* `CochainComplex.quasiIso_mapHomologicalComplex_extendScalars_of_isKFlat`: termwise extension of
  scalars preserves quasi-isomorphisms between K-flat complexes.
* `CochainComplex.hasLeftDerivedFunctor_extendScalars`: termwise extension of scalars admits a left
  derived functor on the unbounded derived category.
* `CochainComplex.isIso_derivedExtendScalarsCounit_of_isKFlat`,
  `CochainComplex.isIso_derivedExtendScalarsCounit_of_boundedAbove_flat`: derived extension of
  scalars is computed by termwise extension of scalars on K-flat complexes and on bounded-above
  complexes of flat modules.
* `ModuleCat.derivedExtendRestrictScalarsAdj`: any left derived functor of extension of scalars is
  left adjoint to restriction of scalars on derived categories, with explicit unit and counit
  compatibility laws on complex models.

## References

* The Stacks Project, More on Algebra, Section 15.61, Lemmas 15.61.1 and 15.61.3 (Tags 06Y6 and
  0GMT), with Lemmas 15.60.10 and 15.60.12 (Tags 06Y4 and 064L).
* G. Maltsiniotis, *Le théorème de Quillen, d'adjonction des foncteurs dérivés, revisité*,
  C. R. Math. Acad. Sci. Paris 344 (2007), 549–552.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

universe u w w'

namespace CochainComplex

variable {R S : Type u} [CommRing R] [CommRing S]

/-- A quasi-isomorphism between K-flat complexes of `R`-modules stays a quasi-isomorphism after
tensoring on the left with an arbitrary, possibly unbounded, complex of `R`-modules. -/
instance quasiIso_id_tensorHom_of_isKFlat
    (A : CochainComplex (ModuleCat.{u} R) ℤ)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} [K.IsKFlat] [L.IsKFlat]
    (g : K ⟶ L) [QuasiIso g] :
    QuasiIso (HomologicalComplex.tensorHom (𝟙 A) g) := by
  rw [HomologicalComplex.tensorHom, ← HomologicalComplex.whiskerLeft_eq_mapBifunctorMap]
  have : QuasiIso (g ▷ A) := by
    rw [HomologicalComplex.whiskerRight_eq_mapBifunctorMap]
    exact inferInstanceAs (QuasiIso (HomologicalComplex.tensorHom g (𝟙 A)))
  exact quasiIso_of_arrow_mk_iso (g ▷ A) (A ◁ g)
    (Arrow.isoMk (β_ A K).symm (β_ A L).symm (by
      simp only [Iso.symm_hom, Arrow.mk_hom, Iso.inv_comp_eq,
        ← BraidedCategory.braiding_naturality_right_assoc, Iso.hom_inv_id, Category.comp_id]))

private def extendScalarsCompRestrictScalarsIso (f : R →+* S) :
    ModuleCat.extendScalars.{u, u, u} f ⋙ ModuleCat.restrictScalars.{u} f ≅
      MonoidalCategory.tensorLeft ((ModuleCat.restrictScalars f).obj (𝟙_ (ModuleCat.{u} S))) :=
  Functor.isoWhiskerRight (Functor.rightUnitor (ModuleCat.extendScalars.{u, u, u} f)).symm
      (ModuleCat.restrictScalars.{u} f) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (ModuleCat.extendScalars.{u, u, u} f)
        (NatIso.ofComponents (F := 𝟭 (ModuleCat.{u} S))
          (G := MonoidalCategory.tensorLeft (𝟙_ (ModuleCat.{u} S)))
          (fun X ↦ (λ_ X).symm) (fun g ↦ by simp)))
      (ModuleCat.restrictScalars.{u} f) ≪≫
    Functor.associator _ _ _ ≪≫
    ModuleCat.extendScalarsCompTensorLeftIso f (𝟙_ (ModuleCat.{u} S))

/-- Termwise extension of scalars preserves quasi-isomorphisms between K-flat complexes of
`R`-modules. -/
instance quasiIso_mapHomologicalComplex_extendScalars_of_isKFlat (f : R →+* S)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} [K.IsKFlat] [L.IsKFlat]
    (g : K ⟶ L) [QuasiIso g] :
    QuasiIso (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)).map g) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (ModuleCat.restrictScalars.{u} f)]
  let S_R : ModuleCat.{u} R := (ModuleCat.restrictScalars f).obj (𝟙_ (ModuleCat.{u} S))
  let e : (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ) ⋙
        (ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (.up ℤ) ≅
      (MonoidalCategory.curriedTensor (ModuleCat.{u} R)).mapBifunctorLeft (.up ℤ) (.up ℤ)
        ((single (ModuleCat.{u} R) (.up ℤ) 0).obj S_R) :=
    Functor.mapHomologicalComplexCompIso (extendScalarsCompRestrictScalarsIso f) (.up ℤ) ≪≫
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).mapBifunctorSingleRowZeroNatIso S_R).symm
  have hsingle : QuasiIso
      (((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).mapBifunctorLeft (.up ℤ) (.up ℤ)
        ((single (ModuleCat.{u} R) (.up ℤ) 0).obj S_R)).map g) :=
    inferInstanceAs (QuasiIso
      (HomologicalComplex.tensorHom (𝟙 ((single (ModuleCat.{u} R) (.up ℤ) 0).obj S_R)) g))
  exact quasiIso_of_arrow_mk_iso
    (((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).mapBifunctorLeft (.up ℤ) (.up ℤ)
      ((single (ModuleCat.{u} R) (.up ℤ) 0).obj S_R)).map g)
    _ (Arrow.isoMk (e.app K).symm (e.app L).symm (e.inv.naturality g).symm)

section LeftDerived

variable (f : R →+* S) [HasDerivedCategory.{w'} (ModuleCat.{u} S)]

/-- The K-flat left derivability structure on `CochainComplex (ModuleCat R) ℤ` derives termwise
extension of scalars along `f : R →+* S`. -/
theorem kFlatLocalizerMorphism_derives_extendScalars :
    (kFlatLocalizerMorphism (ModuleCat.{u} R)).Derives
      (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)) ⋙
        DerivedCategory.Q (C := ModuleCat.{u} S)) := by
  intro K L g hg
  have : QuasiIso g.hom := hg
  have : QuasiIso
      (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)).map g.hom) :=
    quasiIso_mapHomologicalComplex_extendScalars_of_isKFlat f g.hom
  dsimp only [Functor.comp_map, kFlatLocalizerMorphism_functor, ObjectProperty.ι_map]
  infer_instance

/-- **Derived extension of scalars exists.** For any homomorphism `f : R →+* S` of commutative
rings, termwise extension of scalars followed by `DerivedCategory.Q` admits a left derived functor
with respect to quasi-isomorphisms of complexes of `R`-modules. -/
instance hasLeftDerivedFunctor_extendScalars :
    (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)) ⋙
      DerivedCategory.Q (C := ModuleCat.{u} S)).HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)) := by
  have := (kFlatLocalizerMorphism_derives_extendScalars f).hasPointwiseLeftDerivedFunctor
  exact Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor _ _

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]
variable (G : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
  (α : DerivedCategory.Q ⋙ G ⟶
    ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q)
  [G.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))]

/-- **K-flat model computation for derived extension of scalars.** If `P` is a K-flat complex of
`R`-modules, the comparison map `G (Q P) ⟶ Q (S ⊗_R P)` of any left derived functor of extension
of scalars is an isomorphism. -/
theorem isIso_derivedExtendScalarsCounit_of_isKFlat
    (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    IsIso (α.app P) :=
  (kFlatLocalizerMorphism_derives_extendScalars f).isIso' α ⟨P, ‹P.IsKFlat›⟩

/-- **Bounded-above flat model computation for derived extension of scalars.** If `P` is a
bounded-above complex of flat `R`-modules, the comparison map `G (Q P) ⟶ Q (S ⊗_R P)` is an
isomorphism. -/
theorem isIso_derivedExtendScalarsCounit_of_boundedAbove_flat
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ) [P.IsStrictlyLE b]
    [∀ i, Module.Flat R (P.X i)] :
    IsIso (α.app P) := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_of_univLE.{0, 0, u, u} _
  have : P.IsKFlat := isKFlat_of_boundedAbove_flat P b
  exact isIso_derivedExtendScalarsCounit_of_isKFlat f G α P

end LeftDerived

end CochainComplex

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w'} (ModuleCat.{u} S)]
  (G : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
  (α : DerivedCategory.Q ⋙ G ⟶
    ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q)
  [G.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))]

private lemma isLeftDerivedFunctor_extendScalars_comp_restrictScalars :
    (G ⋙ (ModuleCat.restrictScalars.{u} f).mapDerivedCategory).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight α (ModuleCat.restrictScalars.{u} f).mapDerivedCategory)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)) := by
  have hder : (CochainComplex.kFlatLocalizerMorphism (ModuleCat.{u} R)).Derives
      ((((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)) ⋙
          DerivedCategory.Q (C := ModuleCat.{u} S)) ⋙
        (ModuleCat.restrictScalars.{u} f).mapDerivedCategory) := by
    intro K L g hg
    have : IsIso ((((CochainComplex.kFlatLocalizerMorphism (ModuleCat.{u} R)).functor ⋙
        (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)) ⋙
          DerivedCategory.Q (C := ModuleCat.{u} S))).map g)) :=
      CochainComplex.kFlatLocalizerMorphism_derives_extendScalars f g hg
    dsimp only [Functor.comp_map] at this ⊢
    infer_instance
  refine hder.isLeftDerivedFunctor_of_isIso _ (fun P ↦ ?_)
  have : IsIso (α.app P.obj) :=
    CochainComplex.isIso_derivedExtendScalarsCounit_of_isKFlat f G α P.obj
  dsimp only [NatTrans.comp_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    CochainComplex.kFlatLocalizerMorphism_functor, ObjectProperty.ι_obj]
  infer_instance

private lemma isRightDerivedFunctor_restrictScalars :
    (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.IsRightDerivedFunctor
      (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv
      (HomologicalComplex.quasiIso (ModuleCat.{u} S) (.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _
    (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors

private lemma isRightDerivedFunctor_restrictScalars_comp_extendScalars :
    ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory ⋙ G).IsRightDerivedFunctor
      (Functor.whiskerRight (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv G ≫
        (Functor.associator _ _ _).hom)
      (HomologicalComplex.quasiIso (ModuleCat.{u} S) (.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors G)

/-- **Derived extension–restriction adjunction.** For any homomorphism `f : R →+* S` of
commutative rings, any left derived functor
`G : DerivedCategory (ModuleCat R) ⥤ DerivedCategory (ModuleCat S)` of termwise extension of
scalars is left adjoint to the exact restriction-of-scalars functor
`(ModuleCat.restrictScalars f).mapDerivedCategory`. -/
def derivedExtendRestrictScalarsAdj :
    G ⊣ (ModuleCat.restrictScalars.{u} f).mapDerivedCategory :=
  haveI := isRightDerivedFunctor_restrictScalars f
  haveI := isLeftDerivedFunctor_extendScalars_comp_restrictScalars f G α
  haveI := isRightDerivedFunctor_restrictScalars_comp_extendScalars f G
  ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex (.up ℤ)).derived
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
    (HomologicalComplex.quasiIso (ModuleCat.{u} S) (.up ℤ))
    α (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv

/-- Compatibility of the unit of `derivedExtendRestrictScalarsAdj` with the complex-level unit on
objects in the image of `DerivedCategory.Q`. -/
@[reassoc (attr := simp)]
lemma derivedExtendRestrictScalarsAdj_unit_app_Q (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedExtendRestrictScalarsAdj f G α).unit.app (DerivedCategory.Q.obj K) ≫
        (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.map (α.app K) =
      DerivedCategory.Q.map
          (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
            (.up ℤ)).unit.app K) ≫
        (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app
          (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)).obj K) := by
  have := isRightDerivedFunctor_restrictScalars f
  have := isLeftDerivedFunctor_extendScalars_comp_restrictScalars f G α
  have := isRightDerivedFunctor_restrictScalars_comp_extendScalars f G
  simp [derivedExtendRestrictScalarsAdj]

/-- Compatibility of the counit of `derivedExtendRestrictScalarsAdj` with the complex-level counit
on objects in the image of `DerivedCategory.Q`. -/
@[reassoc (attr := simp)]
lemma derivedExtendRestrictScalarsAdj_counit_app_Q (L : CochainComplex (ModuleCat.{u} S) ℤ) :
    G.map ((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app L) ≫
        (derivedExtendRestrictScalarsAdj f G α).counit.app (DerivedCategory.Q.obj L) =
      α.app (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (.up ℤ)).obj L) ≫
        DerivedCategory.Q.map
          (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
            (.up ℤ)).counit.app L) := by
  have := isRightDerivedFunctor_restrictScalars f
  have := isLeftDerivedFunctor_extendScalars_comp_restrictScalars f G α
  have := isRightDerivedFunctor_restrictScalars_comp_extendScalars f G
  simp [derivedExtendRestrictScalarsAdj]

end ModuleCat

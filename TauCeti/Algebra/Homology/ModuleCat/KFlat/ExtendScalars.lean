/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Homology.Adjunction
public import TauCeti.Algebra.Homology.ModuleCat.KFlat.DerivedTensor
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import TauCeti.Algebra.Category.ModuleCat.Monoidal.ChangeOfRings
import TauCeti.Algebra.Homology.Bifunctor.TwoTermSupport

/-!
# Derived extension of scalars and its adjunction with restriction of scalars

For a morphism `f : R →+* S` of commutative rings, restricting scalars after extending scalars
identifies `ModuleCat.extendScalars f ⋙ ModuleCat.restrictScalars f` with tensoring over `R` by
`S` (via `ModuleCat.extendScalarsCompTensorLeftIso`). Since `ModuleCat.restrictScalars f` is exact
and reflects isomorphisms, and tensoring a quasi-isomorphism between K-flat complexes on the left
with any complex (in particular `S[0]`) preserves quasi-isomorphisms
(`CochainComplex.quasiIso_id_tensorHom_of_isKFlat`), termwise extension of scalars preserves
quasi-isomorphisms between K-flat complexes
(`CochainComplex.quasiIso_extendScalars_map_of_isKFlat`).

Combined with the K-flat left derivability structure on `CochainComplex (ModuleCat.{u} R) ℤ`, this
proves that termwise extension of scalars followed by localization admits a pointwise left derived
functor `CochainComplex.hasLeftDerivedFunctor_extendScalars`, computed on any K-flat complex (and
in particular on any bounded-above complex of flat `R`-modules) by ordinary termwise extension of
scalars.

Lifting the module adjunction `ModuleCat.extendRestrictScalarsAdj f` degreewise to cochain
complexes via `CategoryTheory.Adjunction.mapHomologicalComplex` and applying
`CategoryTheory.Adjunction.derived` yields the derived extension–restriction adjunction
`CochainComplex.derivedExtendRestrictScalarsAdj`, exhibiting every left derived functor `G` of
termwise extension of scalars as left adjoint to `(ModuleCat.restrictScalars f).mapDerivedCategory`.

## Main results

* `CochainComplex.quasiIso_extendScalars_map_of_isKFlat`: termwise extension of scalars preserves
  quasi-isomorphisms between K-flat complexes.
* `CochainComplex.hasLeftDerivedFunctor_extendScalars`: termwise extension of scalars followed by
  `DerivedCategory.Q` admits a left derived functor on unbounded complexes.
* `CochainComplex.isIso_derivedExtendScalarsCounit_of_isKFlat` and
  `CochainComplex.isIso_derivedExtendScalarsCounit_of_boundedAbove_flat`: any left derived
  extension-of-scalars functor is computed by termwise scalar extension on K-flat complexes and
  on bounded-above complexes of flat modules.
* `CochainComplex.derivedExtendRestrictScalarsAdj`: every left derived functor of termwise
  extension of scalars is left adjoint to `(ModuleCat.restrictScalars f).mapDerivedCategory`.

## References

* The Stacks Project, More on Algebra, Section 15.61, Lemmas 15.61.1 and 15.61.3
  (Tags 06Y6, 0GMT) and Lemma 15.60.12 (Tag 064L).
* G. Maltsiniotis, *Le théorème de Quillen, d'adjonction des foncteurs dérivés, revisité*,
  C. R. Math. Acad. Sci. Paris 344 (2007), 549–552.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open scoped MonoidalCategory

namespace CochainComplex

universe u w w'

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Extending scalars along `f : R →+* S` and then restricting back to `R` is naturally isomorphic
to tensoring on the left with `S` viewed as an `R`-module. -/
private def extendScalarsCompRestrictScalarsIso (f : R →+* S) :
    ModuleCat.extendScalars.{u, u, u} f ⋙ ModuleCat.restrictScalars.{u} f ≅
      tensorLeft ((ModuleCat.restrictScalars.{u} f).obj (𝟙_ (ModuleCat.{u} S))) :=
  Functor.isoWhiskerLeft (ModuleCat.extendScalars.{u, u, u} f)
      (Functor.leftUnitor (ModuleCat.restrictScalars.{u} f)).symm ≪≫
    Functor.isoWhiskerLeft (ModuleCat.extendScalars.{u, u, u} f)
      (Functor.isoWhiskerRight (leftUnitorNatIso (ModuleCat.{u} S)).symm
        (ModuleCat.restrictScalars.{u} f)) ≪≫
    ModuleCat.extendScalarsCompTensorLeftIso f (𝟙_ (ModuleCat.{u} S))

/-- Termwise extension of scalars along `f : R →+* S` preserves quasi-isomorphisms between
K-flat cochain complexes of `R`-modules. -/
instance quasiIso_extendScalars_map_of_isKFlat (f : R →+* S)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} [K.IsKFlat] [L.IsKFlat]
    (φ : K ⟶ L) [QuasiIso φ] :
    QuasiIso (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)).map φ) := by
  let M : ModuleCat.{u} R := (ModuleCat.restrictScalars.{u} f).obj (𝟙_ (ModuleCat.{u} S))
  let A : CochainComplex (ModuleCat.{u} R) ℤ := (single (ModuleCat.{u} R) (.up ℤ) 0).obj M
  let e : (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ) ⋙
      (ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (.up ℤ) ≅
      (curriedTensor (ModuleCat.{u} R)).mapBifunctorLeft (.up ℤ) (.up ℤ) A :=
    Functor.mapHomologicalComplexCompIso (extendScalarsCompRestrictScalarsIso f) (.up ℤ) ≪≫
      ((curriedTensor (ModuleCat.{u} R)).mapBifunctorSingleRowZeroNatIso M).symm
  rw [← quasiIso_map_iff_of_preservesHomology _ (ModuleCat.restrictScalars.{u} f)]
  have hA :
      QuasiIso (((curriedTensor (ModuleCat.{u} R)).mapBifunctorLeft (.up ℤ) (.up ℤ) A).map φ) :=
    quasiIso_id_tensorHom_of_isKFlat A φ
  exact quasiIso_of_arrow_mk_iso _ _
    (Arrow.isoMk (e.symm.app K) (e.symm.app L) (e.inv.naturality φ).symm)

/-- The K-flat left derivability structure derives termwise extension of scalars followed by
localization to `DerivedCategory (ModuleCat.{u} S)`. -/
lemma derives_extendScalars (f : R →+* S) [HasDerivedCategory.{w} (ModuleCat.{u} S)] :
    (kFlatLocalizerMorphism (ModuleCat.{u} R)).Derives
      ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q) := by
  intro K L φ hφ
  have : QuasiIso φ.hom := (mem_quasiIso_iff _).1 hφ
  exact Localization.inverts DerivedCategory.Q (quasiIso (ModuleCat.{u} S) (.up ℤ)) _
    ((mem_quasiIso_iff _).2 (quasiIso_extendScalars_map_of_isKFlat f φ.hom))

/-- Termwise extension of scalars followed by localization admits a pointwise left derived functor
with respect to quasi-isomorphisms. -/
instance hasPointwiseLeftDerivedFunctor_extendScalars (f : R →+* S)
    [HasDerivedCategory.{w} (ModuleCat.{u} S)] :
    ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q).HasPointwiseLeftDerivedFunctor
      (quasiIso (ModuleCat.{u} R) (.up ℤ)) :=
  (derives_extendScalars f).hasPointwiseLeftDerivedFunctor

/-- **Existence of derived extension of scalars.** For a morphism `f : R →+* S` of commutative
rings, termwise scalar extension of unbounded cochain complexes followed by `DerivedCategory.Q`
admits a left derived functor with respect to quasi-isomorphisms. -/
instance hasLeftDerivedFunctor_extendScalars (f : R →+* S)
    [HasDerivedCategory.{w} (ModuleCat.{u} S)] :
    ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q).HasLeftDerivedFunctor
      (quasiIso (ModuleCat.{u} R) (.up ℤ)) :=
  inferInstance

section Adjunction

variable (f : R →+* S) [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w'} (ModuleCat.{u} S)]
  (G : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
  (α : DerivedCategory.Q ⋙ G ⟶
    (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  [G.IsLeftDerivedFunctor α (quasiIso (ModuleCat.{u} R) (.up ℤ))]

/-- **K-flat model computation for derived extension of scalars.** For any left derived functor `G`
of termwise extension of scalars with comparison `α`, the map `α.app K` is an isomorphism whenever
`K` is K-flat. -/
instance isIso_derivedExtendScalarsCounit_of_isKFlat
    (K : CochainComplex (ModuleCat.{u} R) ℤ) [K.IsKFlat] :
    IsIso (α.app K) :=
  (derives_extendScalars f).isIso' α ⟨K, (isKFlatProperty_iff K).2 inferInstance⟩

/-- For any bounded-above cochain complex `K` of flat `R`-modules, the derived extension-of-scalars
comparison `α.app K` is an isomorphism. -/
lemma isIso_derivedExtendScalarsCounit_of_boundedAbove_flat
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) [K.IsStrictlyLE n]
    (hK : ∀ i, Module.Flat R (K.X i)) :
    IsIso (α.app K) :=
  have := isKFlat_of_boundedAbove_flat_moduleCat K n hK
  inferInstance

private lemma isRightDerivedFunctor_restrictScalars :
    (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.IsRightDerivedFunctor
      (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv
      (quasiIso (ModuleCat.{u} S) (.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _
    (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors

private lemma isRightDerivedFunctor_restrictScalars_comp :
    ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory ⋙ G).IsRightDerivedFunctor
      (Functor.whiskerRight (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv G ≫
        (Functor.associator _ _ _).hom)
      (quasiIso (ModuleCat.{u} S) (.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors G)

private lemma isLeftDerivedFunctor_comp_restrictScalars :
    (G ⋙ (ModuleCat.restrictScalars.{u} f).mapDerivedCategory).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight α (ModuleCat.restrictScalars.{u} f).mapDerivedCategory)
      (quasiIso (ModuleCat.{u} R) (.up ℤ)) := by
  have hGR : (kFlatLocalizerMorphism (ModuleCat.{u} R)).Derives
      (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q) ⋙ (ModuleCat.restrictScalars.{u} f).mapDerivedCategory) :=
    fun _ _ φ hφ ↦ by
      have : IsIso (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q).map ((kFlatLocalizerMorphism (ModuleCat.{u} R)).functor.map φ)) :=
        derives_extendScalars f φ hφ
      exact Functor.map_isIso (ModuleCat.restrictScalars.{u} f).mapDerivedCategory _
  exact hGR.isLeftDerivedFunctor_of_isIso
    ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight α (ModuleCat.restrictScalars.{u} f).mapDerivedCategory) fun K ↦ by
      dsimp
      have : IsIso (α.app K.obj) := isIso_derivedExtendScalarsCounit_of_isKFlat f G α K.obj
      infer_instance

/-- **Derived extension of scalars is left adjoint to restriction of scalars.** Every left derived
functor `G` of termwise scalar extension along `f : R →+* S` is left adjoint to
`(ModuleCat.restrictScalars f).mapDerivedCategory`. -/
def derivedExtendRestrictScalarsAdj :
    G ⊣ (ModuleCat.restrictScalars.{u} f).mapDerivedCategory := by
  haveI := isRightDerivedFunctor_restrictScalars f
  haveI := isRightDerivedFunctor_restrictScalars_comp f G
  haveI := isLeftDerivedFunctor_comp_restrictScalars f G α
  exact ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex (.up ℤ)).derived
    (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} S) (.up ℤ)) α
    (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv

/-- Characterization of the unit of `derivedExtendRestrictScalarsAdj` on images of complexes. -/
@[reassoc (attr := simp)]
lemma derivedExtendRestrictScalarsAdj_unit_app_Q (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedExtendRestrictScalarsAdj f G α).unit.app (DerivedCategory.Q.obj K) ≫
      (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.map (α.app K) =
    DerivedCategory.Q.map
        (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
          (.up ℤ)).unit.app K) ≫
      (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app _ := by
  have := isLeftDerivedFunctor_comp_restrictScalars f G α
  exact Adjunction.derivedη_fac_app
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex (.up ℤ))
    (quasiIso (ModuleCat.{u} R) (.up ℤ)) α
    (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv K

/-- Characterization of the counit of `derivedExtendRestrictScalarsAdj` on images of complexes. -/
@[reassoc (attr := simp)]
lemma derivedExtendRestrictScalarsAdj_counit_app_Q (L : CochainComplex (ModuleCat.{u} S) ℤ) :
    G.map ((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app L) ≫
      (derivedExtendRestrictScalarsAdj f G α).counit.app (DerivedCategory.Q.obj L) =
    α.app (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (.up ℤ)).obj L) ≫
      DerivedCategory.Q.map
        (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
          (.up ℤ)).counit.app L) := by
  have := isRightDerivedFunctor_restrictScalars_comp f G
  exact Adjunction.derivedε_fac_app
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex (.up ℤ))
    (quasiIso (ModuleCat.{u} S) (.up ℤ)) α
    (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv L

end Adjunction

end CochainComplex

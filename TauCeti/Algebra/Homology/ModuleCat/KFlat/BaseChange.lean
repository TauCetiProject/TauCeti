/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import TauCeti.Algebra.Homology.Adjunction
public import TauCeti.Algebra.Homology.ModuleCat.KFlat.DerivedTensor
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import TauCeti.Algebra.Category.ModuleCat.Monoidal.ChangeOfRings
import TauCeti.Algebra.Homology.Bifunctor.TwoTermSupport

/-!
# Derived extension of scalars and its adjunction with restriction of scalars

For a homomorphism `f : R →+* S` of commutative rings, degreewise extension of scalars on cochain
complexes (`TauCeti.complexBaseChange f`) does not preserve arbitrary quasi-isomorphisms when `S`
is not flat over `R`, so it does not descend directly to derived categories. It does, however,
preserve quasi-isomorphisms between K-flat complexes of `R`-modules
(`TauCeti.quasiIso_complexBaseChange_map_of_isKFlat`).

Together with the K-flat left derivability structure on `CochainComplex (ModuleCat.{u} R) ℤ`, this
provides:
* existence of the left derived extension-of-scalars functor `- ⊗^L_R S : D(R) ⥤ D(S)`
  (`TauCeti.hasLeftDerivedFunctor_extendScalars`, `TauCeti.derivedExtendScalars`);
* invertibility of the derived comparison on K-flat complexes
  (`TauCeti.isIso_app_of_isKFlat_of_isLeftDerivedFunctor_extendScalars`);
* the derived adjunction `G ⊣ (ModuleCat.restrictScalars f).mapDerivedCategory` for any left
  derived functor `(G, α)` of scalar extension (`TauCeti.derivedExtendRestrictScalarsAdj`,
  `TauCeti.nonempty_derivedExtendRestrictScalarsAdj`), together with the compatibility of its unit
  and counit on complex models with the degreewise lift of `ModuleCat.extendRestrictScalarsAdj f`.

## References

* [The Stacks Project, *The Stacks Project*][stacks-project], Tags 064L, 06Y6, and 0GMT.
* [Georges Maltsiniotis, *Le théorème de Quillen, d'adjonction des foncteurs dérivés,
  revisité*][Maltsiniotis2007].
-/

public section

universe u w w'

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

namespace TauCeti

/-- Ordinary extension of scalars along `f : R →+* S` applied degreewise to cochain complexes. -/
abbrev complexBaseChange {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} S) ℤ :=
  (ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ)

section BaseChangeQuasiIso

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

private def extendCompRestrictIso :
    ModuleCat.extendScalars.{u, u, u} f ⋙ ModuleCat.restrictScalars.{u} f ≅
      (MonoidalCategory.curriedTensor (ModuleCat.{u} R)).obj
        ((ModuleCat.restrictScalars f).obj (𝟙_ (ModuleCat.{u} S))) :=
  Functor.isoWhiskerLeft (ModuleCat.extendScalars f)
    ((Functor.leftUnitor (ModuleCat.restrictScalars f)).symm ≪≫
      Functor.isoWhiskerRight
        (NatIso.ofComponents (fun M ↦ λ_ M) fun g ↦ MonoidalCategory.leftUnitor_naturality g).symm
        (ModuleCat.restrictScalars f)) ≪≫
    ModuleCat.extendScalarsCompTensorLeftIso f (𝟙_ (ModuleCat.{u} S))

private def complexBaseChangeCompRestrictIso :
    complexBaseChange f ⋙
      (ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ) ≅
    (MonoidalCategory.curriedTensor (ModuleCat.{u} R)).mapBifunctorLeft
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
        ((ModuleCat.restrictScalars f).obj (𝟙_ (ModuleCat.{u} S)))) :=
  Functor.mapHomologicalComplexCompIso (extendCompRestrictIso f) (ComplexShape.up ℤ) ≪≫
    ((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).mapBifunctorSingleRowZeroNatIso
      ((ModuleCat.restrictScalars f).obj (𝟙_ (ModuleCat.{u} S)))).symm

/-- Degreewise scalar extension along `f : R →+* S` preserves quasi-isomorphisms between K-flat
cochain complexes of `R`-modules. -/
theorem quasiIso_complexBaseChange_map_of_isKFlat
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} [K.IsKFlat] [L.IsKFlat]
    (φ : K ⟶ L) [QuasiIso φ] :
    QuasiIso ((complexBaseChange f).map φ) := by
  let S₀ : ModuleCat.{u} R := (ModuleCat.restrictScalars f).obj (𝟙_ (ModuleCat.{u} S))
  let P₀ : CochainComplex (ModuleCat.{u} R) ℤ :=
    (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj S₀
  have hP₀ : QuasiIso (tensorHom (𝟙 P₀) φ) := CochainComplex.quasiIso_id_tensorHom_of_isKFlat P₀ φ
  let e := complexBaseChangeCompRestrictIso f
  have hRes : QuasiIso (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).map ((complexBaseChange f).map φ)) := by
    refine quasiIso_of_arrow_mk_iso (tensorHom (𝟙 P₀) φ)
      (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((complexBaseChange f).map φ)) ?_
    exact Arrow.isoMk (e.symm.app K) (e.symm.app L) (e.inv.naturality φ).symm
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    ((complexBaseChange f).map φ) (ModuleCat.restrictScalars.{u} f)).mp hRes

/-- The K-flat localizer morphism on `CochainComplex (ModuleCat.{u} R) ℤ` derives degreewise scalar
extension along `f : R →+* S` followed by `DerivedCategory.Q`. -/
theorem localizerMorphism_derives_complexBaseChange
    [HasDerivedCategory.{w} (ModuleCat.{u} S)] :
    (CochainComplex.KFlat.localizerMorphism (ModuleCat.{u} R)).Derives
      (complexBaseChange f ⋙ DerivedCategory.Q (C := ModuleCat.{u} S)) := by
  rw [LocalizerMorphism.Derives, CochainComplex.KFlat.localizerMorphism_functor]
  intro K L g hg
  have : QuasiIso g.hom := (CochainComplex.KFlat.quasiIso_iff g).1 hg
  have : QuasiIso ((complexBaseChange f).map g.hom) :=
    quasiIso_complexBaseChange_map_of_isKFlat f g.hom
  simp only [Functor.comp_map, ObjectProperty.ι_map]
  infer_instance

end BaseChangeQuasiIso

section DerivedExtendScalars

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- **Derived extension of scalars exists.** For `f : R →+* S`, degreewise scalar extension of
cochain complexes followed by localization to `DerivedCategory (ModuleCat.{u} S)` admits a left
derived functor with respect to quasi-isomorphisms of complexes of `R`-modules. -/
theorem hasLeftDerivedFunctor_extendScalars [HasDerivedCategory.{w} (ModuleCat.{u} S)] :
    (complexBaseChange f ⋙ DerivedCategory.Q (C := ModuleCat.{u} S)).HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  have := (localizerMorphism_derives_complexBaseChange.{u, w} f).hasPointwiseLeftDerivedFunctor
  infer_instance

attribute [instance] hasLeftDerivedFunctor_extendScalars

/-- The canonical left derived extension-of-scalars functor `- ⊗^L_R S` from
`DerivedCategory (ModuleCat.{u} R)` to `DerivedCategory (ModuleCat.{u} S)`. -/
def derivedExtendScalars [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} S)] :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S) :=
  (complexBaseChange f ⋙ DerivedCategory.Q).totalLeftDerived
    DerivedCategory.Q (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))

/-- The canonical counit comparison `Q ⋙ derivedExtendScalars f ⟶ complexBaseChange f ⋙ Q`. -/
def derivedExtendScalarsCounit [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} S)] :
    DerivedCategory.Q ⋙ derivedExtendScalars f ⟶ complexBaseChange f ⋙ DerivedCategory.Q :=
  (complexBaseChange f ⋙ DerivedCategory.Q).totalLeftDerivedCounit
    DerivedCategory.Q (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))

instance instIsLeftDerivedFunctorDerivedExtendScalars
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w'} (ModuleCat.{u} S)] :
    (derivedExtendScalars f).IsLeftDerivedFunctor (derivedExtendScalarsCounit f)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  dsimp only [derivedExtendScalars, derivedExtendScalarsCounit]
  infer_instance

/-- On a K-flat complex `P` of `R`-modules, the comparison `α.app P` of any left derived
extension-of-scalars functor `(G, α)` is an isomorphism in `DerivedCategory (ModuleCat.{u} S)`. -/
instance isIso_app_of_isKFlat_of_isLeftDerivedFunctor_extendScalars
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w'} (ModuleCat.{u} S)]
    (G : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (α : DerivedCategory.Q ⋙ G ⟶ complexBaseChange f ⋙ DerivedCategory.Q)
    [G.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    IsIso (α.app P) := by
  have h := (localizerMorphism_derives_complexBaseChange f).isIso' α
    (CochainComplex.KFlat.mk P)
  have heq : (CochainComplex.KFlat.localizerMorphism (ModuleCat.{u} R)).functor.obj
      (CochainComplex.KFlat.mk P) = P := by
    simp
  rwa [NatTrans.isIso_app_iff_of_iso α (eqToIso heq)] at h

end DerivedExtendScalars

section DerivedAdjunction

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w'} (ModuleCat.{u} S)]

/-- **Derived extension-restriction adjunction.** Any left derived functor `(G, α)` of degreewise
scalar extension along `f : R →+* S` is left adjoint to
`(ModuleCat.restrictScalars f).mapDerivedCategory`. -/
def derivedExtendRestrictScalarsAdj
    (G : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (α : DerivedCategory.Q ⋙ G ⟶ complexBaseChange f ⋙ DerivedCategory.Q)
    [G.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))] :
    G ⊣ (ModuleCat.restrictScalars.{u} f).mapDerivedCategory := by
  let W_R := HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)
  let W_S := HomologicalComplex.quasiIso (ModuleCat.{u} S) (ComplexShape.up ℤ)
  let R' := (ModuleCat.restrictScalars.{u} f).mapDerivedCategory
  let eR := (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors
  have : R'.IsRightDerivedFunctor eR.inv W_S :=
    Functor.isRightDerivedFunctor_of_inverts W_S R' eR
  have : (R' ⋙ G).IsRightDerivedFunctor
      (Functor.whiskerRight eR.inv G ≫ (Functor.associator _ _ _).hom) W_S :=
    Functor.isRightDerivedFunctor_of_inverts W_S (R' ⋙ G)
      ((Functor.associator DerivedCategory.Q R' G).symm ≪≫ Functor.isoWhiskerRight eR G)
  have hDerivesComp : (CochainComplex.KFlat.localizerMorphism (ModuleCat.{u} R)).Derives
      ((complexBaseChange f ⋙ DerivedCategory.Q) ⋙ R') := by
    intro K L g hg
    have : IsIso (((CochainComplex.KFlat.localizerMorphism (ModuleCat.{u} R)).functor ⋙
        (complexBaseChange f ⋙ DerivedCategory.Q)).map g) :=
      localizerMorphism_derives_complexBaseChange f g hg
    dsimp at this ⊢
    infer_instance
  have : (G ⋙ R').IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α R') W_R := by
    refine hDerivesComp.isLeftDerivedFunctor_of_isIso _ fun P ↦ ?_
    have : IsIso (α.app ((CochainComplex.KFlat.localizerMorphism
        (ModuleCat.{u} R)).functor.obj P)) :=
      (localizerMorphism_derives_complexBaseChange f).isIso' α P
    dsimp
    rw [Category.id_comp]
    infer_instance
  exact ((ModuleCat.extendRestrictScalarsAdj f).mapHomologicalComplex
    (ComplexShape.up ℤ)).derived W_R W_S α eR.inv

/-- On a complex model `K`, the unit of `derivedExtendRestrictScalarsAdj` intertwines `α.app K`
with the degreewise extension-restriction unit. -/
@[reassoc (attr := simp)]
theorem derivedExtendRestrictScalarsAdj_unit_app_Q_comp
    (G : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (α : DerivedCategory.Q ⋙ G ⟶ complexBaseChange f ⋙ DerivedCategory.Q)
    [G.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedExtendRestrictScalarsAdj f G α).unit.app (DerivedCategory.Q.obj K) ≫
      (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.map (α.app K) =
    DerivedCategory.Q.map (((ModuleCat.extendRestrictScalarsAdj f).mapHomologicalComplex
        (ComplexShape.up ℤ)).unit.app K) ≫
      (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app
        ((complexBaseChange f).obj K) := by
  dsimp [derivedExtendRestrictScalarsAdj]
  simp

/-- On a complex model `M`, the counit of `derivedExtendRestrictScalarsAdj` intertwines
`mapDerivedCategoryFactors.inv` with the degreewise extension-restriction counit. -/
@[reassoc (attr := simp)]
theorem map_derivedExtendRestrictScalarsAdj_counit_app_Q
    (G : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (α : DerivedCategory.Q ⋙ G ⟶ complexBaseChange f ⋙ DerivedCategory.Q)
    [G.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    (M : CochainComplex (ModuleCat.{u} S) ℤ) :
    G.map ((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app M) ≫
      (derivedExtendRestrictScalarsAdj f G α).counit.app (DerivedCategory.Q.obj M) =
    α.app (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
      DerivedCategory.Q.map (((ModuleCat.extendRestrictScalarsAdj f).mapHomologicalComplex
        (ComplexShape.up ℤ)).counit.app M) := by
  dsimp [derivedExtendRestrictScalarsAdj]
  simp

instance instIsLeftAdjointDerivedExtendScalars :
    (derivedExtendScalars.{u, w, w'} f).IsLeftAdjoint :=
  (derivedExtendRestrictScalarsAdj f (derivedExtendScalars f)
    (derivedExtendScalarsCounit f)).isLeftAdjoint

/-- **Derived extension of scalars is left adjoint to restriction of scalars.** Any left derived
functor `(G, α)` of degreewise scalar extension along `f : R →+* S` admits an adjunction with
`(ModuleCat.restrictScalars f).mapDerivedCategory`. -/
theorem nonempty_derivedExtendRestrictScalarsAdj
    (G : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (α : DerivedCategory.Q ⋙ G ⟶ complexBaseChange f ⋙ DerivedCategory.Q)
    [G.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))] :
    Nonempty (G ⊣ (ModuleCat.restrictScalars.{u} f).mapDerivedCategory) :=
  ⟨derivedExtendRestrictScalarsAdj f G α⟩

end DerivedAdjunction

end TauCeti

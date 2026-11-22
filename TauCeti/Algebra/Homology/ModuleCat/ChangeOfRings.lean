/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Monoidal.ChangeOfRings
public import TauCeti.Algebra.Homology.Bifunctor.TwoTermSupport

/-!
# Degreewise extension of scalars on module cochain complexes

For a homomorphism `f : R →+* S` of commutative rings, `TauCeti.complexBaseChange f` applies
`ModuleCat.extendScalars f` degreewise to cochain complexes of `R`-modules. Composing it with
degreewise restriction of scalars identifies naturally with left tensoring by `S` concentrated in
degree `0` (`TauCeti.complexBaseChangeCompRestrictScalarsIso`).

This provides the complex-level functor derived to `- ⊗^L_R S` on unbounded derived categories:
since degreewise restriction of scalars preserves and reflects quasi-isomorphisms,
`TauCeti.complexBaseChangeCompRestrictScalarsIso` reduces preservation of quasi-isomorphisms
between K-flat complexes by `TauCeti.complexBaseChange f` to left tensoring with `S[0]`.
-/

public section

universe u

noncomputable section

open CategoryTheory HomologicalComplex
open scoped MonoidalCategory

namespace TauCeti

/-- Ordinary extension of scalars along `f : R →+* S` applied degreewise to cochain complexes. -/
abbrev complexBaseChange {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} S) ℤ :=
  (ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Natural isomorphism identifying degreewise scalar extension along `f : R →+* S` followed by
degreewise scalar restriction with left tensoring by
`(ModuleCat.restrictScalars f).obj (𝟙_ (ModuleCat S))` concentrated in degree `0`. -/
def complexBaseChangeCompRestrictScalarsIso {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) :
    complexBaseChange f ⋙
      (ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ) ≅
    (MonoidalCategory.curriedTensor (ModuleCat.{u} R)).mapBifunctorLeft
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
        ((ModuleCat.restrictScalars f).obj (𝟙_ (ModuleCat.{u} S)))) :=
  Functor.mapHomologicalComplexCompIso
      (ModuleCat.extendScalarsCompRestrictScalarsIso f) (ComplexShape.up ℤ) ≪≫
    ((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).mapBifunctorSingleRowZeroNatIso
      ((ModuleCat.restrictScalars f).obj (𝟙_ (ModuleCat.{u} S)))).symm

/-- In degree `j`, the forward comparison `complexBaseChangeCompRestrictScalarsIso` applies
`ModuleCat.extendScalarsCompRestrictScalarsIso` and includes the degree-`(0, j)` summand. -/
@[reassoc, simp]
theorem complexBaseChangeCompRestrictScalarsIso_hom_app_f
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (j : ℤ) :
    ((complexBaseChangeCompRestrictScalarsIso f).hom.app K).f j =
      (ModuleCat.extendScalarsCompRestrictScalarsIso f).hom.app (K.X j) ≫
        ((singleObjXSelf (ComplexShape.up ℤ) 0
          ((ModuleCat.restrictScalars f).obj (𝟙_ (ModuleCat.{u} S)))).inv ▷ K.X j) ≫
        ιMapBifunctor
          ((single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
            ((ModuleCat.restrictScalars f).obj (𝟙_ (ModuleCat.{u} S))))
          K (MonoidalCategory.curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ) 0 j j
          (zero_add j) := by
  simp [complexBaseChangeCompRestrictScalarsIso]

/-- On the degree-`(0, j)` summand, the inverse comparison `complexBaseChangeCompRestrictScalarsIso`
identifies the degree-`0` term of the single complex on the left factor via `singleObjXSelf` and
applies `(ModuleCat.extendScalarsCompRestrictScalarsIso f).inv`. -/
@[reassoc (attr := simp), simp]
theorem ι_complexBaseChangeCompRestrictScalarsIso_inv_app_f
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (j : ℤ) :
    ιMapBifunctor
        ((single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
          ((ModuleCat.restrictScalars f).obj (𝟙_ (ModuleCat.{u} S))))
        K (MonoidalCategory.curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ) 0 j j
        (zero_add j) ≫
      ((complexBaseChangeCompRestrictScalarsIso f).inv.app K).f j =
    ((singleObjXSelf (ComplexShape.up ℤ) 0
        ((ModuleCat.restrictScalars f).obj (𝟙_ (ModuleCat.{u} S)))).hom ▷ K.X j) ≫
      (ModuleCat.extendScalarsCompRestrictScalarsIso f).inv.app (K.X j) := by
  simp [complexBaseChangeCompRestrictScalarsIso]

end TauCeti

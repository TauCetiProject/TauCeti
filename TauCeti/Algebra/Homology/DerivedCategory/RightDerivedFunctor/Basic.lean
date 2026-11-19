/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import TauCeti.Algebra.Homology.DerivedCategory.KInjective
public import TauCeti.CategoryTheory.Functor.Derived.RightDerived

/-!
# Unbounded right derived functors

Let `F : C ⥤ D` be an additive functor between abelian categories, where every cochain complex
in `C`, with no boundedness assumption, has a K-injective replacement
(`TauCeti.HasKInjectiveResolutions C`, which holds for Grothendieck abelian categories, such as
sheaves of modules). The right derived functor
`F.rightDerivedFunctor : DerivedCategory C ⥤ DerivedCategory D` applies `F` termwise to a
K-injective replacement: it is the composite of the K-injective replacement functor
`TauCeti.kInjectiveReplacement C`, the functor `F.mapHomotopyCategory` induced on homotopy
categories, and the localization functor `DerivedCategory.Qh`.

Together with the transformation `F.rightDerivedFunctorUnith` induced by the replacement maps
`K ⟶ I(K)`, it is a right derived functor of `F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh`
with respect to the quasi-isomorphisms, in the sense of Mathlib's
`CategoryTheory.Functor.IsRightDerivedFunctor`: a left Kan extension along `DerivedCategory.Qh`.
It is triangulated, and its value on a K-injective complex `I` is `F(I)`
(`CategoryTheory.Functor.rightDerivedFunctorObjIso`). An exact functor is its own right derived
functor: `F.rightDerivedFunctor ≅ F.mapDerivedCategory`
(`CategoryTheory.Functor.rightDerivedFunctorIsoMapDerivedCategory`); in particular the right
derived functor of the identity is the identity (`CategoryTheory.Functor.rightDerivedFunctorIdIso`).
Isomorphic functors have isomorphic right derived functors
(`CategoryTheory.NatIso.rightDerivedFunctor`).

Mathlib's `CategoryTheory.Functor.rightDerivedFunctorPlus` is the analogous construction on
bounded below derived categories, using injective resolutions.

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154.
* [Stacks Project, Lemma 13.31.7 (Tag 070K)](https://stacks.math.columbia.edu/tag/070K).
-/

public section

noncomputable section

open CategoryTheory DerivedCategory Limits TauCeti Functor

universe w w' v v' u u'

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] [HasKInjectiveResolutions C]
  (F : C ⥤ D) [F.Additive]

/-- The right derived functor `RF : D(C) ⥤ D(D)` of an additive functor `F : C ⥤ D`, computed
by applying `F` termwise to K-injective replacements. -/
@[expose]
def rightDerivedFunctor : DerivedCategory C ⥤ DerivedCategory D :=
  kInjectiveReplacement C ⋙ F.mapHomotopyCategory (.up ℤ) ⋙ Qh

/-- The natural transformation `F(K) ⟶ RF(K)` induced by the K-injective replacements
`K ⟶ I(K)`. -/
def rightDerivedFunctorUnith :
    F.mapHomotopyCategory (.up ℤ) ⋙ Qh ⟶ Qh ⋙ F.rightDerivedFunctor :=
  (kInjectiveReplacementAdjunction C).whiskerRightUnit (F.mapHomotopyCategory (.up ℤ) ⋙ Qh)

lemma rightDerivedFunctorUnith_app (K : HomotopyCategory C (.up ℤ)) :
    F.rightDerivedFunctorUnith.app K =
      Qh.map ((F.mapHomotopyCategory _).map ((kInjectiveReplacementAdjunction C).unit.app K)) :=
  Adjunction.whiskerRightUnit_app _ _ _

instance : F.rightDerivedFunctor.IsRightDerivedFunctor F.rightDerivedFunctorUnith
    (HomotopyCategory.quasiIso C (.up ℤ)) :=
  (kInjectiveReplacementAdjunction C).isRightDerivedFunctor_whiskerRightUnit _ _

noncomputable instance : F.rightDerivedFunctor.CommShift ℤ :=
  inferInstanceAs ((kInjectiveReplacement C ⋙ F.mapHomotopyCategory (.up ℤ) ⋙ Qh).CommShift ℤ)

instance : F.rightDerivedFunctor.IsTriangulated :=
  inferInstanceAs (kInjectiveReplacement C ⋙ F.mapHomotopyCategory (.up ℤ) ⋙ Qh).IsTriangulated

/-- On a K-injective complex, the comparison `F(K) ⟶ RF(K)` is an isomorphism. -/
instance (K : HomotopyCategory C (.up ℤ)) [CochainComplex.IsKInjective K.as] :
    IsIso (F.rightDerivedFunctorUnith.app K) := by
  rw [rightDerivedFunctorUnith_app]
  exact (Qh.mapIso ((F.mapHomotopyCategory _).mapIso (asIso _))).isIso_hom

/-- The right derived functor sends a K-injective complex `I` to `F(I)`. -/
def rightDerivedFunctorObjIso (I : CochainComplex C ℤ) [I.IsKInjective] :
    F.rightDerivedFunctor.obj (Q.obj I) ≅ Q.obj ((F.mapHomologicalComplex _).obj I) :=
  have : CochainComplex.IsKInjective ((HomotopyCategory.quotient _ _).obj I).as := ‹_›
  F.rightDerivedFunctor.mapIso ((quotientCompQhIso C).app I).symm ≪≫
    (asIso (F.rightDerivedFunctorUnith.app ((HomotopyCategory.quotient _ _).obj I))).symm ≪≫
    Qh.mapIso ((F.mapHomotopyCategoryFactors (.up ℤ)).app I) ≪≫ (quotientCompQhIso D).app _

/-- An exact functor is its own right derived functor: `RF` is the functor `F.mapDerivedCategory`
induced by `F` on derived categories. -/
def rightDerivedFunctorIsoMapDerivedCategory [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] :
    F.rightDerivedFunctor ≅ F.mapDerivedCategory :=
  isoWhiskerLeft (kInjectiveReplacement C) F.mapDerivedCategoryFactorsh.symm ≪≫
    (associator _ _ _).symm ≪≫
    isoWhiskerRight (asIso (kInjectiveReplacementAdjunction C).counit) F.mapDerivedCategory ≪≫
    F.mapDerivedCategory.leftUnitor

variable (C) in
/-- The right derived functor of the identity functor is the identity functor. -/
def rightDerivedFunctorIdIso : (𝟭 C).rightDerivedFunctor ≅ 𝟭 (DerivedCategory C) :=
  (𝟭 C).rightDerivedFunctorIsoMapDerivedCategory ≪≫ mapDerivedCategoryIdIso C

end CategoryTheory.Functor

namespace CategoryTheory.NatIso

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] [HasKInjectiveResolutions C]
  {F G : C ⥤ D} [F.Additive] [G.Additive]

/-- Isomorphic additive functors have isomorphic right derived functors. -/
def rightDerivedFunctor (e : F ≅ G) : F.rightDerivedFunctor ≅ G.rightDerivedFunctor :=
  isoWhiskerLeft (kInjectiveReplacement C)
    (isoWhiskerRight (NatIso.mapHomotopyCategory e (.up ℤ)) Qh)

end CategoryTheory.NatIso

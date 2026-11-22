/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import TauCeti.Algebra.Homology.DerivedCategory.RightDerivedFunctor.Basic
public import TauCeti.Algebra.Homology.Embedding.Extend.Homology.Basic
public import TauCeti.Algebra.Homology.Functor.Extend

/-!
# Cohomology of unbounded right derived functors of objects

Let `F : C ⥤ D` be an additive functor between abelian categories, where `C` has injective
resolutions of objects and K-injective replacements of unbounded complexes. For an object `X` of
`C`, the K-injective replacement of `X[0]` is an injective resolution of `X`, viewed as a complex
indexed by `ℤ` (`TauCeti.singleFunctorCompKInjectiveReplacementIso`). Consequently the cohomology
sheaves of the unbounded right derived functor `F.rightDerivedFunctor` on `X[0]` are the classical
right derived functors `RⁿF` of Mathlib's `CategoryTheory.Functor.rightDerived`, naturally in `X`:
`Hⁿ(RF(X[0])) ≅ RⁿF(X)` for every `n : ℕ` (`CategoryTheory.Functor.rightDerivedFunctorHomologyIso`).

The comparison goes through Mathlib's `CategoryTheory.InjectiveResolution.cochainComplex`, the
extension by zero of an injective resolution along `ComplexShape.embeddingUpNat`, with its
quasi-isomorphism `CategoryTheory.InjectiveResolution.ι'` from `X[0]`.

## References

* [Stacks Project, Lemma 13.31.7 (Tag 070K)](https://stacks.math.columbia.edu/tag/070K): a right
  derived functor computed by K-injective complexes takes the value `F(I)` on a K-injective `I`.
-/

public section

noncomputable section

open CategoryTheory DerivedCategory Functor

universe w w' v v' u u'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]

namespace TauCeti

/-- The quasi-isomorphisms `X[0] ⟶ I` into injective resolutions, extended by zero to complexes
indexed by `ℤ`, as a natural transformation of functors to the homotopy category. -/
def singleToInjectiveResolutions :
    CochainComplex.singleFunctor C 0 ⋙ HomotopyCategory.quotient C (.up ℤ) ⟶
      injectiveResolutions C ⋙ ComplexShape.embeddingUpNat.extendHomotopyFunctor C where
  app X := (HomotopyCategory.quotient C _).map (injectiveResolution X).ι'
  naturality X Y f := by
    let φ : (injectiveResolution X).Hom (injectiveResolution Y) f :=
      ⟨InjectiveResolution.desc f _ _,
        (InjectiveResolution.desc_commutes_zero f _ _).trans (by simp)⟩
    -- By definition, `injectiveResolutions C` sends `f` to the class of its lift
    -- `InjectiveResolution.desc`, and `extendHomotopyFunctor` is induced by `extendMap`.
    have h : (injectiveResolutions C ⋙ ComplexShape.embeddingUpNat.extendHomotopyFunctor C).map f =
        (HomotopyCategory.quotient C _).map φ.hom' := rfl
    rw [Functor.comp_map, h]
    exact ((HomotopyCategory.quotient C _).map_comp _ _).symm.trans
      ((congrArg (HomotopyCategory.quotient C _).map φ.ι'_comp_hom'.symm).trans
        ((HomotopyCategory.quotient C _).map_comp _ _))

lemma singleToInjectiveResolutions_app (X : C) :
    (singleToInjectiveResolutions (C := C)).app X =
      (HomotopyCategory.quotient C _).map (injectiveResolution X).ι' :=
  (rfl)

instance (X : C) : CochainComplex.IsKInjective
    ((injectiveResolutions C ⋙ ComplexShape.embeddingUpNat.extendHomotopyFunctor C).obj X).as :=
  CochainComplex.isKInjective_of_injective (injectiveResolution X).cochainComplex 0

variable [HasDerivedCategory.{w} C]

/-- The maps `X[0] ⟶ I` into injective resolutions are quasi-isomorphisms. -/
instance (X : C) : IsIso (Qh.map ((singleToInjectiveResolutions (C := C)).app X)) :=
  (isIso_Qh_map_iff _).2 ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
    (inferInstanceAs (QuasiIso (injectiveResolution X).ι')))

instance : IsIso (whiskerRight (singleToInjectiveResolutions (C := C)) Qh) :=
  have (X : C) : IsIso ((whiskerRight (singleToInjectiveResolutions (C := C)) Qh).app X) :=
    inferInstanceAs (IsIso (Qh.map _))
  NatIso.isIso_of_isIso_app _

variable [HasKInjectiveResolutions C]

instance : IsIso (whiskerLeft
    (injectiveResolutions C ⋙ ComplexShape.embeddingUpNat.extendHomotopyFunctor C)
    (kInjectiveReplacementAdjunction C).unit) :=
  have (X : C) : IsIso ((whiskerLeft
      (injectiveResolutions C ⋙ ComplexShape.embeddingUpNat.extendHomotopyFunctor C)
      (kInjectiveReplacementAdjunction C).unit).app X) :=
    inferInstanceAs (IsIso ((kInjectiveReplacementAdjunction C).unit.app _))
  NatIso.isIso_of_isIso_app _

variable (C) in
/-- The K-injective replacement of an object `X` placed in degree `0` is an injective resolution of
`X`, extended by zero to a complex indexed by `ℤ`: this holds naturally in `X`, in the homotopy
category. -/
def singleFunctorCompKInjectiveReplacementIso :
    singleFunctor C 0 ⋙ kInjectiveReplacement C ≅
      injectiveResolutions C ⋙ ComplexShape.embeddingUpNat.extendHomotopyFunctor C :=
  isoWhiskerRight
      (singleFunctorIsoCompQ C 0 ≪≫ isoWhiskerLeft _ (quotientCompQhIso C).symm ≪≫
        asIso (whiskerRight singleToInjectiveResolutions Qh)) _ ≪≫
    (asIso (whiskerLeft _ (kInjectiveReplacementAdjunction C).unit)).symm

end TauCeti

namespace CategoryTheory.Functor

variable [HasDerivedCategory.{w} C] [TauCeti.HasKInjectiveResolutions C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive]

/-- The cohomology of the unbounded right derived functor `RF` on an object `X` placed in degree
`0` is the classical right derived functor: `Hⁿ(RF(X[0])) ≅ RⁿF(X)`, naturally in `X`. -/
def rightDerivedFunctorHomologyIso (n : ℕ) :
    singleFunctor C 0 ⋙ F.rightDerivedFunctor ⋙ homologyFunctor D n ≅ F.rightDerived n :=
  isoWhiskerLeft (singleFunctor C 0)
      (isoWhiskerRight F.rightDerivedFunctorIsoKInjectiveReplacement (homologyFunctor D n)) ≪≫
    isoWhiskerRight (TauCeti.singleFunctorCompKInjectiveReplacementIso C)
      (F.mapHomotopyCategory _ ⋙ Qh ⋙ homologyFunctor D n) ≪≫
    isoWhiskerLeft (injectiveResolutions C ⋙ ComplexShape.embeddingUpNat.extendHomotopyFunctor C ⋙
      F.mapHomotopyCategory _) (homologyFunctorFactorsh D n) ≪≫
    isoWhiskerLeft (injectiveResolutions C)
      (isoWhiskerRight (F.mapHomotopyCategoryExtendIso ComplexShape.embeddingUpNat)
          (HomotopyCategory.homologyFunctor D _ n) ≪≫
        isoWhiskerLeft (F.mapHomotopyCategory _)
          (ComplexShape.embeddingUpNat.extendHomotopyFunctorCompHomologyFunctorIso D (j := n) rfl))

end CategoryTheory.Functor

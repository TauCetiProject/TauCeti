/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.Equivalence
public import TauCeti.AlgebraicGeometry.Modules.Restriction.Coherence

/-!
# Derived restriction to open subschemes

For an open immersion `f : X ⟶ Y`, restriction of module sheaves
`AlgebraicGeometry.Scheme.Modules.restrictFunctor f` is exact: it is a left adjoint in Mathlib, and
additive and a right adjoint in Tau Ceti (`Scheme.Modules.restrictFunctorIsRightAdjoint`). Its
derived functor `AlgebraicGeometry.Scheme.Hom.derivedRestrict f : D(𝒪_Y) ⥤ D(𝒪_X)`,
`K ↦ K|_X`, is Mathlib's `Functor.mapDerivedCategory`, so it is a triangulated functor and Mathlib's
API for derived functors of exact functors applies to it directly: on complexes through
`Functor.mapDerivedCategoryFactors`, and on sheaves placed in one degree through
`Functor.mapDerivedCategorySingleFunctor`. Derived restriction restricts objects and morphisms of
derived categories; the following comparisons identify iterated restrictions with direct ones.

* `Scheme.Hom.derivedRestrictComp f g h w`: for open immersions with `w : f ≫ g = h`, the
  comparison `(K|_Y)|_X ≅ K|_X` induced by `Scheme.Modules.restrictFunctorComp` and
  `Scheme.Modules.restrictFunctorCongr`, with its values on complexes and on sheaves placed in one
  degree.
* `Scheme.derivedRestrictId X`: derived restriction along the identity of `X` is the identity.
* `Scheme.Hom.derivedRestrictComp_associativity`: for three composable open immersions the two
  comparisons of the threefold restriction with the restriction along the composite agree;
  `TauCeti.AlgebraicGeometry.Coherent.derivedRestrictComp_homOfLE_associativity` is the case of
  nested opens `W ≤ V ≤ U` of a scheme, `((K|_U)|_V)|_W ≅ K|_W`.
* `Scheme.Hom.derivedRestrictComp_id_comp`, `Scheme.Hom.derivedRestrictComp_comp_id`: for a
  composite with an identity, the comparison is induced by `Scheme.derivedRestrictId`.
* Derived restriction along an isomorphism of schemes is an equivalence, obtained from the
  equivalence `Scheme.Modules.restrictEquivalence` of categories of module sheaves; for instance
  restriction to the open `⊤` is.

These comparisons are used to formulate the gluing of morphisms and objects of derived
categories of module sheaves along open covers.

## References

* [Stacks: Lemma 20.45.2](https://stacks.math.columbia.edu/tag/0D66), where restriction of
  derived morphisms to opens is composed through these comparisons.
-/

public section

open CategoryTheory Limits DerivedCategory

universe w₁ w₂ w₃ w₄ u

namespace AlgebraicGeometry.Scheme.Hom

open Scheme.Modules

variable {X Y Z T : Scheme.{u}} [HasDerivedCategory.{w₁} X.Modules]
  [HasDerivedCategory.{w₂} Y.Modules] [HasDerivedCategory.{w₃} Z.Modules]
  [HasDerivedCategory.{w₄} T.Modules]

/-- Derived restriction `K ↦ K|_X` along an open immersion `f : X ⟶ Y`: the functor
`D(𝒪_Y) ⥤ D(𝒪_X)` induced by the exact functor `Scheme.Modules.restrictFunctor f`. It is an
abbreviation, so that Mathlib's API for `Functor.mapDerivedCategory` (its shift and triangulated
structure, its values on complexes and on sheaves in one degree) applies to it. -/
noncomputable abbrev derivedRestrict (f : X ⟶ Y) [IsOpenImmersion f] :
    DerivedCategory Y.Modules ⥤ DerivedCategory X.Modules :=
  (Modules.restrictFunctor f).mapDerivedCategory

/-- For open immersions `f : X ⟶ Y`, `g : Y ⟶ Z` and `h : X ⟶ Z` with `f ≫ g = h`, the
comparison `(K|_Y)|_X ≅ K|_X` of derived restrictions: Mathlib's
`Functor.mapDerivedCategoryCompIso` followed by the natural isomorphism induced by the comparison
`Scheme.Modules.restrictFunctorComp` and `Scheme.Modules.restrictFunctorCongr` of restrictions of
module sheaves. -/
noncomputable def derivedRestrictComp (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion h] :
    g.derivedRestrict ⋙ f.derivedRestrict ≅ h.derivedRestrict :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    NatIso.mapDerivedCategory ((restrictFunctorComp f g).symm ≪≫ restrictFunctorCongr w)

section

variable (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion h]

/-- `derivedRestrictComp` is the composite of `Functor.mapDerivedCategoryCompIso` with the
natural transformation induced by the comparison of restrictions of module sheaves. -/
lemma derivedRestrictComp_hom :
    (derivedRestrictComp f g h w).hom = (Functor.mapDerivedCategoryCompIso _ _).hom ≫
      NatTrans.mapDerivedCategory
        ((restrictFunctorComp f g).inv ≫ (restrictFunctorCongr w).hom) := by
  simp [derivedRestrictComp]

/-- The inverse of `derivedRestrictComp` is the natural transformation induced by the inverse
comparison of restrictions of module sheaves, followed by the inverse of
`Functor.mapDerivedCategoryCompIso`. -/
lemma derivedRestrictComp_inv :
    (derivedRestrictComp f g h w).inv = NatTrans.mapDerivedCategory
        ((restrictFunctorCongr w).inv ≫ (restrictFunctorComp f g).hom) ≫
      (Functor.mapDerivedCategoryCompIso _ _).inv := by
  simp [derivedRestrictComp]

/-- On a complex `K`, the comparison `derivedRestrictComp` is the localization of the termwise
comparison of restrictions of module sheaves, up to the identifications of derived restriction on
complexes. -/
@[reassoc]
lemma derivedRestrictComp_hom_app_Q_obj (K : CochainComplex Z.Modules ℤ) :
    (derivedRestrictComp f g h w).hom.app (Q.obj K) =
      f.derivedRestrict.map ((Modules.restrictFunctor g).mapDerivedCategoryFactors.hom.app K) ≫
        (Modules.restrictFunctor f).mapDerivedCategoryFactors.hom.app
          (((Modules.restrictFunctor g).mapHomologicalComplex _).obj K) ≫
          Q.map ((NatTrans.mapHomologicalComplex
            ((restrictFunctorComp f g).inv ≫ (restrictFunctorCongr w).hom) (.up ℤ)).app K) ≫
            (Modules.restrictFunctor h).mapDerivedCategoryFactors.inv.app K := by
  rw [derivedRestrictComp_hom, NatTrans.comp_app]
  exact Functor.mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategory_app_Q_obj _ _ _ K

/-- On a module sheaf `M` placed in degree `n`, the comparison `derivedRestrictComp` is the
comparison `(M|_Y)|_X ≅ M|_X` of restrictions of `M` placed in degree `n`, up to the
identifications of derived restriction on sheaves in one degree. -/
@[reassoc]
lemma derivedRestrictComp_hom_app_singleFunctor_obj (M : Z.Modules) (n : ℤ) :
    (derivedRestrictComp f g h w).hom.app ((singleFunctor _ n).obj M) =
      f.derivedRestrict.map
          (((Modules.restrictFunctor g).mapDerivedCategorySingleFunctor n).hom.app M) ≫
        ((Modules.restrictFunctor f).mapDerivedCategorySingleFunctor n).hom.app _ ≫
          (singleFunctor _ n).map
            ((restrictFunctorComp f g).inv.app M ≫ (restrictFunctorCongr w).hom.app M) ≫
            ((Modules.restrictFunctor h).mapDerivedCategorySingleFunctor n).inv.app M := by
  rw [derivedRestrictComp_hom, NatTrans.comp_app, NatTrans.mapDerivedCategory_app_singleFunctor_obj,
    Functor.mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategorySingleFunctor_hom_app_assoc,
    NatTrans.comp_app]

/-- The comparison `derivedRestrictComp` commutes with the shifts of derived categories. -/
instance : NatTrans.CommShift (derivedRestrictComp f g h w).hom ℤ := by
  rw [derivedRestrictComp_hom]
  infer_instance

end

/-- Associativity of the comparisons of derived restrictions: for open immersions
`f : X ⟶ Y`, `g : Y ⟶ Z`, `h : Z ⟶ T`, the comparison `((K|_Z)|_Y)|_X ≅ K|_X` built by first
combining the restrictions along `h` and `g` agrees with the one built by first combining those
along `g` and `f`. -/
theorem derivedRestrictComp_associativity (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (fg : X ⟶ Z)
    (gh : Y ⟶ T) (fgh : X ⟶ T) (w₁ : f ≫ g = fg) (w₂ : g ≫ h = gh) (w₃ : fg ≫ h = fgh)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion h]
    [IsOpenImmersion fg] [IsOpenImmersion gh] [IsOpenImmersion fgh] :
    Functor.whiskerRight (derivedRestrictComp g h gh w₂).hom f.derivedRestrict ≫
        (derivedRestrictComp f gh fgh (by rw [← w₃, ← w₂, ← w₁, Category.assoc])).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft h.derivedRestrict (derivedRestrictComp f g fg w₁).hom ≫
          (derivedRestrictComp fg h fgh w₃).hom := by
  simp only [derivedRestrictComp_hom]
  exact Functor.mapDerivedCategoryCompIso_associativity _ _ _ _ _ _ _
    (restrictFunctorComp_associativity f g h fg gh fgh w₁ w₂ w₃)

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme

open Scheme.Modules

universe w

variable (X : Scheme.{u}) [HasDerivedCategory.{w} X.Modules]

/-- Derived restriction along the identity of `X` is the identity of `D(𝒪_X)`: the natural
isomorphism induced by `Scheme.Modules.restrictFunctorId` followed by Mathlib's
`Functor.mapDerivedCategoryIdIso`. -/
noncomputable def derivedRestrictId : Hom.derivedRestrict (𝟙 X) ≅ 𝟭 _ :=
  NatIso.mapDerivedCategory restrictFunctorId ≪≫ Functor.mapDerivedCategoryIdIso _

/-- The comparison `derivedRestrictId` commutes with the shifts of derived categories. -/
instance : NatTrans.CommShift (derivedRestrictId X).hom ℤ := by
  rw [derivedRestrictId, Iso.trans_hom]
  infer_instance

/-- On a complex `K`, `derivedRestrictId` is the localization of the termwise identification
`Scheme.Modules.restrictFunctorId` of restriction along the identity, up to the identification of
derived restriction on complexes. -/
lemma derivedRestrictId_hom_app_Q_obj (K : CochainComplex X.Modules ℤ) :
    (derivedRestrictId X).hom.app (Q.obj K) =
      (Modules.restrictFunctor (𝟙 X)).mapDerivedCategoryFactors.hom.app K ≫
        Q.map ((NatTrans.mapHomologicalComplex restrictFunctorId.hom (.up ℤ)).app K ≫
          (Functor.mapHomologicalComplexIdIso _ _).hom.app K) := by
  simp [derivedRestrictId, NatTrans.mapDerivedCategory_app_Q_obj,
    Functor.mapDerivedCategoryIdIso_hom_app]

/-- On a module sheaf `M` placed in degree `n`, `derivedRestrictId` is the identification of
`M|_X` with `M` for the identity of `X`, placed in degree `n`. -/
lemma derivedRestrictId_hom_app_singleFunctor_obj (M : X.Modules) (n : ℤ) :
    (derivedRestrictId X).hom.app ((singleFunctor _ n).obj M) =
      ((Modules.restrictFunctor (𝟙 X)).mapDerivedCategorySingleFunctor n).hom.app M ≫
        (singleFunctor _ n).map (restrictFunctorId.hom.app M) := by
  simp only [derivedRestrictId, Iso.trans_hom, NatIso.mapDerivedCategory_hom, NatTrans.comp_app,
    NatTrans.mapDerivedCategory_app_singleFunctor_obj, Functor.comp_obj,
    Functor.mapDerivedCategoryIdIso_hom_app_singleFunctor_obj', Category.assoc,
    NatIso.cancel_natIso_hom_left, Iso.inv_hom_id_app]
  exact Category.comp_id _

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Hom

open Scheme.Modules

variable {X Y Z : Scheme.{u}} [HasDerivedCategory.{w₁} X.Modules]
  [HasDerivedCategory.{w₂} Y.Modules] [HasDerivedCategory.{w₃} Z.Modules]

/-- For an open immersion `g : Y ⟶ Z`, the comparison `(K|_Y)|_Y ≅ K|_Y` for `𝟙 Y ≫ g = g` is
induced by the identification `Scheme.derivedRestrictId` of derived restriction along `𝟙 Y`. -/
@[simp]
lemma derivedRestrictComp_id_comp (g : Y ⟶ Z) [IsOpenImmersion g] :
    (derivedRestrictComp (𝟙 Y) g g (Category.id_comp g)).hom =
      Functor.whiskerLeft g.derivedRestrict (derivedRestrictId Y).hom ≫
        (Functor.rightUnitor _).hom := by
  rw [derivedRestrictComp_hom, derivedRestrictId, Iso.trans_hom, NatIso.mapDerivedCategory_hom]
  exact Functor.mapDerivedCategoryCompIso_right_unitality _ _ (restrictFunctorComp_id_comp g)

/-- For an open immersion `f : X ⟶ Y`, the comparison `(K|_Y)|_X ≅ K|_X` for `f ≫ 𝟙 Y = f` is
the derived restriction along `f` of the identification `Scheme.derivedRestrictId` of derived
restriction along `𝟙 Y`. -/
@[simp]
lemma derivedRestrictComp_comp_id (f : X ⟶ Y) [IsOpenImmersion f] :
    (derivedRestrictComp f (𝟙 Y) f (Category.comp_id f)).hom =
      Functor.whiskerRight (derivedRestrictId Y).hom f.derivedRestrict ≫
        (Functor.leftUnitor _).hom := by
  rw [derivedRestrictComp_hom, derivedRestrictId, Iso.trans_hom, NatIso.mapDerivedCategory_hom]
  exact Functor.mapDerivedCategoryCompIso_left_unitality _ _ (restrictFunctorComp_comp_id f)

/-- Derived restriction along an isomorphism of schemes is an equivalence: it is the functor of
the derived equivalence induced by `Scheme.Modules.restrictEquivalence`. -/
instance (f : X ⟶ Y) [IsIso f] : f.derivedRestrict.IsEquivalence := by
  have : (restrictEquivalence (asIso f)).functor.Additive := by
    rw [restrictEquivalence_functor]
    exact restrictFunctorAdditive f
  have := ((restrictEquivalence (asIso f)).mapDerivedCategory).isEquivalence_functor
  simpa only [Equivalence.mapDerivedCategory_functor, restrictEquivalence_functor, asIso_hom]
    using this

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti.AlgebraicGeometry.Coherent

open _root_.AlgebraicGeometry

variable {X : Scheme.{u}} [HasDerivedCategory.{w₁} X.Modules] {U V W : X.Opens}
  [HasDerivedCategory.{w₂} U.toScheme.Modules] [HasDerivedCategory.{w₃} V.toScheme.Modules]
  [HasDerivedCategory.{w₄} W.toScheme.Modules]

/-- For nested opens `W ≤ V ≤ U` of a scheme `X` and `K ∈ D(𝒪_X)`, the two comparisons
`((K|_U)|_V)|_W ≅ K|_W` built from `Scheme.Hom.derivedRestrictComp` agree: restricting the
comparison for `V ≤ U` to `W` and then comparing on `W ≤ V`, or first comparing the restrictions
along `W ≤ V ≤ U` and then on `W ≤ U`. -/
theorem derivedRestrictComp_homOfLE_associativity (hWV : W ≤ V) (hVU : V ≤ U)
    (K : DerivedCategory X.Modules) :
    (X.homOfLE hWV).derivedRestrict.map
        (((X.homOfLE hVU).derivedRestrictComp U.ι V.ι (X.homOfLE_ι hVU)).hom.app K) ≫
      ((X.homOfLE hWV).derivedRestrictComp V.ι W.ι (X.homOfLE_ι hWV)).hom.app K =
    ((X.homOfLE hWV).derivedRestrictComp (X.homOfLE hVU) (X.homOfLE (hWV.trans hVU))
        (X.homOfLE_homOfLE hWV hVU)).hom.app (U.ι.derivedRestrict.obj K) ≫
      ((X.homOfLE (hWV.trans hVU)).derivedRestrictComp U.ι W.ι (X.homOfLE_ι _)).hom.app K := by
  simpa using congr_app (Scheme.Hom.derivedRestrictComp_associativity (X.homOfLE hWV)
    (X.homOfLE hVU) U.ι _ _ _ (X.homOfLE_homOfLE hWV hVU) (X.homOfLE_ι hVU) (X.homOfLE_ι _)) K

end TauCeti.AlgebraicGeometry.Coherent

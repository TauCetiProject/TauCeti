/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Restriction.Basic

/-!
# Coherence of the restriction comparisons

For open immersions `f : X ⟶ Y` and `g : Y ⟶ Z` with `f ≫ g = h`, Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` and
`AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr` compare restricting along `g` and then
along `f` with restricting along `h`. For three composable open immersions, the two ways of
comparing the threefold restriction with restriction along the composite agree
(`AlgebraicGeometry.Scheme.Hom.restrictFunctorComp_associativity`), and for a composite with an
identity the comparison is Mathlib's identification
`AlgebraicGeometry.Scheme.Modules.restrictFunctorId` of restriction along the identity
(`AlgebraicGeometry.Scheme.Hom.restrictFunctorComp_id_comp`,
`AlgebraicGeometry.Scheme.Hom.restrictFunctorComp_comp_id`). On sections, every comparison is a
restriction map of the original module sheaf between equal opens. These are the associativity and
unit laws of restriction as a pseudofunctor on open immersions.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

open Scheme.Modules

variable {X Y Z T : Scheme.{u}}

/-- `restrictFunctor_map_app_restrictAppIso_hom` with the identifications `restrictAppIso`, which
are identities, left implicit: the sections over `U` of a restricted morphism are its sections
over `f ''ᵁ U`. -/
private lemma restrictFunctor_map_app (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}
    (φ : M ⟶ N) (U : X.Opens) : ((Modules.restrictFunctor f).map φ).app U = φ.app (f ''ᵁ U) :=
  restrictFunctor_map_app_restrictAppIso_hom f φ U

/-- The comparison `((M|_Z)|_Y)|_X ≅ M|_X` is independent of the order in which it is built: first
combining the restrictions along `h` and `g`, or first those along `g` and `f`. -/
theorem restrictFunctorComp_associativity (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (fg : X ⟶ Z)
    (gh : Y ⟶ T) (fgh : X ⟶ T) (w₁ : f ≫ g = fg) (w₂ : g ≫ h = gh) (w₃ : fg ≫ h = fgh)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion h]
    [IsOpenImmersion fg] [IsOpenImmersion gh] [IsOpenImmersion fgh] :
    Functor.whiskerRight ((restrictFunctorComp g h).inv ≫ (restrictFunctorCongr w₂).hom)
        (Modules.restrictFunctor f) ≫
      (restrictFunctorComp f gh).inv ≫
        (restrictFunctorCongr (by rw [← w₃, ← w₂, ← w₁, Category.assoc] : f ≫ gh = fgh)).hom =
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (Modules.restrictFunctor h)
        ((restrictFunctorComp f g).inv ≫ (restrictFunctorCongr w₁).hom) ≫
      (restrictFunctorComp fg h).inv ≫ (restrictFunctorCongr w₃).hom := by
  -- On sections over `U`, restriction acts on a morphism as the morphism over the image
  -- (`restrictFunctor_map_app`), and the restriction maps of `M|_Z` are those of `M`
  -- (`restrict_map`). Both sides are then composites of restriction maps of `M` along equalities
  -- of opens, which agree since opens form a poset.
  ext M U : 3
  simp only [Functor.associator_hom_app, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Modules.Hom.comp_app, restrictFunctor_map_app,
    restrictFunctorComp_inv_app_app, restrictFunctorCongr_hom_app_app, Category.id_comp,
    restrict_map, eqToHom_map]
  repeat erw [← Functor.map_comp]
  exact congrArg M.presheaf.map (Subsingleton.elim _ _)

/-- For an open immersion `g : Y ⟶ Z`, the comparison `(M|_Y)|_Y ≅ M|_Y` for `𝟙 Y ≫ g = g` is
Mathlib's identification `Scheme.Modules.restrictFunctorId` of restriction along `𝟙 Y`. -/
theorem restrictFunctorComp_id_comp (g : Y ⟶ Z) [IsOpenImmersion g] :
    (restrictFunctorComp (𝟙 Y) g).inv ≫ (restrictFunctorCongr (Category.id_comp g)).hom =
      Functor.whiskerLeft (Modules.restrictFunctor g) restrictFunctorId.hom ≫
        (Functor.rightUnitor _).hom := by
  ext M U : 3
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Modules.Hom.comp_app, restrictFunctorComp_inv_app_app, restrictFunctorCongr_hom_app_app,
    restrictFunctorId_hom_app_app, restrict_map, eqToHom_map]
  erw [Modules.Hom.id_app, Category.comp_id, ← Functor.map_comp]
  exact congrArg M.presheaf.map (Subsingleton.elim _ _)

/-- For an open immersion `f : X ⟶ Y`, the comparison `(M|_Y)|_X ≅ M|_X` for `f ≫ 𝟙 Y = f` is
the restriction along `f` of Mathlib's identification `Scheme.Modules.restrictFunctorId` of
restriction along `𝟙 Y`. -/
theorem restrictFunctorComp_comp_id (f : X ⟶ Y) [IsOpenImmersion f] :
    (restrictFunctorComp f (𝟙 Y)).inv ≫ (restrictFunctorCongr (Category.comp_id f)).hom =
      Functor.whiskerRight restrictFunctorId.hom (Modules.restrictFunctor f) ≫
        (Functor.leftUnitor _).hom := by
  ext M U : 3
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.leftUnitor_hom_app]
  erw [Category.comp_id ((Functor.whiskerRight _ (Modules.restrictFunctor f)).app M)]
  simp only [Functor.whiskerRight_app, Modules.Hom.comp_app, restrictFunctor_map_app,
    restrictFunctorComp_inv_app_app, restrictFunctorCongr_hom_app_app,
    restrictFunctorId_hom_app_app]
  erw [← Functor.map_comp]
  exact congrArg M.presheaf.map (Subsingleton.elim _ _)

end AlgebraicGeometry.Scheme.Hom

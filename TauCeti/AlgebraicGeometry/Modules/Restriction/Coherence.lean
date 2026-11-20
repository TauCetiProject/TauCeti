/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Associativity of the restriction comparisons

For open immersions `f : X ⟶ Y` and `g : Y ⟶ Z` with `f ≫ g = h`, Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` and
`AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr` compare restricting along `g` and then
along `f` with restricting along `h`. For three composable open immersions, the two ways of
comparing the threefold restriction with restriction along the composite agree
(`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp_associativity`): on sections, every
comparison is a restriction map of the original module sheaf between equal opens. This is the
associativity law of restriction as a pseudofunctor on open immersions.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z T : Scheme.{u}}

/-- The comparison `(M|_Z)|_Y)|_X ≅ M|_X` is independent of the order in which it is built: first
combining the restrictions along `h` and `g`, or first those along `g` and `f`. -/
theorem restrictFunctorComp_associativity (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (fg : X ⟶ Z)
    (gh : Y ⟶ T) (fgh : X ⟶ T) (w₁ : f ≫ g = fg) (w₂ : g ≫ h = gh) (w₃ : fg ≫ h = fgh)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion h]
    [IsOpenImmersion fg] [IsOpenImmersion gh] [IsOpenImmersion fgh] :
    Functor.whiskerRight ((restrictFunctorComp g h).inv ≫ (restrictFunctorCongr w₂).hom)
        (restrictFunctor f) ≫
      (restrictFunctorComp f gh).inv ≫
        (restrictFunctorCongr (by rw [← w₃, ← w₂, ← w₁, Category.assoc] : f ≫ gh = fgh)).hom =
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (restrictFunctor h)
        ((restrictFunctorComp f g).inv ≫ (restrictFunctorCongr w₁).hom) ≫
      (restrictFunctorComp fg h).inv ≫ (restrictFunctorCongr w₃).hom := by
  -- On sections over `U`, both sides are composites of restriction maps of `M` (for the
  -- restricted module `M|_Z` after rewriting with `hr`), hence equal to a single one.
  -- Restriction is a pushforward, so by definition it acts on sections over `U` as the original
  -- morphism over the image `j ''ᵁ U`; Mathlib states this only through `restrictAppIso`.
  have hmap {Y' X' : Scheme.{u}} (j : X' ⟶ Y') [IsOpenImmersion j] {M N : Y'.Modules}
      (φ : M ⟶ N) (U : X'.Opens) : ((restrictFunctor j).map φ).app U = φ.app (j ''ᵁ U) := rfl
  ext M U : 3
  simp only [Functor.associator_hom_app, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Hom.comp_app, hmap, restrictFunctorComp_inv_app_app,
    restrictFunctorCongr_hom_app_app, Category.id_comp]
  have hr {V W : Z.Opens} (p : V = W) : ((restrictFunctor h).obj M).presheaf.map (eqToHom p).op =
      M.presheaf.map (eqToHom (congrArg (h ''ᵁ ·) p)).op := by
    subst p; simp; rfl
  simp only [hr]
  repeat erw [← Functor.map_comp]
  rfl

end AlgebraicGeometry.Scheme.Modules

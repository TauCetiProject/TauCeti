/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.CommAlgCat.Fppf
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
import Mathlib.CategoryTheory.Sites.CartesianClosed
import Mathlib.CategoryTheory.Sites.PreservesLimits
import TauCeti.CategoryTheory.Monoidal.Mod.Basic

/-!
# Equivariance descent for points sheaves

This file extends `TauCeti.Algebra.Category.CommAlgCat.Fppf` with whisker-left epimorphism and
equivariance-descent lemmas for the affine fppf points-sheaf functor
`TauCeti.CommAlgCat.pointsSheafFunctor`.

Specifically:

* Morphisms inducing fppf-locally surjective maps on affine points sheaves stay epimorphic after
  whiskering on the left (`TauCeti.CommAlgCat.epi_whiskerLeft_of_isLocallySurjective`).
* Equivariance under an internal monoid-scheme action descends along equivariant fppf-locally
  surjective morphisms (`TauCeti.CommAlgCat.isModHom_of_isLocallySurjective_comp`).
-/

public section

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace TauCeti.CommAlgCat

universe u

variable {R : Type u} [CommRing R]

/-- If `p : Z ⟶ X` over `Spec R` induces an fppf-locally surjective map on affine points sheaves,
then `W ◁ p : W ⊗ Z ⟶ W ⊗ X` is an epimorphism in `Over (Spec R)` for every `R`-scheme `W`. -/
theorem epi_whiskerLeft_of_isLocallySurjective (W : Over (Spec (CommRingCat.of R)))
    {Z X : Over (Spec (CommRingCat.of R))} (p : Z ⟶ X)
    [Presheaf.IsLocallySurjective (fppfTopology R) ((pointsSheafFunctor R).map p).hom] :
    Epi (W ◁ p) := by
  have : Sheaf.IsLocallySurjective ((pointsSheafFunctor R).map p) :=
    (Sheaf.isLocallySurjective_sheafToPresheaf_map_iff
      ((pointsSheafFunctor R).map p)).2 ‹_›
  have : Epi ((pointsSheafFunctor R).map p) := Sheaf.epi_of_isLocallySurjective _
  let : MonoidalClosed ((CommAlgCat.{u} R)ᵒᵖᵒᵖ ⥤ Type (u + 1)) :=
    FunctorToTypes.monoidalClosed.{0}
  have : Epi (pointsSheaf W ◁ (pointsSheafFunctor R).map p) :=
    (tensorLeft (pointsSheaf W)).map_epi ((pointsSheafFunctor R).map p)
  have : ∀ Y : Over (Spec (CommRingCat.of R)),
      Limits.PreservesLimit (Limits.pair W Y) (pointsSheafFunctor R) := fun _ ↦
    Limits.comp_preservesLimit (GrothendieckTopology.uliftYoneda.{u + 1} _) _
  have heq : (pointsSheafFunctor R).map (W ◁ p) =
      (prodComparisonIso (pointsSheafFunctor R) W Z).hom ≫
        (pointsSheaf W ◁ (pointsSheafFunctor R).map p) ≫
        (prodComparisonIso (pointsSheafFunctor R) W X).inv := by
    rw [← Category.assoc, Iso.eq_comp_inv, prodComparisonIso_hom, prodComparisonIso_hom]
    -- `prodComparison_natural_whiskerLeft` uses `CartesianMonoidalCategory`'s monoidal structure
    -- on `Sheaf`, which is definitionally equal to the `FullSubcategory` monoidal structure used
    -- in `pointsSheaf W ◁ _`.
    exact prodComparison_natural_whiskerLeft (pointsSheafFunctor R) p
  have : Epi ((pointsSheafFunctor R).map (W ◁ p)) := by rw [heq]; infer_instance
  exact (pointsSheafFunctor R).epi_of_epi_map this

/-- Equivariance descends along an equivariant morphism whose map on affine points sheaves is
fppf locally surjective. -/
theorem isModHom_of_isLocallySurjective_comp {G Z X Y : Over (Spec (CommRingCat.of R))}
    [MonObj G] [ModObj G Z] [ModObj G X] [ModObj G Y] (p : Z ⟶ X)
    [Presheaf.IsLocallySurjective (fppfTopology R) ((pointsSheafFunctor R).map p).hom]
    [IsModHom G p] (f : X ⟶ Y) [IsModHom G (p ≫ f)] :
    IsModHom G f :=
  have : Epi (G ◁ p) := epi_whiskerLeft_of_isLocallySurjective G p
  isModHom_of_epi_whiskerLeft_comp p f

end TauCeti.CommAlgCat

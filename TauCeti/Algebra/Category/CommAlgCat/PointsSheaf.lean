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
# Equivariance descent and fppf local surjectivity for points sheaves

This file extends `TauCeti.Algebra.Category.CommAlgCat.Fppf` with local surjectivity, whisker-left
epimorphism, and equivariance-descent lemmas for the affine fppf points-sheaf functor
`TauCeti.CommAlgCat.pointsSheafFunctor`.

Specifically:

* Fppf morphisms of schemes over `Spec R` induce locally surjective maps on affine fppf points
  sheaves (`TauCeti.CommAlgCat.isLocallySurjective_pointsSheafFunctor_map`).
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

/-- **Fppf morphisms induce locally surjective maps on affine points sheaves.** Every
affine-valued point of the target lifts after a faithfully flat, finitely presented extension of
the value algebra. -/
instance isLocallySurjective_pointsSheafFunctor_map
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
    [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left] :
    Presheaf.IsLocallySurjective (fppfTopology R) ((pointsSheafFunctor R).map f).hom := by
  have hcov : Sieve.ofArrows (fun _ : PUnit.{1} ↦ X) (fun _ : PUnit.{1} ↦ f) ∈
      Scheme.fppfTopology.over (Spec (CommRingCat.of R)) Y := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    refine Precoverage.generate_mem_toGrothendieck ?_
    rw [Presieve.ofArrows_pUnit]
    exact f.left.singleton_mem_fppfPrecoverage
  let c : Limits.Cofan (fun _ : PUnit.{1} ↦ uliftYoneda.{u + 1}.obj X) :=
    Limits.Cofan.mk (uliftYoneda.{u + 1}.obj X) (fun _ ↦ 𝟙 _)
  have hc : Limits.IsColimit c :=
    Limits.Cofan.IsColimit.mk c (fun s ↦ s.inj PUnit.unit) (fun _ _ ↦ Category.id_comp _)
      (fun _ m hm ↦ by simpa [c] using hm PUnit.unit)
  have hloc : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (uliftYoneda.{u + 1}.map f) := by
    have h :=
      (GrothendieckTopology.ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_uliftYoneda_map
        (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (fun _ : PUnit.{1} ↦ f) hc).mp hcov
    have hdesc : Limits.Cofan.IsColimit.desc hc (fun _ ↦ uliftYoneda.{u + 1}.map f) =
        uliftYoneda.{u + 1}.map f := by
      simpa [c] using Limits.Cofan.IsColimit.fac hc (fun _ ↦ uliftYoneda.{u + 1}.map f) PUnit.unit
    rwa [hdesc] at h
  have : Sheaf.IsLocallySurjective ((GrothendieckTopology.uliftYoneda.{u + 1}
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))).map f) := hloc
  have hepi : Epi ((GrothendieckTopology.uliftYoneda.{u + 1}
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))).map f) :=
    Sheaf.epi_of_isLocallySurjective _
  have hepi' : Epi ((pointsSheafFunctor R).map f) := by
    dsimp only [pointsSheafFunctor, Functor.comp_map]
    rw [← fppfSheafEquiv_inverse]
    exact (fppfSheafEquiv R (Type (u + 1))).inverse.map_epi _
  exact (Sheaf.isLocallySurjective_iff_epi ((pointsSheafFunctor R).map f)).mpr hepi'

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
    rw [← Category.assoc, Iso.eq_comp_inv, prodComparisonIso_hom, prodComparisonIso_hom,
      prodComparison_natural_whiskerLeft]
    rfl
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

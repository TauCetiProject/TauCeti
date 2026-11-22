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
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Lifting
import TauCeti.CategoryTheory.Monoidal.Mod.Basic
import TauCeti.CategoryTheory.Sites.Continuous

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
  surjective morphisms (`TauCeti.CommAlgCat.isModHom_of_isLocallySurjective_comp`,
  `TauCeti.CommAlgCat.isModHom_of_isLocallySurjective_mul_comp`).
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
    Presheaf.IsLocallySurjective (fppfTopology R) ((pointsSheafFunctor R).map f).hom where
  imageSieve_mem {U} s := by
    obtain ⟨y⟩ := s
    let y' : Spec (CommRingCat.of U.unop) ⟶ Y.left := y.left
    obtain ⟨B, φ, z, hflat, hfp, hz⟩ := f.left.exists_faithfullyFlat_lift y'
    let _ : Algebra R B := (φ.hom.comp (algebraMap R U.unop)).toAlgebra
    let φ' : U.unop ⟶ CommAlgCat.of R B :=
      CommAlgCat.ofHom { φ.hom with commutes' := fun _ ↦ rfl }
    have hbase : z ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
      have hscalar : CommRingCat.ofHom (algebraMap R B) =
          CommRingCat.ofHom (algebraMap R U.unop) ≫ φ := rfl
      rw [hscalar, Spec.map_comp, ← Over.w f, ← Category.assoc, hz, Category.assoc]
      exact congrArg (Spec.map φ ≫ ·) (Over.w y)
    refine GrothendieckTopology.superset_covering _ ?_
      (generate_singleton_op_mem_fppfTopology φ' hflat hfp)
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨⟩
    refine ⟨ULift.up (Over.homMk z hbase), ?_⟩
    rw [pointsSheafFunctor_map_hom_app, pointsSheaf_obj_map]
    refine congrArg ULift.up (Over.OverMorphism.ext ?_)
    dsimp only [Quiver.Hom.unop_op, Functor.op_obj, unop_op]
    rw [Over.comp_left, Over.comp_left, AlgebraicGeometry.algSpec_map_left]
    exact hz

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

/-- Equivariance descends along an fppf-locally surjective morphism out of `G` that intertwines
left multiplication with the target actions. -/
theorem isModHom_of_isLocallySurjective_mul_comp {G X Y : Over (Spec (CommRingCat.of R))}
    [MonObj G] [ModObj G X] [ModObj G Y] (p : G ⟶ X)
    [Presheaf.IsLocallySurjective (fppfTopology R) ((pointsSheafFunctor R).map p).hom]
    (hp : μ[G] ≫ p = G ◁ p ≫ γ[G,X]) (f : X ⟶ Y)
    (hpf : μ[G] ≫ (p ≫ f) = G ◁ (p ≫ f) ≫ γ[G,Y]) :
    IsModHom G f :=
  have : Epi (G ◁ p) := epi_whiskerLeft_of_isLocallySurjective G p
  isModHom_of_epi_whiskerLeft_mul_comp p hp f hpf

end TauCeti.CommAlgCat

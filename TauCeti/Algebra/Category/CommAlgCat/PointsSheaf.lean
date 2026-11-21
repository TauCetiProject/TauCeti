/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.CommAlgCat.Fppf
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Lifting

/-!
# Equivariance descent and fppf local surjectivity for points sheaves

This file extends `TauCeti.Algebra.Category.CommAlgCat.Fppf` with extensionality, local
surjectivity, and equivariance-descent lemmas for the affine fppf points-sheaf functor
`TauCeti.CommAlgCat.pointsSheafFunctor`.

Specifically:

* Morphisms of schemes over `Spec R` are determined by their action on all affine-valued points
  (`TauCeti.CommAlgCat.hom_ext_pointsSheaf`).
* Fppf morphisms of schemes over `Spec R` induce locally surjective maps on affine fppf points
  sheaves (`TauCeti.CommAlgCat.isLocallySurjective_pointsSheafFunctor_map`).
* Equivariance under an internal monoid-scheme action is detected on affine-valued points
  (`TauCeti.CommAlgCat.isModHom_iff_pointsSheaf`) and descends along equivariant fppf-locally
  surjective morphisms (`TauCeti.CommAlgCat.isModHom_of_isLocallySurjective_comp`,
  `TauCeti.CommAlgCat.isModHom_of_isLocallySurjective_mul_comp`).
-/

public section

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace TauCeti.CommAlgCat

universe u

variable {R : Type u} [CommRing R]

/-- Two morphisms of schemes over `Spec R` are equal if they induce the same map on all
affine-valued points. -/
theorem hom_ext_pointsSheaf {X Y : Over (Spec (CommRingCat.of R))} {f g : X ⟶ Y}
    (h : ∀ (A : CommAlgCat.{u} R) (p : (algSpec (CommRingCat.of R)).obj (op A) ⟶ X),
      p ≫ f = p ≫ g) :
    f = g := by
  apply (pointsSheafFunctor R).map_injective
  ext A ⟨p⟩
  exact congrArg ULift.up (h A.unop.unop p)

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
    exact congrArg ULift.up (Over.OverMorphism.ext hz)

/-- Equivariance of a scheme morphism over `Spec R` is detected on all affine-valued points. -/
theorem isModHom_iff_pointsSheaf {G X Y : Over (Spec (CommRingCat.of R))}
    [MonObj G] [ModObj G X] [ModObj G Y] (f : X ⟶ Y) :
    IsModHom G f ↔
      ∀ (A : CommAlgCat.{u} R) (g : (algSpec (CommRingCat.of R)).obj (op A) ⟶ G)
        (x : (algSpec (CommRingCat.of R)).obj (op A) ⟶ X),
        (g • x) ≫ f = g • (x ≫ f) := by
  refine ⟨fun _ A g x ↦ IsModHom.map_smul f g x, fun h ↦ ⟨?_⟩⟩
  apply hom_ext_pointsSheaf
  intro A p
  have hp : p = lift (p ≫ fst G X) (p ≫ snd G X) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rw [hp, ← Category.assoc, ← Hom.smul_def, h, Hom.smul_def, ← lift_whiskerLeft_assoc]
  rfl

/-- Equivariance descends along an equivariant morphism whose map on affine points sheaves is
fppf locally surjective. -/
theorem isModHom_of_isLocallySurjective_comp {G Z X Y : Over (Spec (CommRingCat.of R))}
    [MonObj G] [ModObj G Z] [ModObj G X] [ModObj G Y] (p : Z ⟶ X)
    [Presheaf.IsLocallySurjective (fppfTopology R) ((pointsSheafFunctor R).map p).hom]
    [IsModHom G p] (f : X ⟶ Y) [IsModHom G (p ≫ f)] :
    IsModHom G f := by
  rw [isModHom_iff_pointsSheaf]
  intro A g x
  let x' : (pointsSheaf X).obj.obj (op (op A)) := ULift.up x
  have hcov := Presheaf.imageSieve_mem (fppfTopology R) ((pointsSheafFunctor R).map p).hom x'
  have heq : (ULift.up ((g • x) ≫ f) : (pointsSheaf Y).obj.obj (op (op A))) =
      ULift.up (g • (x ≫ f)) := by
    refine (((isSheaf_iff_isSheaf_of_type _ _).mp (pointsSheaf Y).property).isSeparated _ hcov).ext
      fun B φ hφ ↦ ?_
    obtain ⟨⟨h⟩, hh⟩ := hφ
    have hx : h ≫ p = (algSpec (CommRingCat.of R)).map φ ≫ x := congrArg ULift.down hh
    rw [pointsSheaf_obj_map, pointsSheaf_obj_map, Quiver.Hom.unop_op]
    apply congrArg ULift.up
    rw [← Category.assoc, ModObj.comp_smul, ← hx, ← IsModHom.map_smul p, Category.assoc,
      IsModHom.map_smul (p ≫ f), ← Category.assoc, hx, Category.assoc, ← ModObj.comp_smul]
  exact congrArg ULift.down heq

/-- Equivariance descends along an fppf-locally surjective morphism out of `G` that intertwines
left multiplication with the target actions. -/
theorem isModHom_of_isLocallySurjective_mul_comp {G X Y : Over (Spec (CommRingCat.of R))}
    [MonObj G] [ModObj G X] [ModObj G Y] (p : G ⟶ X)
    [Presheaf.IsLocallySurjective (fppfTopology R) ((pointsSheafFunctor R).map p).hom]
    (hp : μ[G] ≫ p = G ◁ p ≫ γ[G,X]) (f : X ⟶ Y)
    (hpf : μ[G] ≫ (p ≫ f) = G ◁ (p ≫ f) ≫ γ[G,Y]) :
    IsModHom G f := by
  let _ : ModObj G G := ModObj.regular G
  have _ : IsModHom G p := ⟨hp⟩
  have _ : IsModHom G (p ≫ f) := ⟨hpf⟩
  exact isModHom_of_isLocallySurjective_comp p f

end TauCeti.CommAlgCat

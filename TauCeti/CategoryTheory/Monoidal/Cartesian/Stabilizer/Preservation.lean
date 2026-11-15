/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Cartesian.Stabilizer.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Preservation of orbit fibres and stabilizers

A strong monoidal functor between cartesian monoidal categories that preserves the
orbit-fibre pullback carries that fibre to the fibre of the transported action.
For stabilizers the comparison is an isomorphism of group objects, compatible
with their inclusions. In particular this comparison keeps infinitesimal
stabilizers when applied to base change of schemes; it is not a comparison of
sets of rational points.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 7, scheme-theoretic stabilizers.
-/

public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.Obj
open TauCeti

namespace CategoryTheory.Functor

section OrbitFiber

open TauCeti.orbitFiber

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] (G : C) {X : C} [MonObj G] [ModObj G X]
  (x y : 𝟙_ C ⟶ X) [HasPullback (orbitMap G x) y]
  [PreservesLimit (cospan (orbitMap G x) y) F]

attribute [local instance] Functor.modObjObj

/-- The image of the defining orbit-fibre square, with its terminal vertex
identified by the monoidal unit comparison. -/
theorem isPullback_map_orbitFiber :
    IsPullback (F.map (incl G x y)) (toUnit (F.obj (orbitFiber G x y)))
      (orbitMap (F.obj G) (Functor.LaxMonoidal.ε F ≫ F.map x))
      (Functor.LaxMonoidal.ε F ≫ F.map y) := by
  apply ((orbitFiber.isPullback G x y).map F).of_iso
    (Iso.refl _) (Iso.refl _) (asIso (Functor.LaxMonoidal.ε F)).symm (Iso.refl _)
  · simp
  · exact toUnit_unique _ _
  · simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp] using
      F.map_orbitMap G X x
  · simp

variable [HasPullback (orbitMap (F.obj G) (Functor.LaxMonoidal.ε F ≫ F.map x))
  (Functor.LaxMonoidal.ε F ≫ F.map y)]

/-- Preservation of an orbit fibre, including its map into the acting monoid. -/
def mapOrbitFiberIso : F.obj (orbitFiber G x y) ≅
    orbitFiber (F.obj G) (Functor.LaxMonoidal.ε F ≫ F.map x)
      (Functor.LaxMonoidal.ε F ≫ F.map y) :=
  (isPullback_map_orbitFiber F G x y).isoIsPullback _ _
    (orbitFiber.isPullback (F.obj G) (Functor.LaxMonoidal.ε F ≫ F.map x)
      (Functor.LaxMonoidal.ε F ≫ F.map y))

/-- The forward fibre comparison respects the inclusions. -/
@[reassoc (attr := simp)]
theorem mapOrbitFiberIso_hom_incl :
    (mapOrbitFiberIso F G x y).hom ≫ incl (F.obj G) (Functor.LaxMonoidal.ε F ≫ F.map x)
      (Functor.LaxMonoidal.ε F ≫ F.map y) = F.map (incl G x y) :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The inverse fibre comparison respects the inclusions. -/
@[reassoc (attr := simp)]
theorem mapOrbitFiberIso_inv_incl :
    (mapOrbitFiberIso F G x y).inv ≫ F.map (incl G x y) =
      incl (F.obj G) (Functor.LaxMonoidal.ε F ≫ F.map x)
        (Functor.LaxMonoidal.ε F ≫ F.map y) :=
  IsPullback.isoIsPullback_inv_fst _ _ _ _

/-- The inclusion uniquely characterizes the forward comparison. -/
theorem mapOrbitFiberIso_hom_unique
    (a : F.obj (orbitFiber G x y) ⟶
      orbitFiber (F.obj G) (Functor.LaxMonoidal.ε F ≫ F.map x)
        (Functor.LaxMonoidal.ε F ≫ F.map y))
    (ha : a ≫ incl (F.obj G) (Functor.LaxMonoidal.ε F ≫ F.map x)
      (Functor.LaxMonoidal.ε F ≫ F.map y) = F.map (incl G x y)) :
    a = (mapOrbitFiberIso F G x y).hom := by
  apply (cancel_mono (incl (F.obj G) (Functor.LaxMonoidal.ε F ≫ F.map x)
    (Functor.LaxMonoidal.ε F ≫ F.map y))).mp
  rw [ha, mapOrbitFiberIso_hom_incl]

end OrbitFiber

section Stabilizer

open TauCeti.stabilizer

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] (G : C) {X : C} [GrpObj G] [ModObj G X]
  (x : 𝟙_ C ⟶ X) [HasPullback (orbitMap G x) x]
  [PreservesLimit (cospan (orbitMap G x) x) F]

attribute [local instance] Functor.modObjObj

variable [HasPullback (orbitMap (F.obj G) (Functor.LaxMonoidal.ε F ≫ F.map x))
  (Functor.LaxMonoidal.ε F ≫ F.map x)]

/-- The orbit-fibre comparison at the base point is a morphism of group objects.
Its inverse is therefore a group-object morphism as well. -/
instance isMonHom_mapOrbitFiberIso_hom : IsMonHom (mapOrbitFiberIso F G x x).hom where
  one_hom := by
    apply (cancel_mono (incl (F.obj G) (Functor.LaxMonoidal.ε F ≫ F.map x))).mp
    simp only [Category.assoc, mapOrbitFiberIso_hom_incl, IsMonHom.one_hom]
  mul_hom := by
    apply (cancel_mono (incl (F.obj G) (Functor.LaxMonoidal.ε F ≫ F.map x))).mp
    simp only [Category.assoc, mapOrbitFiberIso_hom_incl, IsMonHom.mul_hom]
    rw [← Category.assoc, tensorHom_comp_tensorHom]
    simp

end Stabilizer

end CategoryTheory.Functor

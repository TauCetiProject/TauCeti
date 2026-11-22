/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import TauCeti.AlgebraicGeometry.Scheme.SpecOver

/-!
# Affine-point detection of equivariance for scheme actions

A morphism `f : X ⟶ Y` between schemes over `Spec R` carrying actions of a monoid scheme `G`
over `Spec R` is equivariant if and only if it commutes with the action on all affine-valued
points `(algSpec (CommRingCat.of R)).obj (op A) ⟶ G` and
`(algSpec (CommRingCat.of R)).obj (op A) ⟶ X`.

This follows directly from the relative affine-point extensionality criterion
`TauCeti.AlgebraicGeometry.hom_ext_of_forall_algSpec`, without any Grothendieck topology or
flat-lifting machinery.

## Main results

* `TauCeti.SchemeAction.isModHom_iff_forall_algSpec`: equivariance over `Spec R` is detected on
  all affine-valued points.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace TauCeti.SchemeAction

universe u

/-- Equivariance of a scheme morphism over `Spec R` is detected on all affine-valued points. -/
theorem isModHom_iff_forall_algSpec {R : Type u} [CommRing R]
    {G X Y : Over (Spec (CommRingCat.of R))}
    [MonObj G] [ModObj G X] [ModObj G Y] (f : X ⟶ Y) :
    IsModHom G f ↔
      ∀ (A : CommAlgCat.{u} R) (g : (algSpec (CommRingCat.of R)).obj (op A) ⟶ G)
        (x : (algSpec (CommRingCat.of R)).obj (op A) ⟶ X),
        (g • x) ≫ f = g • (x ≫ f) := by
  refine ⟨fun _ A g x ↦ IsModHom.map_smul f g x, fun h ↦ ⟨?_⟩⟩
  apply TauCeti.AlgebraicGeometry.hom_ext_of_forall_algSpec
  intro A p
  have hp : p = lift (p ≫ fst G X) (p ≫ snd G X) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rw [hp, ← Category.assoc, ← Hom.smul_def, h, Hom.smul_def, ← lift_whiskerLeft_assoc]
  rfl

end TauCeti.SchemeAction

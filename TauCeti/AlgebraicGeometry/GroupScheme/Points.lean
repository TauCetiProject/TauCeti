/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# Algebra-valued points of group schemes

Restricting group-valued Yoneda along relative spectrum gives a group-valued functor on
commutative algebras. The group law is supplied by the native group object, rather than a
chosen coordinate presentation. The value-algebra map is relative-spectrum precomposition.

This is `CategoryTheory.yonedaGrp` restricted along relative spectrum. It is defined
for arbitrary group schemes, without affineness, smoothness or finite type.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace TauCeti

universe u

namespace GroupScheme

/-- The group-valued functor of algebra-valued points of a group scheme over `Spec R`.
A value-algebra morphism acts by precomposition with its relative spectrum map. -/
noncomputable abbrev algebraPointsFunctor (R : Type u) [CommRing R]
    (G : Grp (Over (Spec (CommRingCat.of R)))) : CommAlgCat.{u} R ⥤ GrpCat.{u} :=
  (opOp (CommAlgCat.{u} R) ⋙ (algSpec (CommRingCat.of R)).op) ⋙ yonedaGrp.obj G

/-- The value of the algebra-points functor is the group of relative scheme morphisms. -/
theorem algebraPointsFunctor_obj (R : Type u) [CommRing R]
    (G : Grp (Over (Spec (CommRingCat.of R)))) (A : CommAlgCat.{u} R) :
    (algebraPointsFunctor R G).obj A =
      GrpCat.of ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶ G.X) :=
  (rfl)

/-- The map on algebra-valued points is precomposition with relative spectrum. -/
theorem algebraPointsFunctor_map_apply (R : Type u) [CommRing R]
    (G : Grp (Over (Spec (CommRingCat.of R)))) {A B : CommAlgCat.{u} R} (f : A ⟶ B)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶ G.X) :
    (algebraPointsFunctor R G).map f p =
      (Spec.map (CommRingCat.ofHom f.hom.toRingHom)).asOver (Spec (CommRingCat.of R)) ≫ p :=
  (rfl)

end GroupScheme

end TauCeti

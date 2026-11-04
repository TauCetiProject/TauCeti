/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# The dual of a cube of modules

A commutative cube of `R`-modules indexed by a finite type `ι` is a functor
`F : Finset ι ⥤ ModuleCat R`. Taking duals reverses every edge, and complementation
`S ↦ Sᶜ` reverses the inclusion order of the vertices, so the two reversals compose to a cube
pointing in the original direction: the *dual cube* `F.dualCube` has vertex `Module.Dual R (F(Sᶜ))`
at `S`, and along an inclusion `S ⊆ T` it is the transpose of the map of `F` along `Tᶜ ⊆ Sᶜ`.
Its height-`r` vertices are the duals of the height-`(#ι - r)` vertices of `F`.

This is the cube of the dual complex: mirroring a link diagram exchanges the two smoothings at
every crossing, and the Frobenius pairing identifies the cube of resolutions of the mirror with
the dual cube of the cube of resolutions of the diagram
(`TauCeti.PDCode.mirrorResolutionCubeIso`).

## Main definitions

* `CategoryTheory.Functor.dualCube F`: the dual cube of `F`, with maps characterized by
  `Functor.dualCube_map_hom`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §7.
-/

public section

open CategoryTheory Finset

universe w u

namespace CategoryTheory.Functor

variable {ι : Type w} [Fintype ι] [DecidableEq ι] {R : Type u} [CommRing R]
  (F : Finset ι ⥤ ModuleCat.{u} R)

/-- The **dual cube** of a cube of modules `F`: its vertex `S` is the dual of the complementary
vertex `F(Sᶜ)`, and along an inclusion `S ⊆ T` it is the transpose of the map of `F` along the
reversed inclusion `Tᶜ ⊆ Sᶜ`. It is reducible so that an element of a vertex is a linear form
on the complementary vertex of `F`. -/
abbrev dualCube : Finset ι ⥤ ModuleCat.{u} R where
  obj S := ModuleCat.of R (Module.Dual R (F.obj Sᶜ))
  map f := ModuleCat.ofHom (F.map (homOfLE (compl_subset_compl.2 (leOfHom f)))).hom.dualMap
  map_id S := by
    ext φ x
    simp [homOfLE_refl]
  map_comp f g := by
    ext φ x
    simp [← ModuleCat.comp_apply, ← F.map_comp]

/-- The vertex `S` of the dual cube is the dual of the vertex `Sᶜ` of the cube. -/
theorem dualCube_obj (S : Finset ι) :
    F.dualCube.obj S = ModuleCat.of R (Module.Dual R (F.obj Sᶜ)) :=
  (rfl)

/-- Along an inclusion `S ⊆ T`, the dual cube is the transpose of the map of the cube along
`Tᶜ ⊆ Sᶜ`: it precomposes a linear form on `F(Sᶜ)` with that map. -/
theorem dualCube_map_hom {S T : Finset ι} (f : S ⟶ T) :
    (F.dualCube.map f).hom = (F.map (homOfLE (compl_subset_compl.2 (leOfHom f)))).hom.dualMap :=
  (rfl)

/-- Along an inclusion `S ⊆ T`, the dual cube precomposes a linear form on `F(Sᶜ)` with the map
of the cube along `Tᶜ ⊆ Sᶜ`. -/
theorem dualCube_map_hom_apply {S T : Finset ι} (f : S ⟶ T) (φ : F.dualCube.obj S)
    (x : F.obj Tᶜ) :
    (F.dualCube.map f).hom φ x = φ ((F.map (homOfLE (compl_subset_compl.2 (leOfHom f)))).hom x) :=
  (rfl)

end CategoryTheory.Functor

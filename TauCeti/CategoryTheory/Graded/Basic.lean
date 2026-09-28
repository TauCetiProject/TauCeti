/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.GradedObject

/-!
# Graded linear quivers

A *graded linear quiver* over a commutative ring `R` is a collection of objects such that every
ordered pair of objects carries an `R`-module of morphisms with an internal `ℤ`-grading.  That is
the whole of the data: there is no composition, no identity, and no law relating the morphisms of
different pairs of objects.

The higher theories of this library are built on such a quiver rather than assumed in it.  A
differential graded category is a graded linear quiver together with a differential of degree one
on each hom module, and an `A∞` category is a graded linear quiver together with operations `mₙ`
of degree `2 - n` in arity `n` for `n ≥ 1`.  Composition is the operation `m₂` of that structure
and not a datum of the quiver, so a differential graded category is the subcase of an `A∞`
category in which `m₂` is a strictly unital and strictly associative composition and the operations
`mₙ` vanish for `n ≥ 3`.

The grading is internal: the morphisms of degree `n` are the submodule `grHom X Y n` of the hom
module `X → Y`, and the submodule family is an internal direct sum, so every morphism is a finite
and uniquely determined sum of morphisms of definite degrees, its degree-`n` component being
`DirectSum.decompose` of the grading, as in `TauCeti.InternalGrading`.  The same data is a
`CategoryTheory.GradedObject ℤ (ModuleCat R)`, which presents the homogeneous modules separately,
through `TauCeti.GradedLinearQuiver.gradedHom` and the constructor
`TauCeti.GradedLinearQuiver.ofGradedHom`;
`TauCeti.InternalGrading.toGradedObject` and `TauCeti.InternalGrading.ofGradedObject` convert
between the two presentations.

## Main definitions

* `TauCeti.GradedLinearQuiver`: a graded linear quiver over a commutative ring.
* `TauCeti.GradedLinearQuiver.ofGradedHom`: the graded linear quiver of a graded object of hom
modules.
* `TauCeti.GradedLinearQuiver.grHom`: the morphisms `X → Y` of a fixed degree.
* `TauCeti.GradedLinearQuiver.gradedHom`: the hom modules of a graded linear quiver as a graded
object.
* `TauCeti.GradedLinearQuiver.grHomReindex`: a homogeneous morphism recorded at another degree.

## Main results

* `TauCeti.GradedLinearQuiver.eq_zero_of_mem_piece_of_ne`: a nonzero morphism is homogeneous of at
most one degree, so that a degree together with its homogeneous submodule determines a morphism.

## References

* E. Getzler and J. D. Jones, *A-infinity algebras and the cyclic bar complex*, *Illinois Journal
of Mathematics* 34 (1990), 256-283, Section 1: `ℤ`-graded objects and their homogeneous elements.
* J. Mu, A. Yao, N. Voss and M. David, *A-infinity grading data*,
[mathlib4#40984](https://github.com/leanprover-community/mathlib4/pull/40984), whose
`RLinearGradedQuiver` is a graded `R`-module of morphisms between each pair of objects, with
neither composition nor identity.
-/

public section

open scoped DirectSum

namespace TauCeti

universe u v

/-- A **graded linear quiver** over a commutative ring `R`: a collection of objects `C` with, for
each ordered pair of objects, an `R`-module `homModule X Y` of morphisms carrying an internal `ℤ`
grading `grading X Y`.

There is no composition and no identity, and no law relating the data of different pairs of
objects: they belong to the structure which a graded linear quiver carries, such as the `A∞`
structure whose operation `m₂` is the composition.

The base ring is a commutative ring, as for the differential graded categories of `TauCeti`. -/
class GradedLinearQuiver (R : Type v) [CommRing R] (C : Type u) where
  /-- The `R`-module of morphisms from `X` to `Y`. -/
  homModule : C → C → ModuleCat.{v} R
  /-- The internal `ℤ`-grading of the hom module from `X` to `Y`. -/
  grading : (X Y : C) → InternalGrading R (homModule X Y)

namespace GradedLinearQuiver

variable (R : Type v) [CommRing R] {C : Type u}

/-- The graded linear quiver whose hom modules are the components of a graded object: the total
module of morphisms `X → Y` is the external direct sum of the components of `F X Y`. -/
@[instance_reducible]
noncomputable def ofGradedHom (F : (X Y : C) → CategoryTheory.GradedObject ℤ (ModuleCat.{v} R)) :
    GradedLinearQuiver R C where
  homModule X Y := ModuleCat.of R (⨁ p, F X Y p)
  grading X Y := InternalGrading.ofGradedObject R (F X Y)

variable [GradedLinearQuiver R C] {X Y : C}

/-- The morphisms from `X` to `Y` of cohomological degree `n`, as the `R`-module
`(grading X Y).piece n`. -/
abbrev grHom (X Y : C) (n : ℤ) : Type v :=
  ↥((grading (R := R) X Y).piece n : Submodule R (homModule (R := R) X Y))

/-- The hom modules of a graded linear quiver as a graded object: the component in the degree `n` is
the module of the morphisms of that degree. -/
abbrev gradedHom (X Y : C) : CategoryTheory.GradedObject ℤ (ModuleCat.{v} R) :=
  (grading (R := R) X Y).toGradedObject

/-- Record a morphism of degree `n` as a morphism of degree `k`, along an equation `h : n = k` of
degrees.  The underlying morphism is unchanged. -/
def grHomReindex {n k : ℤ} (h : n = k) (f : grHom R X Y n) : grHom R X Y k :=
  ⟨f, by rw [← h]; exact f.property⟩

/-- Reindexing a homogeneous morphism does not change the underlying morphism. -/
@[simp, grind =]
theorem val_grHomReindex (h : n = k) (f : grHom R X Y n) :
    (grHomReindex (R := R) (C := C) h f).1 = f.1 := by
  rw [grHomReindex]

/-- A morphism which is homogeneous of two distinct degrees is zero.  Equivalently, a nonzero
morphism is homogeneous of at most one degree. -/
theorem eq_zero_of_mem_piece_of_ne (R : Type v) [CommRing R] {C : Type u}
    [GradedLinearQuiver R C] {X Y : C} {n m : ℤ} {f : ↥(homModule (R := R) X Y)} (hne : n ≠ m)
    (hn : f ∈ (grading (R := R) X Y).piece n)
    (hm : f ∈ (grading (R := R) X Y).piece m) : f = 0 := by
  let A := (grading (R := R) X Y).piece
  have h : DirectSum.IsInternal A := (grading (R := R) X Y).isInternal
  have happ : (⟨f, hn⟩ : A n) = 0 := by
    rw [← h.ofBijective_coeLinearMap_of_mem hn,
      ← h.ofBijective_coeLinearMap_of_mem_ne (i := m) (j := n) hne.symm hm]
  exact congrArg (fun x : A n => (x : ↥(homModule (R := R) X Y))) happ

/-! ### An example

A graded linear quiver with two objects, whose morphisms form a module with a copy of `R` in each
of the degrees `0` and `1` and no morphism in any other degree. -/

section Example

/-- The two objects of `twoObjQuiver`. -/
inductive TwoObj where
  /-- The first object. -/
  | one
  /-- The second object. -/
  | two

/-- The graded module of morphisms of `twoObjQuiver`: a copy of `R` in each of the degrees `0` and
`1`, and the zero module in every other degree. -/
noncomputable def twoObjModule (R : Type v) [CommRing R] :
    CategoryTheory.GradedObject ℤ (ModuleCat.{v} R) :=
  fun p => if p = 0 then ModuleCat.of R R else
    if p = 1 then ModuleCat.of R R else ModuleCat.of R PUnit

/-- A graded linear quiver with two objects, whose hom modules are the components of
`twoObjModule`. -/
noncomputable instance twoObjQuiver (R : Type v) [CommRing R] : GradedLinearQuiver R TwoObj :=
  ofGradedHom (R := R) fun _ _ => twoObjModule R

/-- The morphisms from the first to the second object of `twoObjQuiver` form a copy of `R` in the
degree `0`. -/
theorem twoObjModule_zero (R : Type v) [CommRing R] : twoObjModule R 0 = ModuleCat.of R R := by
  simp [twoObjModule]

/-- The morphisms from the first to the second object of `twoObjQuiver` form a copy of `R` in the
degree `1`. -/
theorem twoObjModule_one (R : Type v) [CommRing R] : twoObjModule R 1 = ModuleCat.of R R := by
  simp [twoObjModule]

/-- The morphisms from the first to the second object of `twoObjQuiver` are the zero module in every
degree other than `0` and `1`. -/
theorem twoObjModule_ne (R : Type v) [CommRing R] {p : ℤ} (h0 : p ≠ 0) (h1 : p ≠ 1) :
    twoObjModule R p = ModuleCat.of R PUnit := by
  simp [twoObjModule, h0, h1]

end Example

end GradedLinearQuiver

end TauCeti

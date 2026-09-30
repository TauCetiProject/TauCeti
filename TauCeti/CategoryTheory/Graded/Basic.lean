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
differential graded category is a graded linear quiver together with a graded composition and
identities which are unital and associative, and an `A∞` category is a graded linear quiver
together with operations `mₙ` of degree `2 - n` in arity `n` for `n ≥ 1`.  Composition is the
operation `m₂` of that structure and not a datum of the quiver, so a differential graded category
is the subcase of an `A∞` category in which `m₂` is a strictly unital and strictly
associative composition and the operations `mₙ` vanish for `n ≥ 3`.  The differential is part
of that structure rather than of the quiver as well: it is the degree-one operation `d = m₁`,
and a differential graded category requires that it square to zero and be a graded derivation of
the composition, `d (f ∘ g) = d f ∘ g + (-1)^{|f|} f ∘ d g` for morphisms `f` and `g` of
degrees `|f|` and `|g|`.

The grading is internal: the morphisms of degree `n` are the submodule `grHom X Y n` of the hom
module `X → Y`, and the submodule family is an internal direct sum, so every morphism is a finite
and uniquely determined sum of morphisms of definite degrees, its degree-`n` component being
`DirectSum.decompose` of the grading, as in `TauCeti.InternalGrading`.  The same data is a
`CategoryTheory.GradedObject ℤ (ModuleCat R)`, which presents the homogeneous modules separately,
through `TauCeti.GradedLinearQuiver.gradedHom` and the constructor
`TauCeti.GradedLinearQuiver.ofGradedHom`;
`TauCeti.InternalGrading.toGradedObject` and `TauCeti.InternalGrading.ofGradedObject` convert
between the two presentations, and `TauCeti.InternalGrading.ofGradedObjectToGradedObjectIso`
recovers the components `F X Y` of `ofGradedHom F` from its grading, degree by degree.

## Main definitions

* `TauCeti.GradedLinearQuiver`: a graded linear quiver over a commutative ring.
* `TauCeti.GradedLinearQuiver.ofGradedHom`: the graded linear quiver of a graded object of hom
  modules.
* `TauCeti.GradedLinearQuiver.grHom`: the morphisms `X → Y` of a fixed degree.
* `TauCeti.GradedLinearQuiver.gradedHom`: the hom modules of a graded linear quiver as a graded
  object.
* `TauCeti.GradedLinearQuiver.grHomReindex`: a homogeneous morphism recorded at another degree.

## Main results

* `TauCeti.GradedLinearQuiver.homModule_ofGradedHom`: the hom module of `ofGradedHom F`, the
  external direct sum of the components of `F X Y`.
* `TauCeti.GradedLinearQuiver.grading_ofGradedHom`: the internal grading of that hom module, the
  canonical grading of the external direct sum of the components of `F X Y`.
* `TauCeti.GradedLinearQuiver.grHomReindex_refl` and
  `TauCeti.GradedLinearQuiver.grHomReindex_trans`: a homogeneous morphism reindexed by an equation
  of degrees is the morphism itself, recorded at the new degree, and successive reindexings compose.

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

universe u v w

/-- A **graded linear quiver** over a commutative ring `R`: a collection of objects `C` with, for
each ordered pair of objects, an `R`-module `homModule X Y` of morphisms carrying an internal `ℤ`
grading `grading X Y`.

There is no composition and no identity, and no law relating the data of different pairs of
objects: they belong to the structure which a graded linear quiver carries, such as the `A∞`
structure whose operation `m₂` is the composition.

The base ring is a commutative ring, as for the differential graded categories of `TauCeti`. -/
class GradedLinearQuiver (R : Type w) [CommRing R] (C : Type u) where
  /-- The `R`-module of morphisms from `X` to `Y`. -/
  homModule : C → C → ModuleCat.{v} R
  /-- The internal `ℤ`-grading of the hom module from `X` to `Y`. -/
  grading : (X Y : C) → InternalGrading R (homModule X Y)

namespace GradedLinearQuiver

variable (R : Type w) [CommRing R] {C : Type u}

/-- The graded linear quiver whose hom modules are the components of a graded object: the total
module of morphisms `X → Y` is the external direct sum of the components of `F X Y`.

The two fields of this quiver are `homModule_ofGradedHom` and `grading_ofGradedHom`, and
`InternalGrading.ofGradedObjectToGradedObjectIso` recovers the graded object `F` itself, degree by
degree, from the second of them. -/
-- The body is exposed, since the module system hides the body of a `def` from the statements of
-- the other exported declarations of a module, and the two field equations could not be stated
-- without it.
@[instance_reducible, expose]
noncomputable def ofGradedHom (F : (X Y : C) → CategoryTheory.GradedObject ℤ (ModuleCat.{v} R)) :
    GradedLinearQuiver R C where
  homModule X Y := ModuleCat.of R (⨁ p, F X Y p)
  grading X Y := InternalGrading.ofGradedObject R (F X Y)

variable {F : (X Y : C) → CategoryTheory.GradedObject ℤ (ModuleCat.{v} R)}

/-- The hom module between two objects of the graded linear quiver `ofGradedHom F`: the external
direct sum of the components of `F X Y`. -/
@[simp]
theorem homModule_ofGradedHom (X Y : C) :
    (ofGradedHom (R := R) (C := C) F).homModule X Y = ModuleCat.of R (⨁ p, F X Y p) :=
  rfl

/-- The internal grading between two objects of the graded linear quiver `ofGradedHom F` is the
canonical grading of the external direct sum of the components of `F X Y`. -/
@[simp]
theorem grading_ofGradedHom (X Y : C) :
    (ofGradedHom (R := R) (C := C) F).grading X Y = InternalGrading.ofGradedObject R (F X Y) :=
  rfl

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

/-- A homogeneous morphism reindexed by reflexivity is the morphism itself. -/
@[simp]
theorem grHomReindex_refl (f : grHom R X Y n) : grHomReindex (R := R) (C := C) rfl f = f := by
  rw [grHomReindex]

/-- A homogeneous morphism reindexed successively along two equations of degrees is the morphism
reindexed along their composition. -/
@[simp]
theorem grHomReindex_trans {n k l : ℤ} (h₁ : n = k) (h₂ : k = l) (f : grHom R X Y n) :
    grHomReindex (R := R) (C := C) (k := l) h₂
        (grHomReindex (R := R) (C := C) (k := k) h₁ f)
      = grHomReindex (R := R) (C := C) (k := l) (h₁.trans h₂) f := by
  simp only [grHomReindex]

/-! ### An example

A graded linear quiver with two objects, carrying a copy of `R` in each of the degrees `0` and `1`
and no morphism in any other degree.  The same graded object of components is assigned to every
ordered pair of objects, so the total hom module of such a pair is the external direct sum
`⨁ p, twoObjModule R p`.  The ring of the example is taken in the universe of the hom modules,
so that a copy of `R` is one of their components. -/

/-- The two objects of the example. -/
private inductive TwoObj where
  /-- The first object. -/
  | one
  /-- The second object. -/
  | two

/-- The graded object of degree components assigned to every ordered pair of the two example
objects: a copy of `R` in each of the degrees `0` and `1`, and the zero module in every other
degree. -/
private noncomputable def twoObjModule (R : Type v) [CommRing R] :
    CategoryTheory.GradedObject ℤ (ModuleCat.{v} R) :=
  fun p => if p = 0 then ModuleCat.of R R else
    if p = 1 then ModuleCat.of R R else ModuleCat.of R PUnit

/-- A graded linear quiver with two objects, a copy of `R` in each of the degrees `0` and `1` of the
hom module of every ordered pair of objects, and no morphism in any other degree. -/
private noncomputable instance twoObjQuiver (R : Type v) [CommRing R] :
    GradedLinearQuiver R TwoObj :=
  ofGradedHom (R := R) fun _ _ => twoObjModule R

/-- The degree-`0` component assigned to every ordered pair of the two example objects is a copy of
`R`. -/
private theorem twoObjModule_zero (R : Type v) [CommRing R] :
    twoObjModule R 0 = ModuleCat.of R R := by
  simp [twoObjModule]

/-- The degree-`1` component assigned to every ordered pair of the two example objects is a copy of
`R`. -/
private theorem twoObjModule_one (R : Type v) [CommRing R] :
    twoObjModule R 1 = ModuleCat.of R R := by
  simp [twoObjModule]

/-- Every other degree component assigned to every ordered pair of the two example objects is the
zero module. -/
private theorem twoObjModule_eq_punit_of_ne_zero_of_ne_one (R : Type v) [CommRing R]
    {p : ℤ} (h0 : p ≠ 0) (h1 : p ≠ 1) :
    twoObjModule R p = ModuleCat.of R PUnit := by
  simp [twoObjModule, h0, h1]

end GradedLinearQuiver

end TauCeti

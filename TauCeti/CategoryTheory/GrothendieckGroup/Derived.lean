/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Abelian
public import TauCeti.CategoryTheory.GrothendieckGroup.Triangulated
public import TauCeti.Algebra.Homology.DerivedCategory.Bounded

/-!
# The canonical map from abelian K₀ to bounded derived K₀

For an essentially small abelian category `A` whose bounded derived category is essentially small,
this file constructs the canonical additive homomorphism

```text
K₀(A) ⟶ K₀(Dᵇ(A)).
```

It sends `[X]` to the class of the complex with `X` in degree zero. A short exact sequence in `A`
gives a distinguished triangle between the corresponding degree-zero complexes in `Dᵇ(A)`, so this
assignment respects the defining relations of abelian `K₀`.

Classically this map is an isomorphism, with inverse given by the alternating sum of cohomology
classes; that inverse is not constructed here.

## Main definitions

* `TauCeti.AbelianK0.toBoundedDerivedK0` is induced by the degree-zero embedding into the bounded
  derived category.

## Main results

* `TauCeti.TriangulatedK0.of_singleFunctor_shortExact` is the triangulated `K₀` relation between
  the degree-zero objects of a short exact sequence.
* `TauCeti.AbelianK0.toBoundedDerivedK0_of` computes the map on an object class.

## Mathlib infrastructure

The degree-zero embedding `DerivedCategory.singleFunctor` and the distinguished triangle
`ShortComplex.ShortExact.singleTriangle` are from Mathlib's derived-category API.

## References

* Charles A. Weibel, *The K-book*, Chapter II, Exercise 9.15, for the comparison between the
  Grothendieck group of an abelian category and that of its bounded derived category.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w w' w'' v u

variable {A : Type u} [Category.{v} A] [Abelian A] [EssentiallySmall.{w} A]
  [HasDerivedCategory.{w'} A] [EssentiallySmall.{w''} (DerivedCategory.Bounded A)]

namespace TriangulatedK0

omit [EssentiallySmall.{w} A] in
/-- A short exact sequence gives a distinguished triangle in the bounded derived category, so
its degree-zero objects satisfy the triangulated `K₀` relation. -/
theorem of_singleFunctor_shortExact {S : ShortComplex A} (hS : S.ShortExact) :
    of ((DerivedCategory.Bounded.singleFunctor A 0).obj S.X₂) =
      of ((DerivedCategory.Bounded.singleFunctor A 0).obj S.X₁) +
        of ((DerivedCategory.Bounded.singleFunctor A 0).obj S.X₃) := by
  simpa using of_distTriang hS.boundedSingleTriangle_distinguished

end TriangulatedK0

namespace AbelianK0

/-- The canonical homomorphism from abelian `K₀` to the triangulated `K₀` of the bounded derived
category. It sends the class of an object to the class of the complex concentrated in degree
zero. -/
noncomputable def toBoundedDerivedK0 : AbelianK0 A →+ TriangulatedK0 (DerivedCategory.Bounded A) :=
  lift
    { obj := fun X ↦ TriangulatedK0.of ((DerivedCategory.Bounded.singleFunctor A 0).obj X)
      map_iso := fun _ _ e ↦ TriangulatedK0.of_congr
        ((DerivedCategory.Bounded.singleFunctor A 0).mapIso e)
      map_shortExact := fun _ hS ↦ TriangulatedK0.of_singleFunctor_shortExact hS }

/-- The canonical map to derived `K₀` sends an object class to the class of its degree-zero
complex. -/
@[simp] theorem toBoundedDerivedK0_of (X : A) :
    toBoundedDerivedK0 (of X) =
      TriangulatedK0.of ((DerivedCategory.Bounded.singleFunctor A 0).obj X) :=
  lift_of _ X

end AbelianK0

end TauCeti

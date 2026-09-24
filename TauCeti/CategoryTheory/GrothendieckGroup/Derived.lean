/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Abelian
public import TauCeti.CategoryTheory.GrothendieckGroup.Triangulated
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# The canonical map from abelian K₀ to derived K₀

For an essentially small abelian category `A` whose derived category is essentially small, this
file constructs the canonical additive homomorphism

```text
K₀(A) ⟶ K₀(D(A)).
```

It sends `[X]` to the class of the complex with `X` in degree zero. A short exact sequence in `A`
gives a distinguished triangle between the corresponding degree-zero complexes in `D(A)`, so this
assignment respects the defining relations of abelian `K₀`.

This is one direction of the bounded-derived comparison in the Grothendieck--Euler roadmap. The
remaining direction must identify the class of a bounded derived object with the alternating sum of
its cohomology classes, and then prove the two maps inverse on the bounded derived category. We do
not assume that the unbounded derived category is essentially small: the explicit smallness
hypothesis is only what lets its triangulated `K₀` be formed while this map is used as an ambient
construction.

## Main definitions

* `TauCeti.AbelianK0.toDerivedK0` is the homomorphism induced by the degree-zero embedding into
  the derived category.

## Main results

* `TauCeti.AbelianK0.toDerivedK0_of` computes the map on an object class.
* `TauCeti.AbelianK0.toDerivedK0_of_shortExact` records the image of a short exact sequence.
* `TauCeti.AbelianK0.toDerivedK0_unique` is the universal characterization of the map.

## Mathlib infrastructure

The degree-zero embedding `DerivedCategory.singleFunctor` and the distinguished triangle
`ShortComplex.ShortExact.singleTriangle` are from Mathlib's derived-category API.

## References

* Charles A. Weibel, *The K-book*, Chapter II, Exercise 9.15, for the comparison between the
  Grothendieck group of an abelian category and that of its bounded derived category.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe w v u

variable {A : Type u} [Category.{v} A] [Abelian A] [EssentiallySmall.{w} A]
  [HasDerivedCategory.{w} A] [EssentiallySmall.{w} (DerivedCategory A)]

namespace AbelianK0

/-- The canonical homomorphism from abelian `K₀` to the triangulated `K₀` of the derived category.
It sends the class of an object to the class of the complex concentrated in degree zero. -/
noncomputable def toDerivedK0 : AbelianK0 A →+ TriangulatedK0 (DerivedCategory A) :=
  lift
    { obj := fun X ↦ TriangulatedK0.of ((DerivedCategory.singleFunctor A 0).obj X)
      map_iso := fun _ _ e ↦ TriangulatedK0.of_congr ((DerivedCategory.singleFunctor A 0).mapIso e)
      map_shortExact := fun _ hS ↦ TriangulatedK0.of_distTriang hS.singleTriangle_distinguished }

/-- The canonical map to derived `K₀` sends an object class to the class of its degree-zero
complex. -/
theorem toDerivedK0_of (X : A) :
    toDerivedK0 (of X) = TriangulatedK0.of ((DerivedCategory.singleFunctor A 0).obj X) :=
  lift_of _ X

/-- The canonical map to derived `K₀` sends the relation of a short exact sequence to the relation
of its associated distinguished triangle. -/
theorem toDerivedK0_of_shortExact {S : ShortComplex A} (hS : S.ShortExact) :
    toDerivedK0 (of S.X₂) = toDerivedK0 (of S.X₁) + toDerivedK0 (of S.X₃) := by
  rw [toDerivedK0_of, toDerivedK0_of, toDerivedK0_of]
  exact TriangulatedK0.of_distTriang hS.singleTriangle_distinguished

/-- A homomorphism from abelian `K₀` is the canonical map to derived `K₀` when it sends every
object class to the class of its degree-zero complex. -/
theorem toDerivedK0_unique (f : AbelianK0 A →+ TriangulatedK0 (DerivedCategory A))
    (hf : ∀ X : A, f (of X) = TriangulatedK0.of ((DerivedCategory.singleFunctor A 0).obj X)) :
    f = toDerivedK0 := by
  refine lift_unique _ f ?_
  intro X
  exact hf X

/-- The canonical map to derived `K₀` is the unique homomorphism with the degree-zero value on
object classes. -/
theorem eq_toDerivedK0_iff (f : AbelianK0 A →+ TriangulatedK0 (DerivedCategory A)) :
    f = toDerivedK0 ↔
      ∀ X : A, f (of X) = TriangulatedK0.of ((DerivedCategory.singleFunctor A 0).obj X) := by
  constructor
  · intro h X
    rw [h, toDerivedK0_of]
  · exact toDerivedK0_unique f

end AbelianK0

end TauCeti

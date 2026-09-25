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

The comparison is an isomorphism: its inverse sends a bounded derived object to the alternating
sum of its cohomology classes.

## Main definitions

* `TauCeti.AbelianK0.toBoundedDerivedK0` is induced by the degree-zero embedding into the bounded
  derived category.

## Main results

* `TauCeti.AbelianK0.toBoundedDerivedK0_of` computes the map on an object class.
* `TauCeti.AbelianK0.toBoundedDerivedK0_unique` is the universal characterization of the map.

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

namespace AbelianK0

omit [EssentiallySmall.{w} A] in
/-- A short exact sequence gives a distinguished triangle in the bounded derived category, so
its degree-zero objects satisfy the triangulated `K₀` relation. -/
theorem triangulatedK0Of_singleFunctor_shortExact {S : ShortComplex A} (hS : S.ShortExact) :
    TriangulatedK0.of ((DerivedCategory.Bounded.singleFunctor A 0).obj S.X₂) =
      TriangulatedK0.of ((DerivedCategory.Bounded.singleFunctor A 0).obj S.X₁) +
        TriangulatedK0.of ((DerivedCategory.Bounded.singleFunctor A 0).obj S.X₃) :=
  TriangulatedK0.of_distTriang (DerivedCategory.Bounded.singleTriangleBounded_distinguished hS)

/-- The canonical homomorphism from abelian `K₀` to the triangulated `K₀` of the bounded derived
category. It sends the class of an object to the class of the complex concentrated in degree
zero. -/
noncomputable def toBoundedDerivedK0 : AbelianK0 A →+ TriangulatedK0 (DerivedCategory.Bounded A) :=
  lift
    { obj := fun X ↦ TriangulatedK0.of ((DerivedCategory.Bounded.singleFunctor A 0).obj X)
      map_iso := fun _ _ e ↦ TriangulatedK0.of_congr
        ((DerivedCategory.Bounded.singleFunctor A 0).mapIso e)
      map_shortExact := fun _ hS ↦ triangulatedK0Of_singleFunctor_shortExact hS }

/-- The canonical map to derived `K₀` sends an object class to the class of its degree-zero
complex. -/
@[simp] theorem toBoundedDerivedK0_of (X : A) :
    toBoundedDerivedK0 (of X) =
      TriangulatedK0.of ((DerivedCategory.Bounded.singleFunctor A 0).obj X) :=
  lift_of _ X

/-- A homomorphism from abelian `K₀` is the canonical map to derived `K₀` when it sends every
object class to the class of its degree-zero complex. -/
theorem toBoundedDerivedK0_unique
    (f : AbelianK0 A →+ TriangulatedK0 (DerivedCategory.Bounded A))
    (hf : ∀ X : A, f (of X) =
      TriangulatedK0.of ((DerivedCategory.Bounded.singleFunctor A 0).obj X)) :
    f = toBoundedDerivedK0 := by
  refine lift_unique _ f ?_
  intro X
  exact hf X

end AbelianK0

end TauCeti

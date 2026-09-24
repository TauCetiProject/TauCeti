/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Abelian
public import TauCeti.CategoryTheory.GrothendieckGroup.Triangulated
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# The canonical map from abelian K₀ to derived K₀

For an essentially small abelian category `A` whose bounded derived category is essentially small,
this file constructs the canonical additive homomorphism

```text
K₀(A) ⟶ K₀(Dᵇ(A)).
```

It sends `[X]` to the class of the complex with `X` in degree zero. A short exact sequence in `A`
gives a distinguished triangle between the corresponding degree-zero complexes in `Dᵇ(A)`, so this
assignment respects the defining relations of abelian `K₀`.

This is one direction of the bounded-derived comparison in the Grothendieck--Euler roadmap. The
remaining direction must identify the class of a bounded derived object with the alternating sum of
its cohomology classes, and then prove the two maps inverse on the bounded derived category.

## Main definitions

* `TauCeti.AbelianK0.toDerivedK0` is the homomorphism induced by the degree-zero embedding into
  the bounded derived category.

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

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

variable {A : Type u} [Category.{v} A] [Abelian A] [EssentiallySmall.{w} A]
  [HasDerivedCategory.{w} A] [EssentiallySmall.{w} (DerivedCategory.Bounded A)]

namespace AbelianK0

/-- The degree-zero embedding into the bounded derived category. -/
noncomputable def singleFunctorBounded : A ⥤ DerivedCategory.Bounded A :=
  (DerivedCategory.TStructure.t (C := A)).bounded.lift (DerivedCategory.singleFunctor A 0)
    (fun _ ↦ ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩)

omit [EssentiallySmall.{w} A] in
/-- A short exact sequence gives a distinguished triangle in the bounded derived category, so
its degree-zero objects satisfy the triangulated `K₀` relation. -/
theorem of_singleFunctorBounded_shortExact {S : ShortComplex A} (hS : S.ShortExact) :
    TriangulatedK0.of (singleFunctorBounded.obj S.X₂) =
      TriangulatedK0.of (singleFunctorBounded.obj S.X₁) +
        TriangulatedK0.of (singleFunctorBounded.obj S.X₃) := by
  let P := (DerivedCategory.TStructure.t (C := A)).bounded
  let F := singleFunctorBounded (A := A)
  let T : Triangle (DerivedCategory.Bounded A) :=
    Triangle.mk (F.map S.f) (F.map S.g)
      (P.fullyFaithfulι.preimage
        (hS.singleδ ≫ (P.ι.commShiftIso (1 : ℤ)).inv.app (F.obj S.X₁)))
  have hT : T ∈ distTriang (DerivedCategory.Bounded A) := by
    change P.ι.mapTriangle.obj T ∈ distTriang (DerivedCategory A)
    simpa [T, F, singleFunctorBounded, ObjectProperty.lift,
      ShortComplex.ShortExact.singleTriangle] using hS.singleTriangle_distinguished
  exact TriangulatedK0.of_distTriang hT

/-- The canonical homomorphism from abelian `K₀` to the triangulated `K₀` of the bounded derived
category. It sends the class of an object to the class of the complex concentrated in degree
zero. -/
noncomputable def toDerivedK0 : AbelianK0 A →+ TriangulatedK0 (DerivedCategory.Bounded A) :=
  lift
    { obj := fun X ↦ TriangulatedK0.of (singleFunctorBounded.obj X)
      map_iso := fun _ _ e ↦ TriangulatedK0.of_congr (singleFunctorBounded.mapIso e)
      map_shortExact := fun _ hS ↦ of_singleFunctorBounded_shortExact hS }

/-- The canonical map to derived `K₀` sends an object class to the class of its degree-zero
complex. -/
theorem toDerivedK0_of (X : A) :
    toDerivedK0 (of X) = TriangulatedK0.of (singleFunctorBounded.obj X) :=
  lift_of _ X

/-- The canonical map to derived `K₀` sends the relation of a short exact sequence to the relation
of its associated distinguished triangle. -/
theorem toDerivedK0_of_shortExact {S : ShortComplex A} (hS : S.ShortExact) :
    toDerivedK0 (of S.X₂) = toDerivedK0 (of S.X₁) + toDerivedK0 (of S.X₃) := by
  rw [toDerivedK0_of, toDerivedK0_of, toDerivedK0_of]
  exact of_singleFunctorBounded_shortExact hS

/-- A homomorphism from abelian `K₀` is the canonical map to derived `K₀` when it sends every
object class to the class of its degree-zero complex. -/
theorem toDerivedK0_unique (f : AbelianK0 A →+ TriangulatedK0 (DerivedCategory.Bounded A))
    (hf : ∀ X : A, f (of X) = TriangulatedK0.of (singleFunctorBounded.obj X)) :
    f = toDerivedK0 := by
  refine lift_unique _ f ?_
  intro X
  exact hf X

/-- The canonical map to derived `K₀` is the unique homomorphism with the degree-zero value on
object classes. -/
theorem eq_toDerivedK0_iff (f : AbelianK0 A →+ TriangulatedK0 (DerivedCategory.Bounded A)) :
    f = toDerivedK0 ↔
      ∀ X : A, f (of X) = TriangulatedK0.of (singleFunctorBounded.obj X) := by
  constructor
  · intro h X
    rw [h, toDerivedK0_of]
  · exact toDerivedK0_unique f

end AbelianK0

end TauCeti

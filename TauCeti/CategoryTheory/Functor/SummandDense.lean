/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# Summand-dense functors

A functor `T : C ⥤ D` into a category with binary biproducts is *summand-dense* (Weibel calls
such a functor *cofinal*) when every object `X` of `D` is a direct summand of an object in the
essential image of `T`: there is an object `Y` of `D` with `X ⊞ Y ≅ T P` for some `P`.

This is the hypothesis under which the relative Grothendieck group `K₀(T)` of `T` fits into the
exact sequence `K₀(T) → K₀(C) → K₀(D)`. The guiding example is extension of scalars along a ring
homomorphism `R → S` on finitely generated projective modules: every finitely generated projective
`S`-module is a direct summand of a free module `Sⁿ`, which is the extension of `Rⁿ`.
An essentially surjective functor is summand-dense.

## Main definitions

* `CategoryTheory.Functor.IsSummandDense T`: every object of `D` has a complement whose
  biproduct with it lies in the essential image of `T`.

## Main results

* `CategoryTheory.Functor.IsSummandDense.exists_biprod_iso`: every object `X` of `D` has a
  complement `Y` with `X ⊞ Y ≅ T P` for some object `P` of `C`.
* `CategoryTheory.Functor.isSummandDense_of_essSurj`: essentially surjective functors are
  summand-dense.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Exercise 2.17 (cofinal functors and the relative group `K₀(T)`).
-/

public section

namespace CategoryTheory.Functor

open Limits

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms D] [HasBinaryBiproducts D]

/-- A functor `T : C ⥤ D` is **summand-dense** (cofinal, in Weibel's terminology) when every
object of `D` is a direct summand of an object in the essential image of `T`: for each `X` there
is `Y` with `X ⊞ Y` in the essential image. -/
class IsSummandDense (T : C ⥤ D) : Prop where
  /-- Every object `X` has a complement `Y` such that `X ⊞ Y` lies in the essential image. -/
  exists_biprod_mem_essImage (X : D) : ∃ Y : D, T.essImage (X ⊞ Y)

/-- For a summand-dense functor `T`, every object `X` has a complement `Y` with `X ⊞ Y ≅ T P`. -/
theorem IsSummandDense.exists_biprod_iso (T : C ⥤ D) [T.IsSummandDense] (X : D) :
    ∃ (Y : D) (P : C), Nonempty (X ⊞ Y ≅ T.obj P) := by
  obtain ⟨Y, P, ⟨e⟩⟩ := IsSummandDense.exists_biprod_mem_essImage (T := T) X
  exact ⟨Y, P, ⟨e.symm⟩⟩

/-- An essentially surjective functor is summand-dense: every object, in particular `X ⊞ X`, lies
in its essential image. -/
instance isSummandDense_of_essSurj (T : C ⥤ D) [T.EssSurj] : T.IsSummandDense where
  exists_biprod_mem_essImage X := ⟨X, EssSurj.mem_essImage T _⟩

end CategoryTheory.Functor

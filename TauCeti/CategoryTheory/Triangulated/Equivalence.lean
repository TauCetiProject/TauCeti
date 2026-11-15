/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Triangulated equivalences from triangle functors

If `E : C ≌ D` is an equivalence between pretriangulated categories whose forward functor is equal
to a triangle functor `F : C ⥤ D` (for example `E = F.asEquivalence` for `[F.IsEquivalence]`),
transporting `F`'s shift compatibility along `eqToIso (h : E.functor = F).symm` via
`Functor.CommShift.ofIso_compatibility` and `Equivalence.IsTriangulated.mk'` equips `E` with
compatible shift structures on `E.functor` and `E.inverse` and proves `E.IsTriangulated`.

## Main results

* `CategoryTheory.Equivalence.isTriangulated_of_functor_eq`: derives `E.IsTriangulated` from
  `h : E.functor = F`, `[F.CommShift ℤ]`, and `[F.IsTriangulated]`.
* `CategoryTheory.Functor.asEquivalence_isTriangulated`: specializes to `F.asEquivalence` for a
  triangle functor `F` satisfying `[F.IsEquivalence]`.
-/

public section

namespace CategoryTheory

open Limits Pretriangulated

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [Preadditive C] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

/-- If the forward functor of an equivalence `E : C ≌ D` between pretriangulated categories is equal
to a triangle functor `F`, transporting `F`'s shift compatibility along `E.functor = F` makes `E`
a triangulated equivalence. -/
theorem Equivalence.isTriangulated_of_functor_eq (E : C ≌ D) {F : C ⥤ D} [F.CommShift ℤ]
    [F.IsTriangulated] (h : E.functor = F) :
    letI : E.functor.CommShift ℤ := Functor.CommShift.ofIso (eqToIso h.symm) ℤ
    letI := E.commShiftInverse ℤ
    letI := E.commShift_of_functor ℤ
    E.IsTriangulated := by
  let e := eqToIso h.symm
  let : E.functor.CommShift ℤ := Functor.CommShift.ofIso e ℤ
  let := E.commShiftInverse ℤ
  let := E.commShift_of_functor ℤ
  have := Functor.CommShift.ofIso_compatibility e ℤ
  exact Equivalence.IsTriangulated.mk' _ (Functor.isTriangulated_of_iso e)

/-- If a triangle functor `F : C ⥤ D` between pretriangulated categories is an equivalence of
categories, `F.asEquivalence` is a triangulated equivalence. -/
theorem Functor.asEquivalence_isTriangulated (F : C ⥤ D) [F.IsEquivalence] [F.CommShift ℤ]
    [F.IsTriangulated] :
    letI : F.asEquivalence.functor.CommShift ℤ :=
      Functor.CommShift.ofIso (eqToIso (Functor.asEquivalence_functor F).symm) ℤ
    letI := F.asEquivalence.commShiftInverse ℤ
    letI := F.asEquivalence.commShift_of_functor ℤ
    F.asEquivalence.IsTriangulated :=
  F.asEquivalence.isTriangulated_of_functor_eq (Functor.asEquivalence_functor F)

end CategoryTheory

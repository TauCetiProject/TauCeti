/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.SumOfUnits
public import Mathlib.CategoryTheory.Monoidal.Subcategory

/-!
# Transport of tensor-closed subquotient hulls

A monoidal equivalence identifies the hulls of corresponding objects, including the condition
that these hulls are closed under tensor products. Together with transport of sums of units,
this allows representation-theoretic criteria to be stated in an equivalent tensor category.

## References

* P. Deligne and J. S. Milne, *Tannakian categories*, Corollary 2.22.
-/

public section

namespace CategoryTheory.Equivalence

open Limits MonoidalCategory TauCeti

universe v u v' u'

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  [MonoidalCategory C] {D : Type u'} [Category.{v'} D] [Preadditive D]
  [HasFiniteBiproducts D] [MonoidalCategory D]

/-- A monoidal equivalence preserves and reflects tensor closure of finite-sum and
subquotient hulls. Neither rigidity nor symmetry is needed. -/
@[simp]
theorem tensorLE_subquotientHull_obj_iff (E : C ≌ D) [E.functor.Monoidal] (X : C) :
    (subquotientHull (E.functor.obj X)).TensorLE
        (subquotientHull (E.functor.obj X)) (subquotientHull (E.functor.obj X)) ↔
      (subquotientHull X).TensorLE (subquotientHull X) (subquotientHull X) := by
  constructor
  · intro h
    exact ⟨fun Y Z hY hZ ↦ (E.subquotientHull_obj_iff X (Y ⊗ Z)).1
      ((subquotientHull (E.functor.obj X)).prop_of_iso (Functor.Monoidal.μIso E.functor Y Z)
        (h.prop_tensor _ _ ((E.subquotientHull_obj_iff X Y).2 hY)
          ((E.subquotientHull_obj_iff X Z).2 hZ)))⟩
  · intro h
    refine ⟨fun Y Z hY hZ ↦ ?_⟩
    have hY' : subquotientHull X (E.inverse.obj Y) := (E.subquotientHull_obj_iff _ _).1
      ((subquotientHull (E.functor.obj X)).prop_of_iso (E.counitIso.app Y).symm hY)
    have hZ' : subquotientHull X (E.inverse.obj Z) := (E.subquotientHull_obj_iff _ _).1
      ((subquotientHull (E.functor.obj X)).prop_of_iso (E.counitIso.app Z).symm hZ)
    exact (subquotientHull (E.functor.obj X)).prop_of_iso
      ((Functor.Monoidal.μIso E.functor _ _).symm ≪≫
        tensorIso (E.counitIso.app Y) (E.counitIso.app Z))
      ((E.subquotientHull_obj_iff _ _).2 (h.prop_tensor _ _ hY' hZ'))

/-- Existence of a nontrivial object with tensor-closed hull is invariant under monoidal
equivalence. Here nontrivial means that the object is not a finite sum of units. -/
theorem exists_not_isSumOfUnits_tensorLE_subquotientHull_iff
    (E : C ≌ D) [E.functor.Monoidal] :
    (∃ X : C, ¬ IsSumOfUnits X ∧
      (subquotientHull X).TensorLE (subquotientHull X) (subquotientHull X)) ↔
    ∃ Y : D, ¬ IsSumOfUnits Y ∧
      (subquotientHull Y).TensorLE (subquotientHull Y) (subquotientHull Y) := by
  let := E.inverseMonoidal
  constructor
  · rintro ⟨X, hX, hT⟩
    exact ⟨E.functor.obj X, hX ∘ (E.isSumOfUnits_obj_iff X).1,
      (E.tensorLE_subquotientHull_obj_iff X).2 hT⟩
  · rintro ⟨Y, hY, hT⟩
    exact ⟨E.inverse.obj Y, hY ∘ (E.symm.isSumOfUnits_obj_iff Y).1,
      (E.symm.tensorLE_subquotientHull_obj_iff Y).2 hT⟩

end CategoryTheory.Equivalence

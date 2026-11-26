/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
# Quotients and finite sums of additive functors

This file collects closure properties of additive functors inside functor categories.

A biproduct `⨁ P` of functors `P j : C ⥤ D` into a preadditive category acts on a morphism `a` as
the sum over `j` of the projection to `P j`, the action of `P j` on `a`, and the inclusion of
`P j` (`CategoryTheory.biproduct_functor_map_eq_sum`). So a finite biproduct, and hence a finite
coproduct, of additive functors is additive. A quotient of an additive functor
`C ⥤ AddCommGrpCat` is additive, since every element of its values lifts to the additive functor.

## Main declarations

* `CategoryTheory.biproduct_functor_map_eq_sum`: the action of a biproduct of functors on
  morphisms.
* `CategoryTheory.Functor.additive_biproduct`, `CategoryTheory.Functor.additive_sigma`: finite
  biproducts and finite coproducts of additive functors are additive.
* `CategoryTheory.Functor.additive_of_epi`: a quotient of an additive functor
  `C ⥤ AddCommGrpCat` is additive.
-/

public section

universe v

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type*} [Category* C] {D : Type*} [Category* D] [Preadditive D]

/-- A biproduct `⨁ P` of functors acts on a morphism `a` as the sum, over the summands, of the
projection, the action of the summand on `a`, and the inclusion. -/
theorem biproduct_functor_map_eq_sum {J : Type*} [Fintype J] (P : J → C ⥤ D) [HasBiproduct P]
    {Z W : C} (a : Z ⟶ W) :
    (⨁ P).map a = ∑ j, (biproduct.π P j).app Z ≫ (P j).map a ≫ (biproduct.ι P j).app W := by
  calc (⨁ P).map a = (𝟙 (⨁ P) : ⨁ P ⟶ ⨁ P).app Z ≫ (⨁ P).map a := by simp
    _ = _ := by
      rw [← biproduct.total, NatTrans.app_sum, Preadditive.sum_comp]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [NatTrans.comp_app, Category.assoc, (biproduct.ι P j).naturality]

namespace Functor

variable [Preadditive C]

/-- A finite biproduct of additive functors is additive. -/
instance additive_biproduct {J : Type*} [Finite J] (P : J → C ⥤ D) [HasBiproduct P]
    [∀ j, (P j).Additive] : (⨁ P).Additive where
  map_add {Z W a b} := by
    have := Fintype.ofFinite J
    simp only [biproduct_functor_map_eq_sum, Functor.map_add, Preadditive.add_comp,
      Preadditive.comp_add, Finset.sum_add_distrib]

/-- A finite coproduct of additive functors is additive. -/
instance additive_sigma {J : Type*} [Finite J] (P : J → C ⥤ D) [HasCoproduct P]
    [∀ j, (P j).Additive] : (∐ P).Additive :=
  have := Fintype.ofFinite J
  have := HasBiproduct.of_hasCoproduct P
  additive_of_iso (biproduct.isoCoproduct P)

/-- A quotient of an additive functor `C ⥤ AddCommGrpCat` is additive: every element of a value
of the quotient lifts to the additive functor. -/
theorem additive_of_epi {F G : C ⥤ AddCommGrpCat.{v}} [F.Additive] (q : F ⟶ G) [Epi q] :
    G.Additive where
  map_add {Z W a b} := by
    ext x
    obtain ⟨y, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (q.app Z)).1 inferInstance x
    simp only [AddCommGrpCat.hom_add_apply, ← NatTrans.naturality_apply, Functor.map_add,
      _root_.map_add]

end Functor

end CategoryTheory

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.ModCat.SimpleFunctor

/-!
# Simple additive functors and finite presentation

A simple additive functor is a quotient of a representable functor. In a Krull-Schmidt category,
it is therefore the simple quotient of a representable at an indecomposable. The existence of
right almost split morphisms at all indecomposables is equivalent to finite presentation of
every simple additive functor.

## References

* H. Enomoto, *Classifications of exact structures and Cohen-Macaulay-finite algebras*,
  Adv. Math. **335** (2018), 838–877, Proposition A.2.
-/

public section

universe v u

open CategoryTheory Limits Opposite

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A simple additive functor is finitely generated. -/
theorem isFinitelyGeneratedFunctor_of_simple {F : Cᵒᵖ ⥤ AddCommGrpCat.{v}}
    [F.Additive] [Simple F] : IsFinitelyGeneratedFunctor F := by
  have zero_app_apply {G : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (Z : Cᵒᵖ) (z : G.obj Z) :
      (0 : G ⟶ F).app Z z = 0 := by
    rw [Limits.zero_app]
    exact (congrArg (fun f : _ →+ _ ↦ f z) AddCommGrpCat.hom_zero).trans
      (AddMonoidHom.zero_apply z)
  obtain ⟨Y, x, hx⟩ : ∃ (Y : C) (x : F.obj (op Y)), x ≠ 0 := by
    by_contra! h
    apply id_ne_zero F
    ext Z z
    simpa only [NatTrans.id_app, AddCommGrpCat.id_apply, zero_app_apply] using h Z.unop z
  let p : preadditiveYoneda.obj Y ⟶ F := preadditiveYonedaEquiv.symm x
  have hp : Epi p := epi_of_ne_zero_to_simple (by
    intro hp
    apply hx
    have he : preadditiveYonedaEquiv p = x := preadditiveYonedaEquiv.apply_symm_apply x
    rw [hp, preadditiveYonedaEquiv_apply] at he
    exact he.symm.trans (zero_app_apply (G := preadditiveYoneda.obj Y) (op Y) (𝟙 Y)))
  exact (isFinitelyGeneratedFunctor_preadditiveYoneda_obj Y).of_epi p

variable [HasFiniteBiproducts C] [IsKrullSchmidt C]

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- In a Krull-Schmidt category, every simple additive functor is finitely presented exactly when
every indecomposable object is the target of a right almost split morphism. -/
theorem forall_isFinitelyPresentedFunctor_of_simple_iff :
    (∀ F : ModCat.{v} C, Simple F → IsFinitelyPresentedFunctor F.obj) ↔
      ∀ Z : C, Indecomposable Z → ∃ (Y : C) (g : Y ⟶ Z), IsRightAlmostSplit g := by
  constructor
  · intro h Z hZ
    let := (IsKrullSchmidt.indecomposable_iff_isLocalRing_end Z).mp hZ
    have hs := simple_comp_preadditiveYoneda_obj_quotientFunctor_jacobsonRadicalIdeal Z
    let S := ModCat.simple Z
    exact (isFinitelyPresentedFunctor_simpleFunctor_iff Z).mp
      (h S ((AdditiveFunctor.simple_obj_iff S).mp hs))
  · intro h F hF
    let : F.obj.Additive := F.property
    let := (AdditiveFunctor.simple_obj_iff F).mpr hF
    obtain ⟨Z, hZ, ⟨e⟩⟩ :=
      IsKrullSchmidt.exists_iso_simpleFunctor (isFinitelyGeneratedFunctor_of_simple (F := F.obj))
    exact ((isFinitelyPresentedFunctor_simpleFunctor_iff Z).mpr
      (h Z indecomposable_of_isLocalRing_end)).of_iso e

end TauCeti

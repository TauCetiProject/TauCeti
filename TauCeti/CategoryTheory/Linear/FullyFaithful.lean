/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Morphism spaces along a fully faithful linear functor

A fully faithful `R`-linear functor identifies the morphism space `X ⟶ Y` with `F X ⟶ F Y` as
`R`-modules. Mathlib supplies the `R`-linear map `CategoryTheory.Functor.mapLinearMap` and,
separately, the bijectivity of `F.map`; this file records the resulting `R`-linear isomorphism,
which is what transports a dimension or a finiteness statement about a morphism space along the
functor.
-/

public section

namespace CategoryTheory

universe v v' u u' t

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] [Preadditive C]
  [Preadditive D] (R : Type t) [Semiring R] [CategoryTheory.Linear R C]
  [CategoryTheory.Linear R D] (F : C ⥤ D) [F.Additive]
  [F.Linear R] [F.Full] [F.Faithful]

/-- **A fully faithful `R`-linear functor is an isomorphism on morphism spaces.** -/
noncomputable def Functor.homLinearEquiv (X Y : C) : (X ⟶ Y) ≃ₗ[R] (F.obj X ⟶ F.obj Y) :=
  LinearEquiv.ofBijective (F.mapLinearMap R) ⟨F.map_injective, F.map_surjective⟩

@[simp]
theorem Functor.homLinearEquiv_apply {X Y : C} (f : X ⟶ Y) :
    F.homLinearEquiv R X Y f = F.map f := by
  rw [Functor.homLinearEquiv]
  exact congrFun (Functor.coe_mapLinearMap R F) f

end CategoryTheory

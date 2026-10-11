/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.CategoryTheory.Linear.FullyFaithful

/-!
# Restriction of actions

Restriction along a composite monoid homomorphism is successive restriction, as an equality
of functors. This equality form complements Mathlib's natural isomorphism `Action.resComp`.

For actions in a linear category, restriction along a surjective monoid homomorphism preserves
the finrank of morphism spaces. This uses Mathlib's fullness result `Action.full_res` and
`Functor.homLinearEquiv`, and in particular applies to intertwining spaces of finite-dimensional
representations over a commutative ring.

## Main results

* `MonoidHom.actionRes_comp`: restriction along a composite is successive restriction.
* `MonoidHom.finrank_hom_actionRes_of_surjective`: restriction along a surjective monoid
  homomorphism preserves the finrank of morphism spaces in a linear category.
-/

public section

open CategoryTheory

variable {V : Type*} [Category V] {H K L : Type*} [Monoid H] [Monoid K] [Monoid L]

/-- Restriction of actions along a composite is successive restriction. This is the equality
form of Mathlib's natural isomorphism `Action.resComp`. -/
theorem MonoidHom.actionRes_comp (φ : K →* L) (ψ : H →* K) :
    Action.res V (φ.comp ψ) = Action.res V φ ⋙ Action.res V ψ :=
  rfl

/-- Restriction along a surjective monoid homomorphism preserves the finrank of morphism spaces
in a linear category. In particular it preserves the dimension of intertwining spaces of
representations. -/
theorem MonoidHom.finrank_hom_actionRes_of_surjective {k : Type*} [Semiring k]
    [Preadditive V] [Linear k V] (f : H →* K) (hf : Function.Surjective f) (X Y : Action V K) :
    Module.finrank k ((Action.res V f).obj X ⟶ (Action.res V f).obj Y) =
      Module.finrank k (X ⟶ Y) := by
  let : (Action.res V f).Full := Action.full_res V f hf
  exact ((Action.res V f).homLinearEquiv k X Y).finrank_eq.symm

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Concrete

/-!
# Permutation representations of concrete actions

`Action.toPermHom_apply_eq_ρ` identifies the permutation action on the underlying type with
the structure maps of a bundled action, using `Action.ρ_apply_eq_smul` and `MulAction.toPermHom`.
-/

public section

open CategoryTheory

/-- The permutation representation of a bundled group action acts by its structure maps. -/
theorem Action.toPermHom_apply_eq_ρ {V : Type (u + 1)} [LargeCategory V]
    {FV : V → V → Type*} {CV : V → Type*}
    [∀ X Y, FunLike (FV X Y) (CV X) (CV Y)] [ConcreteCategory V FV]
    {G : Type*} [Group G] (A : Action V G) (g : G) (x : ToType A.V) :
    MulAction.toPermHom G (ToType A.V) g x = (A.ρ g).asHom x := by
  simpa only [MulAction.toPermHom_apply, MulAction.toPerm_apply] using
    (Action.ρ_apply_eq_smul A g x).symm

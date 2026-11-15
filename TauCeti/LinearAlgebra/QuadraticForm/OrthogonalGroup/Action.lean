/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

/-!
# Orthogonal actions on quadratic level sets

The orthogonal group preserves each level set of its quadratic map. This invariant subset uses
its inherited action; its carrier and membership lemmas identify the original quadratic equation.
-/

public section

namespace QuadraticMap

open TauCeti.QuadraticMap

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- A level set of a quadratic map, invariant under its orthogonal group. -/
def orthogonalLevelSet (Q : QuadraticMap R M N) (c : N) :
    SubMulAction (orthogonalGroup Q) M where
  carrier := {x | Q x = c}
  smul_mem' g _ hx := (map_app_of_mem_orthogonalGroup g.property _).trans hx

/-- The carrier of the invariant level set is the original quadratic level set. -/
@[simp]
theorem coe_orthogonalLevelSet (Q : QuadraticMap R M N) (c : N) :
    (orthogonalLevelSet Q c : Set M) = {x | Q x = c} := by
  simp only [orthogonalLevelSet]
  rfl

/-- Membership in the invariant level set is the defining quadratic equation. -/
@[simp]
theorem mem_orthogonalLevelSet_iff (Q : QuadraticMap R M N) (c : N) (x : M) :
    x ∈ orthogonalLevelSet Q c ↔ Q x = c :=
  Iff.rfl

end QuadraticMap

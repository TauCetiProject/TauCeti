/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic

/-!
# Evaluation of the algebraic representation underlying a continuous representation

Forgetting continuity leaves the action on each vector unchanged.

## Main results

* `ContRepresentation.toRepresentation_apply`: evaluation agrees with the continuous action.

## References

* `Mathlib.RepresentationTheory.Continuous.Basic`, for `ContRepresentation.toRepresentation`.
-/

public section

/-- Forgetting continuity of an action preserves its evaluation on vectors. -/
-- Normalize evaluation before the generic linear-map coercion rules expand its head.
@[simp↓]
theorem ContRepresentation.toRepresentation_apply {R G V : Type*} [Ring R] [Monoid G]
    [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [Module R V]
    (π : ContRepresentation R G V) (g : G) (v : V) :
    (π.toRepresentation : Representation R G V) g v = π g v := (rfl)

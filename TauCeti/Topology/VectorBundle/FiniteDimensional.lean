/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# The fibres of a line bundle

Every fibre of a vector bundle has the dimension of the model fibre
(`VectorBundle.finrank_eq`). In particular, every fibre of a bundle whose model fibre is a line is
a line (`VectorBundle.finrank_eq_one`).
-/

public section

namespace VectorBundle

open Bundle Module

variable (R : Type*) {B : Type*} (F : Type*) (E : B → Type*)
  [NontriviallyNormedField R] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F E)]
  [NormedAddCommGroup F] [NormedSpace R F]
  [(x : B) → TopologicalSpace (E x)] [FiberBundle F E]
  [(x : B) → AddCommGroup (E x)] [(x : B) → Module R (E x)] [VectorBundle R F E]

/-- Each fibre of a vector bundle whose model fibre is a line is a line. -/
protected theorem finrank_eq_one (hF : finrank R F = 1) (b : B) : finrank R (E b) = 1 :=
  (VectorBundle.finrank_eq R F E b).trans hF

end VectorBundle

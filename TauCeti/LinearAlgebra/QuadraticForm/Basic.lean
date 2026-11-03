/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Basic properties of quadratic maps

This file records elementary consequences of the quadratic-map axioms.

## Main results

* `QuadraticMap.nontrivial_of_ne_zero`: the source of a nonzero quadratic map is nontrivial.
-/

public section

namespace QuadraticMap

/-- The source of a nonzero quadratic map is nontrivial. -/
theorem nontrivial_of_ne_zero {S V N : Type*} [CommSemiring S] [AddCommMonoid V]
    [Module S V] [AddCommMonoid N] [Module S N] {Q : QuadraticMap S V N} (hQ : Q ≠ 0) :
    Nontrivial V := by
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hQ
  exact nontrivial_of_ne v 0 (fun h ↦ hv (by simp [h]))

end QuadraticMap

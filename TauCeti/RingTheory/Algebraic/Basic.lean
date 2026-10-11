/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Algebraic.Basic

/-!
# Translation of transcendental elements

Adding a base-ring constant to a transcendental element preserves transcendence, over an
arbitrary commutative ring and in an arbitrary ring algebra.
-/

public section

open Polynomial

namespace Transcendental

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {x : A}

/-- Translating a transcendental element by a constant keeps it transcendental. -/
theorem add_algebraMap (hx : Transcendental R x) (c : R) :
    Transcendental R (x + algebraMap R A c) := by
  rw [transcendental_iff] at hx ⊢
  intro p hp
  apply (comp_X_add_C_eq_zero_iff (t := c)).mp
  apply hx
  simpa only [aeval_comp, map_add, aeval_X, aeval_C] using hp

end Transcendental

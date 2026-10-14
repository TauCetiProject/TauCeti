/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Algebraic.Basic

/-!
# Transcendental elements under translations and algebra maps

Adding a base-ring constant to a transcendental element preserves transcendence, over an
arbitrary commutative ring and in an arbitrary ring algebra. So does applying an injective algebra
homomorphism, the transcendental counterpart of Mathlib's `isAlgebraic_algHom_iff`.
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

/-- An injective algebra homomorphism carries a transcendental element to a transcendental
element. -/
protected theorem map {B G : Type*} [Ring B] [Algebra R B] [FunLike G A B] [AlgHomClass G R A B]
    (f : G) (hf : Function.Injective f) (hx : Transcendental R x) : Transcendental R (f x) :=
  (isAlgebraic_algHom_iff (AlgHom.ofClass f) hf).not.mpr hx

end Transcendental

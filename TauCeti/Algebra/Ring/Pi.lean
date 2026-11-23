/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Pi

/-!
# Coordinate slices along a product ring equivalence

Records multiplication identities for the coordinate slices `e.symm (Pi.single i a)` of a ring
equivalence `e : E ≃+* ∀ i, A i` (`RingEquiv.symm_single_one_mul`, `RingEquiv.symm_single_mul`).
-/

public section

namespace RingEquiv

variable {E : Type*} [Semiring E] {ι : Type*} [DecidableEq ι] {A : ι → Type*}
  [∀ i, Semiring (A i)]

/-- Multiplying on the left by `e.symm (Pi.single i 1)` projects `x` onto the `i`-th slice. -/
theorem symm_single_one_mul (e : E ≃+* ∀ i, A i) (i : ι) (x : E) :
    e.symm (Pi.single i 1) * x = e.symm (Pi.single i (e x i)) :=
  e.injective <| by simp [← Pi.single_mul_left]

/-- The `i`-th coordinate embedding `a ↦ e.symm (Pi.single i a)` preserves multiplication. -/
theorem symm_single_mul (e : E ≃+* ∀ i, A i) (i : ι) (u v : A i) :
    e.symm (Pi.single i (u * v)) = e.symm (Pi.single i u) * e.symm (Pi.single i v) := by
  rw [Pi.single_mul, map_mul]

end RingEquiv

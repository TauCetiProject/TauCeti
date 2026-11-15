/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Defs

/-!
# Signs as Booleans

A Boolean `s` acts as a sign on a type with an involutive inversion, sending `g` to
`cond s g g⁻¹`: `true` keeps `g` and `false` inverts it. This is how the letters `x ^ ±1` of
signed words are evaluated.

## Main results

* `Bool.cond_cond_inv`: applying the same sign twice, the second time to the result of the first,
  returns the element.
-/

public section

/-- Raising an element to a sign twice returns the element. -/
theorem Bool.cond_cond_inv {G : Type*} [InvolutiveInv G] (s : Bool) (g : G) :
    cond s (cond s g g⁻¹) (cond s g g⁻¹)⁻¹ = g := by
  cases s <;> simp

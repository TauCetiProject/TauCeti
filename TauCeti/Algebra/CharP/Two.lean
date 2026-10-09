/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Two

/-!
# Additive cancellation in characteristic two

In a semiring of characteristic two, each element is its own additive inverse. Consequently
addition is cancellative, even when the given semiring structure does not include additive
cancellation. This supplies the cancellation needed by the grid commutation chain-map criterion.
-/

public section

namespace TauCeti

/-- Addition in a semiring of characteristic two is cancellative. -/
theorem isCancelAdd_of_charTwo (R : Type*) [Semiring R] [CharP R 2] : IsCancelAdd R where
  add_left_cancel a b c h := by
    have h' := congrArg (fun t => a + t) h
    simpa only [CharTwo.add_cancel_left] using h'
  add_right_cancel a b c h := by
    have h' := congrArg (fun t => t + a) h
    simpa only [CharTwo.add_cancel_right] using h'

end TauCeti

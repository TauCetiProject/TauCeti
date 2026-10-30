/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Module.Defs

/-!
# Additive cancellation in characteristic two

In a possibly nonassociative semiring of characteristic two, each element is its own additive
inverse. Consequently addition is cancellative, even when the given semiring structure lacks
additive cancellation. This supplies the cancellation needed by the grid commutation chain-map
criterion. The same holds in any module over a semiring of characteristic two
(`TauCeti.add_self_eq_zero_of_charTwo`), which is how terms appearing twice cancel in sign-free
differentials.
-/

public section

namespace TauCeti

/-- Addition in a possibly nonassociative semiring of characteristic two is cancellative. -/
theorem isCancelAdd_of_charTwo (R : Type*) [NonAssocSemiring R] [CharP R 2] : IsCancelAdd R where
  add_left_cancel a b c h := by
    have h' := congrArg (fun t => a + t) h
    simpa only [CharTwo.add_cancel_left] using h'
  add_right_cancel a b c h := by
    have h' := congrArg (fun t => t + a) h
    simpa only [CharTwo.add_cancel_right] using h'

/-- In a module over a semiring of characteristic two, each element is its own additive inverse. -/
theorem add_self_eq_zero_of_charTwo (R : Type*) {M : Type*} [Semiring R] [CharP R 2]
    [AddCommMonoid M] [Module R M] (x : M) : x + x = 0 := by
  rw [← two_smul R, CharTwo.two_eq_zero, zero_smul]

end TauCeti

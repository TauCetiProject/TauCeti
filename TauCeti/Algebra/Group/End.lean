/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.End

/-!
# Group endomorphisms and automorphisms

This file records compatibility between the monoid structures on bundled group automorphisms and
endomorphisms.

## Main results

* `TauCeti.mulAut_toMonoidHom_pow`: taking the endomorphism underlying a power of an automorphism is
  the same as taking the corresponding power in the endomorphism monoid.
-/

public section

namespace TauCeti

/-- The endomorphism underlying a power of a multiplicative automorphism is its power in the
endomorphism monoid. -/
theorem mulAut_toMonoidHom_pow {G : Type*} [Monoid G] (f : MulAut G) :
    ∀ m : ℕ, (show Monoid.End G from f.toMonoidHom) ^ m = (f ^ m).toMonoidHom
  | 0 => rfl
  | m + 1 => by rw [pow_succ, mulAut_toMonoidHom_pow f m, pow_succ]; rfl

end TauCeti

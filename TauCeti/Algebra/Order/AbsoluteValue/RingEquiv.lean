/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Equiv

/-!
# Absolute values preserved by ring isomorphisms

If a ring isomorphism preserves absolute values, so does its inverse. This elementary transport
fact is independent of the topologies or completions associated with the absolute values, and is
the archimedean counterpart of `Valuation.apply_symm_eq_of_apply_eq`.
-/

public section

namespace AbsoluteValue

variable {R R' S : Type*} [Semiring R] [Semiring R'] [Semiring S] [PartialOrder S]
  {v : AbsoluteValue R S} {w : AbsoluteValue R' S}

/-- The inverse of a ring isomorphism carrying `v` to `w` carries `w` to `v`. -/
theorem apply_symm_eq_of_apply_eq {σ : R ≃+* R'} (hσ : ∀ x, w (σ x) = v x) (y : R') :
    v (σ.symm y) = w y := by
  rw [← hσ, RingEquiv.apply_symm_apply]

end AbsoluteValue

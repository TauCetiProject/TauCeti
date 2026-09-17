/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Quotient

/-!
# Evaluating homeomorphisms between quotient spaces

This file records how Mathlib's `Homeomorph.Quotient.congrRight`, the homeomorphism between the
quotients of a space by two equivalent relations, acts on equivalence classes.

## Main results

* `Homeomorph.Quotient.congrRight_mk`: `congrRight` sends the class of `x` to the class of `x`.
-/

public section

namespace Homeomorph.Quotient

variable {X : Type*} [TopologicalSpace X]

/-- `Homeomorph.Quotient.congrRight` sends the class of `x` to the class of `x`. This is the
homeomorphism counterpart of Mathlib's `Quot.congr_mk`, and holds by definition for the same
reason: `Homeomorph.Quotient.congrRight` is `Quot.congr` for the identity equivalence. -/
@[simp]
theorem congrRight_mk {r r' : Setoid X} (h : ∀ x₁ x₂, r x₁ x₂ ↔ r' x₁ x₂) (x : X) :
    Homeomorph.Quotient.congrRight h (Quotient.mk r x) = Quotient.mk r' x :=
  rfl

end Homeomorph.Quotient

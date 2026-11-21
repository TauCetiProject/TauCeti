/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Quotient

/-!
# Evaluating homeomorphisms between quotient spaces

This file records how Mathlib's `Homeomorph.Quotient.congr` and
`Homeomorph.Quotient.congrRight`, homeomorphisms between quotient spaces, act on equivalence
classes.

## Main results

* `Homeomorph.Quotient.congr_mk`: `congr` sends the class of `x` to the class of its image.
* `Homeomorph.Quotient.congrRight_mk`: `congrRight` sends the class of `x` to the class of `x`.
-/

public section

namespace Homeomorph.Quotient

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- `Homeomorph.Quotient.congr` sends the class of `x` to the class of its image. This is the
homeomorphism counterpart of Mathlib's `Quotient.congr_mk`, and holds by definition for the same
reason. The counterpart is needed because a homeomorphism and its underlying equivalence are
applied through different coercions, so `Quotient.congr_mk` does not rewrite a goal stated for
`Homeomorph.Quotient.congr`, just as `Quot.congr_mk` does not rewrite one stated for
`Quotient.congr`. -/
@[simp]
theorem congr_mk {rX : Setoid X} {rY : Setoid Y} (e : X ≃ₜ Y)
    (h : ∀ x₁ x₂, rX x₁ x₂ ↔ rY (e x₁) (e x₂)) (x : X) :
    Homeomorph.Quotient.congr e h (Quotient.mk rX x) = Quotient.mk rY (e x) :=
  rfl

/-- `Homeomorph.Quotient.congrRight` sends the class of `x` to the class of `x`. This is the
homeomorphism counterpart of Mathlib's `Quot.congr_mk`, and holds by definition for the same
reason: `Homeomorph.Quotient.congrRight` is `Quot.congr` for the identity equivalence. -/
@[simp]
theorem congrRight_mk {r r' : Setoid X} (h : ∀ x₁ x₂, r x₁ x₂ ↔ r' x₁ x₂) (x : X) :
    Homeomorph.Quotient.congrRight h (Quotient.mk r x) = Quotient.mk r' x :=
  rfl

end Homeomorph.Quotient

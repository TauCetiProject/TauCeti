/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Evaluating the first isomorphism theorem on a class

Mathlib packages the first isomorphism theorem for a surjective homomorphism `φ : G →* M` as
`QuotientGroup.quotientKerEquivOfSurjective φ hφ : G ⧸ φ.ker ≃* M`. It is defined through
`QuotientGroup.quotientKerEquivOfRightInverse` applied to a right inverse extracted from `hφ`
by choice, so evaluating it on a class otherwise means unfolding that noncomputable
implementation. Likewise, `QuotientGroup.quotientKerEquivRange φ : G ⧸ φ.ker ≃* φ.range` is
built with `MulEquiv.ofBijective` from `QuotientGroup.rangeKerLift`, and Mathlib states no
evaluation rule for it.

This file records the computation rules on classes, so that users never have to. The first is
the group-theoretic counterpart of Mathlib's `RingHom.quotientKerEquivOfSurjective_apply_mk`;
both belong beside their definitions in Mathlib.

## Main statements

* `TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk`: the isomorphism
  `G ⧸ φ.ker ≃* M` sends the class of `g` to `φ g`; its additive counterpart is
  `TauCeti.QuotientAddGroup.quotientKerEquivOfSurjective_apply_mk`.
* `TauCeti.QuotientGroup.quotientKerEquivOfSurjective_symm_apply`: the inverse sends
  `φ g` back to the class of `g`; its additive counterpart is
  `TauCeti.QuotientAddGroup.quotientKerEquivOfSurjective_symm_apply`.
* `TauCeti.QuotientGroup.quotientKerEquivRange_apply_mk`: the isomorphism
  `G ⧸ φ.ker ≃* φ.range` sends the class of `g` to `φ g`; its additive counterpart is
  `TauCeti.QuotientAddGroup.quotientKerEquivRange_apply_mk`.
-/

public section

namespace TauCeti

namespace QuotientGroup

variable {G M : Type*} [Group G] [Group M] (φ : G →* M) (hφ : Function.Surjective φ)

/-- The first isomorphism theorem for a surjective homomorphism sends the class of `g` to
`φ g`. -/
@[to_additive (attr := simp) TauCeti.QuotientAddGroup.quotientKerEquivOfSurjective_apply_mk
  /-- The first isomorphism theorem for a surjective additive homomorphism sends the class of
  `g` to `φ g`. -/]
theorem quotientKerEquivOfSurjective_apply_mk (g : G) :
    _root_.QuotientGroup.quotientKerEquivOfSurjective φ hφ (_root_.QuotientGroup.mk g) = φ g :=
  rfl

/-- The inverse of the first isomorphism theorem sends `φ g` to the class of `g`. -/
@[to_additive (attr := simp)
  TauCeti.QuotientAddGroup.quotientKerEquivOfSurjective_symm_apply
  /-- The inverse of the additive first isomorphism theorem sends `φ g` to the class of `g`. -/]
theorem quotientKerEquivOfSurjective_symm_apply (g : G) :
    (_root_.QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm (φ g) =
      _root_.QuotientGroup.mk g := by
  simpa only [quotientKerEquivOfSurjective_apply_mk] using
    (_root_.QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm_apply_apply
      (_root_.QuotientGroup.mk g)

/-- The first isomorphism theorem onto the range sends the class of `g` to `φ g`. -/
@[to_additive (attr := simp) TauCeti.QuotientAddGroup.quotientKerEquivRange_apply_mk
  /-- The first isomorphism theorem onto the range of an additive homomorphism sends the class
  of `g` to `φ g`. -/]
theorem quotientKerEquivRange_apply_mk (g : G) :
    _root_.QuotientGroup.quotientKerEquivRange φ (_root_.QuotientGroup.mk g) =
      ⟨φ g, g, rfl⟩ :=
  rfl

end QuotientGroup

end TauCeti

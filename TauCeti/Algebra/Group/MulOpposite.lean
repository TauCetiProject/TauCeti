/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Equiv.Opposite

/-!
# Unopposing a commutative multiplication

Mathlib's `MulOpposite.opMulEquiv` identifies a commutative monoid with its opposite when
the commutativity is available as a `CommMonoid` instance. This file provides the
explicit-hypothesis variant: for any type with a multiplication that commutes, as a hypothesis
rather than an instance, the unopposite map is a multiplicative isomorphism. This is what makes the
opposite disappear in comparisons such as `TauCeti.Deck.IsRegular.fundamentalGroupDeckEquiv`,
where the deck group is commutative by a proof, not by an instance.
-/

public section

namespace TauCeti

namespace MulOpposite

variable {G : Type*} [Mul G]

/-- The unopposite map on a type whose multiplication commutes is a multiplicative isomorphism.
This is the explicit-hypothesis variant of `MulOpposite.opMulEquiv.symm`, for multiplications
whose commutativity is a hypothesis rather than a `CommMonoid` instance. -/
def unopMulEquivOfComm (hcomm : ∀ a b : G, a * b = b * a) : Gᵐᵒᵖ ≃* G where
  __ := MulOpposite.opEquiv.symm
  map_mul' _ _ := hcomm ..

@[simp]
lemma unopMulEquivOfComm_apply (hcomm : ∀ a b : G, a * b = b * a) (d : Gᵐᵒᵖ) :
    unopMulEquivOfComm hcomm d = d.unop :=
  (rfl)

@[simp]
lemma unopMulEquivOfComm_symm_apply (hcomm : ∀ a b : G, a * b = b * a) (a : G) :
    (unopMulEquivOfComm hcomm).symm a = MulOpposite.op a :=
  (rfl)

end MulOpposite

end TauCeti

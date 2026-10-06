/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Derivation.Basic

/-!
# Derivations vanish on idempotents

Every derivation of a commutative ring kills its idempotents: differentiating `e = e²` gives
`D e = 2 e • D e`, and multiplying by `e` then shows `e • D e = 0`.

Geometrically, an idempotent is locally constant on the spectrum, so its differential vanishes.
For an affine group, this says that a tangent vector at the identity does not see the other
connected components.
-/

public section

namespace Derivation

variable {R A M : Type*} [CommSemiring R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module A M] [Module R M]

/-- A derivation vanishes on every idempotent. -/
theorem apply_eq_zero_of_isIdempotentElem (D : Derivation R A M) {e : A}
    (he : IsIdempotentElem e) : D e = 0 := by
  have hD : D e = e • D e + e • D e := by
    conv_lhs => rw [← he.eq]
    exact D.leibniz e e
  have hsmul : e • D e = 0 := by
    have h := congrArg (e • ·) hD
    simp only [smul_add, smul_smul, he.eq] at h
    exact left_eq_add.mp h
  rw [hD, hsmul, add_zero]

end Derivation

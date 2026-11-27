/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ThetaLift.FrobeniusCycle.Basic
public import TauCeti.RingTheory.MvPolynomial.LinearSubst

/-!
# The twisted action of `GL_k(W)` on polynomials

Let `T` be a Frobenius cycle (`TauCeti.FrobeniusCycle`) with letters `s : ZMod N`. The group
`GL_k(W)` acts on polynomials over `R` in the variables `x (b, s)`, `b : Fin k`, by the twisted
action: `g` acts through the block diagonal matrix of its letter matrices `T.letterMatrix s g`, by
Tau Ceti's substitution of standard vectors `TauCeti.polynomialAction`. This file computes the
action on the variables and shows that it is an action.

## Main results

* `TauCeti.FrobeniusCycle.polynomialAction_letterMatrix_X`: the action on a variable, through `g`
  at even and its inverse transpose at odd letters.
* `TauCeti.FrobeniusCycle.polynomialAction_letterMatrix_mul`,
  `TauCeti.FrobeniusCycle.polynomialAction_letterMatrix_one`: it is an action.

The lemmas are adapted from the file `New/UpperBound/ElementaryDivisors/RootLemma.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

namespace TauCeti

open MvPolynomial Matrix

namespace FrobeniusCycle

variable {W : Type*} [CommRing W] [IsLocalRing W] {R : Type*} [CommRing R] {N k : ℕ} [NeZero N]
  (T : FrobeniusCycle W R N)

/-- The twisted action of `g` on a variable, through `g` at even and its inverse transpose at odd
letters. -/
theorem polynomialAction_letterMatrix_X (g : GL (Fin k) W) (z : Fin k × ZMod N) :
    polynomialAction (blockDiagonal (T.letterMatrix · g)) (X z) = ∑ b, C (T.ι z.2
      ((if T.isEven z.2 then g else GeneralLinearGroup.inverseTranspose g : GL (Fin k) W) b z.1)) *
        X (b, z.2) := by
  obtain ⟨c, s⟩ := z
  rw [polynomialAction_blockDiagonal_X]
  cases h : T.isEven s <;> simp [h, GeneralLinearGroup.coe_inverseTranspose]

/-- The twisted action is an action. -/
theorem polynomialAction_letterMatrix_mul (g h : GL (Fin k) W)
    (f : MvPolynomial (Fin k × ZMod N) R) :
    polynomialAction (blockDiagonal (T.letterMatrix · (g * h))) f =
      polynomialAction (blockDiagonal (T.letterMatrix · g))
        (polynomialAction (blockDiagonal (T.letterMatrix · h)) f) := by
  rw [← polynomialAction_mul_apply, ← blockDiagonal_mul]
  simp only [map_mul]

/-- The identity acts trivially. -/
theorem polynomialAction_letterMatrix_one (f : MvPolynomial (Fin k × ZMod N) R) :
    polynomialAction (blockDiagonal (T.letterMatrix · (1 : GL (Fin k) W))) f = f := by
  simp

end FrobeniusCycle

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Derivation.Basic

/-!
# Derivations vanish on numerals

A derivation vanishes on the image `(n : A)` of a natural number (`Derivation.map_natCast`). A
numeric literal `(OfNat.ofNat n : A)` with `2 ≤ n` is not syntactically such a cast, so `simp`
does not apply that lemma to it. This file adds the literal form `Derivation.map_ofNat`, so that
`simp` differentiates polynomial expressions with numeric coefficients, for instance partial
derivatives `MvPolynomial.pderiv i (3 * X 0 ^ 2)`.

## Main results

* `Derivation.map_ofNat`: a derivation vanishes on numeric literals.
-/

public section

namespace Derivation

variable {R A M : Type*} [CommSemiring R] [CommSemiring A] [AddCommMonoid M] [Algebra R A]
  [Module A M] [Module R M] (D : Derivation R A M)

/-- A derivation vanishes on numeric literals. -/
@[simp]
theorem map_ofNat (n : ℕ) [n.AtLeastTwo] : D (no_index (OfNat.ofNat n : A)) = 0 := by
  rw [← Nat.cast_ofNat, map_natCast]

end Derivation

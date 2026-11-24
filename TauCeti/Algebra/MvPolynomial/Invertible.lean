/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import TauCeti.Algebra.Ring.Invertible

/-!
# Invertibility of numeric literals in multivariate polynomial rings

Mathlib's `MvPolynomial.invertibleCoeNat` provides `Invertible (p : MvPolynomial σ R)` for explicit
`Nat.cast` coercions, which does not match Lean 4 `OfNat.ofNat` numeral literals during typeclass
resolution. `TauCeti.invertibleOfNatMvPolynomial` supplies the `OfNat` shortcut instance via
`TauCeti.invertibleMapOfNat` so that `[Invertible (3 : R)]` (and any `n ≥ 2`) automatically
synthesizes `Invertible (3 : MvPolynomial σ R)`.
-/

public section

namespace TauCeti

/-- A numeric literal `n ≥ 2` that is invertible in `R` is also invertible in `MvPolynomial σ R`.
Shortcut for typeclass resolution on `OfNat` numerals, complementing
`MvPolynomial.invertibleCoeNat`. -/
noncomputable instance invertibleOfNatMvPolynomial (σ R : Type*) (n : ℕ) [CommSemiring R]
    [n.AtLeastTwo] [Invertible (ofNat(n) : R)] : Invertible (ofNat(n) : MvPolynomial σ R) :=
  invertibleMapOfNat (algebraMap R (MvPolynomial σ R)) n

end TauCeti

end

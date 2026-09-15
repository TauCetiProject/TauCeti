/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.PrimeKernel
-- Proof-only: `#ker [n] = n ²`, which the dimension is read off from.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Kernel.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.FieldTheory.Finite.Basic

/-!
# The `ℓ`-torsion is a two-dimensional `ZMod ℓ`-vector space

For a prime `ℓ` invertible in an algebraically closed base field, `ker [ℓ]` is free of rank two
over `ZMod ℓ`. Every point of the kernel is killed by `ℓ`, which makes it a `ZMod ℓ`-module, and
`ZMod ℓ` is a field, so the kernel is a vector space whose cardinality `ℓ ²` reads off its
dimension.

Rank two is what lets an endomorphism act on the torsion as a `2 × 2` matrix over `ZMod ℓ`, which
is the form the degree and the trace are read off in.

## Main results

* `TauCeti.Isogeny.finrank_ker_mulByPrimeIsogeny`: it has dimension two.
* `TauCeti.Isogeny.nonempty_linearEquiv_ker_mulByPrimeIsogeny`: hence `E[ℓ] ≅ (ZMod ℓ) ²`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.4(b).
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]
  [IsAlgClosed F] {l : ℕ} [hl : Fact l.Prime]

/-- **`E[ℓ]` is two-dimensional over `ZMod ℓ`.** -/
@[simp]
theorem finrank_ker_mulByPrimeIsogeny (hchar : (l : F) ≠ 0) :
    Module.finrank (ZMod l) (mulByPrimeIsogeny W l).ker = 2 := by
  have : Module.Finite (ZMod l) (mulByPrimeIsogeny W l).ker := Module.Finite.of_finite
  have hpow := Module.natCard_eq_pow_finrank (K := ZMod l) (V := (mulByPrimeIsogeny W l).ker)
  rw [card_ker_mulByIntIsogeny W (by simpa using hchar), Int.natAbs_natCast, Nat.card_zmod] at hpow
  exact (Nat.pow_right_injective hl.out.two_le hpow).symm

/-- **`E[ℓ] ≅ (ZMod ℓ)²`**: the `ℓ`-torsion is free of rank two. -/
theorem nonempty_linearEquiv_ker_mulByPrimeIsogeny (hchar : (l : F) ≠ 0) :
    Nonempty ((mulByPrimeIsogeny W l).ker ≃ₗ[ZMod l] (Fin 2 → ZMod l)) := by
  have : Module.Finite (ZMod l) (mulByPrimeIsogeny W l).ker := Module.Finite.of_finite
  exact FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    (by simpa using finrank_ker_mulByPrimeIsogeny W hchar)

end TauCeti.Isogeny

end

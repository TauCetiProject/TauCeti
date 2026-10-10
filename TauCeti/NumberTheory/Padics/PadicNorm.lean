/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicNorm

/-!
# The `p`-adic norm of a prime power

For primes `p` and `ℓ`, the `p`-adic norm of `ℓ ^ d` is a power of `ℓ` itself: it is
`ℓ ^ (-d)` when `ℓ = p` and `1 = ℓ ^ 0` otherwise. Writing it uniformly as
`ℓ ^ (-v_p(ℓ ^ d))` lets the two cases be handled at once, as in formulas such as Tate's local
Euler characteristic formula where both the coefficient order and the cohomology orders are powers
of the same prime `ℓ`.

## Main results

* `TauCeti.padicNorm.prime_pow`: `|ℓ ^ d|_p = ℓ ^ (-v_p(ℓ ^ d))` for primes `p` and `ℓ`.
-/

public section

namespace TauCeti.padicNorm

/-- For primes `p` and `ℓ`, the `p`-adic norm of `ℓ ^ d` is `ℓ ^ (-v_p(ℓ ^ d))`: this is
`ℓ ^ (-d)` when `ℓ = p` and `1` otherwise. -/
theorem prime_pow (p : ℕ) [Fact p.Prime] {ℓ : ℕ} (hℓ : ℓ.Prime) (d : ℕ) :
    padicNorm p ((ℓ : ℚ) ^ d) = (ℓ : ℚ) ^ (-(padicValNat p (ℓ ^ d) : ℤ)) := by
  rw [← Nat.cast_pow, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast (pow_pos hℓ.pos d).ne'),
    padicValRat.of_nat]
  rcases eq_or_ne ℓ p with rfl | hne
  · rfl
  · rw [padicValNat.eq_zero_of_not_dvd fun h ↦ hne ((Nat.prime_dvd_prime_iff_eq Fact.out hℓ).1
      ((Fact.out : p.Prime).dvd_of_dvd_pow h)).symm]
    simp

end TauCeti.padicNorm

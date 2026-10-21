/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Divisibility of powers in integrally closed subrings

Mathlib's `IsIntegrallyClosed.pow_dvd_pow_iff` says that in an integrally closed domain
`a ^ n ∣ b ^ n` implies `a ∣ b` for `n ≠ 0`. The same holds in a ring `R` integrally closed in an
algebra `A`, with no domain hypothesis, provided `a` becomes invertible in `A`: then `b / a ∈ A` is
a root of `X ^ n - c` with `c ∈ R`, hence comes from `R`.

For the ring `R°` of power-bounded elements of a Tate ring and a pseudouniformiser `a`, this is
why Frobenius `R° ⧸ a →+* R° ⧸ a ^ p` is injective.

## Main results

* `IsIntegrallyClosedIn.pow_dvd_pow_iff`: if `R` is integrally closed in `A` and `a ∈ R` becomes a
  unit in `A`, then `a ^ n ∣ b ^ n` in `R` with `n ≠ 0` exactly when `a ∣ b` in `R`.
-/

public section

namespace IsIntegrallyClosedIn

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsIntegrallyClosedIn R A]

/-- **Roots of divisibility in an integrally closed subring.** If `R` is integrally closed in `A`
and `a ∈ R` is a unit of `A`, then for `n ≠ 0`, `a ^ n ∣ b ^ n` in `R` exactly when `a ∣ b` in
`R`. Compare `IsIntegrallyClosed.pow_dvd_pow_iff`, which instead asks `R` to be an integrally
closed domain. -/
theorem pow_dvd_pow_iff {n : ℕ} (hn : n ≠ 0) {a b : R} (ha : IsUnit (algebraMap R A a)) :
    a ^ n ∣ b ^ n ↔ a ∣ b := by
  refine ⟨fun ⟨c, hc⟩ ↦ ?_, fun h ↦ pow_dvd_pow_of_dvd h n⟩
  obtain ⟨u, hu⟩ := ha
  -- `x = b / a` satisfies `x ^ n = c`, so it is integral over `R` and comes from `R`.
  have hx : (algebraMap R A b * ↑u⁻¹) ^ n = algebraMap R A c := by
    rw [mul_pow, ← map_pow, hc, map_mul, map_pow, ← hu, mul_right_comm, ← mul_pow, Units.mul_inv,
      one_pow, one_mul]
  obtain ⟨y, hy⟩ := exists_algebraMap_eq_of_isIntegral_pow (Nat.pos_of_ne_zero hn)
    (hx ▸ isIntegral_algebraMap)
  refine ⟨y, IsIntegralClosure.algebraMap_injective R R A ?_⟩
  rw [map_mul, hy, ← hu, mul_left_comm, Units.mul_inv, mul_one]

end IsIntegrallyClosedIn

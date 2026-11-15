/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius

/-!
# The `p`-th power map of a ring in which a prime `p` vanishes

If `p` is a prime and `p = 0` in a commutative semiring `R`, then `x ↦ x ^ p` is a ring
endomorphism of `R`. Mathlib's `frobenius R p` packages this under the hypothesis
`ExpChar R p`, which the zero ring does not satisfy for a prime `p`. The sections of the structure
sheaf of a scheme over `𝔽_p` include the zero ring (the sections over the empty open), so the
absolute Frobenius of such a scheme is built from `TauCeti.powRingHom`, which only asks that `p`
vanish in `R`.

## Main definitions

* `TauCeti.powRingHom R p h`: the ring endomorphism `x ↦ x ^ p` of `R`, for `h : (p : R) = 0`.

## Main results

* `TauCeti.powRingHom_eq_frobenius`: when `R` has exponential characteristic `p`, it is
  `frobenius R p`.
-/

public section

namespace TauCeti

variable (R : Type*) [CommSemiring R] (p : ℕ) [hp : Fact p.Prime]

/-- The `p`-th power map `x ↦ x ^ p` on a commutative semiring in which the prime `p` vanishes,
as a ring endomorphism. Unlike `frobenius R p`, it is defined for the zero ring. -/
def powRingHom (h : (p : R) = 0) : R →+* R where
  __ := powMonoidHom p
  map_zero' := zero_pow hp.out.ne_zero
  map_add' x y := by simp [add_pow_prime_eq hp.out, h]

variable {R p}

@[simp]
theorem powRingHom_apply (h : (p : R) = 0) (x : R) : powRingHom R p h x = x ^ p := (rfl)

/-- When `R` has exponential characteristic `p`, the `p`-th power map is the Frobenius. -/
theorem powRingHom_eq_frobenius [ExpChar R p] (h : (p : R) = 0) :
    powRingHom R p h = frobenius R p :=
  RingHom.ext fun x ↦ by rw [powRingHom_apply, frobenius_def]

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Star
public import TauCeti.Algebra.TemperleyLieb.Trace.Basic
public import Mathlib.Algebra.Order.Star.Basic

/-!
# Positivity of Markov traces at zero loop parameter

At loop parameter `δ = 0`, every unnormalized Markov trace vanishes on one or more strands
(`TauCeti.TemperleyLieb.IsMarkovTrace.eq_zero_of_loop_zero`), while on zero strands
`TemperleyLieb R 0 0 ≃ₐ[R] R` via `aug`, so `tr 0 (star x * x) = star (aug x) * aug x`.

Consequently, over any commutative star-ordered semiring `R`, the Hermitian trace form
`tr n (star x * x)` is nonnegative on every number of strands, and over a commutative
star-ordered ring the signed form `(-1) ^ n * tr n (star x * x)` is likewise nonnegative on
every number of strands. These elementary zero-parameter positivity results depend only on the
abstract trace and star structures, without pulling in analytic Jones positivity or the sign
isomorphism.

## Main results

* `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_zero`: nonnegativity of
  `tr n (star x * x)` at `δ = 0` over any commutative star-ordered semiring.
* `TauCeti.TemperleyLieb.IsMarkovTrace.neg_one_pow_mul_map_star_mul_self_nonneg_zero`:
  nonnegativity of `(-1) ^ n * tr n (star x * x)` at `δ = 0` over any commutative star-ordered
  ring.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4, Sections 4.3–4.5.
-/

public section

namespace TauCeti.TemperleyLieb.IsMarkovTrace

/-- At loop parameter `δ = 0` over a commutative star-ordered semiring, the form `tr n (x⋆ * x)` of
a Markov trace is nonnegative on every number of strands. -/
theorem map_star_mul_self_nonneg_zero
    {R : Type*} [CommSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [Fact (IsSelfAdjoint (0 : R))] {tr : ∀ n : ℕ, TemperleyLieb R 0 n →ₗ[R] R}
    (htr : IsMarkovTrace R 0 tr) :
    ∀ (n : ℕ) (x : TemperleyLieb R 0 n), 0 ≤ tr n (star x * x)
  | 0, x => by
    have hx : x = algebraMap R (TemperleyLieb R 0 0) (aug x) := by
      simpa using ((algEquivOfLeOne (R := R) 0 (Nat.zero_le 1)).symm_apply_apply x).symm
    rw [hx]
    simp [Algebra.algebraMap_eq_smul_one, htr.map_one]
  | n + 1, x => by simp [htr.eq_zero_of_loop_zero n]

/-- At loop parameter `δ = 0` over a commutative star-ordered ring, the signed form
`(-1) ^ n * tr n (x⋆ * x)` of a Markov trace is nonnegative on every number of strands. -/
theorem neg_one_pow_mul_map_star_mul_self_nonneg_zero
    {R : Type*} [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [Fact (IsSelfAdjoint (0 : R))] {tr : ∀ n : ℕ, TemperleyLieb R 0 n →ₗ[R] R}
    (htr : IsMarkovTrace R 0 tr) :
    ∀ (n : ℕ) (x : TemperleyLieb R 0 n), 0 ≤ (-1 : R) ^ n * tr n (star x * x)
  | 0, x => by simpa using htr.map_star_mul_self_nonneg_zero 0 x
  | n + 1, x => by simp [htr.eq_zero_of_loop_zero n]

end TauCeti.TemperleyLieb.IsMarkovTrace

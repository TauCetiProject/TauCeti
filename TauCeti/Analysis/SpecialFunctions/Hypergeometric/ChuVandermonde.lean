/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import TauCeti.RingTheory.Polynomial.Pochhammer

/-!
# The Chu–Vandermonde identity

For `n : ℕ`, the terminating Gauss hypergeometric series at `z = 1` is

`₂F₁(−n, b; c; 1) = (c − b)ₙ / (c)ₙ`  (DLMF 15.4.24),

whenever `(c)ₙ ≠ 0`. This is the case `a = −n` of Gauss's summation theorem; here it is proved
directly, over any topological field of characteristic zero, from the finite-sum form
`TauCeti.ordinaryHypergeometric_neg_nat_eq_sum` and the Pochhammer form of Chu–Vandermonde
`TauCeti.sum_neg_one_pow_mul_choose_ascPochhammer`.

## Main results

* `TauCeti.ordinaryHypergeometric_neg_nat_one`: DLMF 15.4.24.

## Implementation notes

The hypothesis is `(c)ₙ ≠ 0`, which allows `c = −m` with `m ≥ n`; then `(c)ₖ ≠ 0` for `k ≤ n`
and the series stops before Mathlib's junk inverse `0⁻¹` is reached.

## References

* NIST Digital Library of Mathematical Functions, 15.4.24, <https://dlmf.nist.gov/15.4.E24>.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), files
`DLMF/Hypergeometric/EulerIntegral.lean` and `DLMF/Hypergeometric/Basic/GaussSeries.lean`.
-/

public section

open Finset Polynomial
open scoped Nat

namespace TauCeti

variable {K : Type*} [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K]

/-- **Chu–Vandermonde** (DLMF 15.4.24): `₂F₁(−n, b; c; 1) = (c − b)ₙ / (c)ₙ` when `(c)ₙ ≠ 0`. -/
theorem ordinaryHypergeometric_neg_nat_one (n : ℕ) (b : K) {c : K}
    (hc : (ascPochhammer K n).eval c ≠ 0) :
    ordinaryHypergeometric (-n : K) b c (1 : K) =
      (ascPochhammer K n).eval (c - b) / (ascPochhammer K n).eval c := by
  rw [ordinaryHypergeometric_neg_nat_eq_sum, eq_div_iff hc, sum_mul,
    ← sum_neg_one_pow_mul_choose_ascPochhammer]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  -- `(c)ₙ = (c)ₖ (c + k)ₙ₋ₖ`, so `(c)ₖ ≠ 0` and the `k`-th term can be cleared.
  have hadd := ascPochhammer_eval_add c k (n - k)
  rw [Nat.add_sub_of_le hk'] at hadd
  have hck : (ascPochhammer K k).eval c ≠ 0 := by
    intro h
    rw [hadd, h, zero_mul] at hc
    exact hc rfl
  have hkf : (k ! : K) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [hadd, ascPochhammer_eval_neg_natCast, one_pow, smul_eq_mul, mul_one]
  field_simp

end TauCeti

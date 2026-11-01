/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Polynomial.Tower
public import TauCeti.Algebra.Polynomial.DivX

/-!
# Tails of a polynomial relation are integral

Let `x` be a root of a polynomial `p = a₀ + a₁ X + ⋯ + a_d X^d` over a commutative ring `R`.
The leading coefficient need not be a unit, so `x` itself need not be integral over `R`, but
`a_d x` is (`isIntegral_leadingCoeff_smul`). This file proves the same for every *tail* of the
relation: for each `k`, the element

```text
x * (a_k + a_{k+1} x + ⋯ + a_d x^(d-k)) = a_k x + a_{k+1} x² + ⋯ + a_d x^(d-k+1)
```

is integral over `R`. The polynomial `a_k + a_{k+1} X + ⋯ + a_d X^(d-k)` is the `k`-th iterate
`divX^[k] p` of `Polynomial.divX`.

The proof is a downward induction on `k`. If the tail at `k + 1` is integral, then so is
`c = a_k + a_{k+1} x + ⋯`, and `x` is a root of `c X^k + a_{k-1} X^(k-1) + ⋯ + a₀`, a polynomial
over the integral closure of `R` with leading coefficient `c`; hence `c x` is integral over the
integral closure, and so over `R`.

For a valuation ring `O'` of an algebraic extension `L` of a field `K` lying over a valuation
ring `O` of `K`, these elements produce, for each `x ∈ O'`, an element `u` of the integral closure
`C` of `O` in `L` that is a unit of `O'` with `x u ∈ C`.

## Main results

* `Polynomial.isIntegral_mul_aeval_iterate_divX`: `x * p_k(x)` is integral, where
  `p_k = divX^[k] p` and `x` is a root of `p`.
-/

public section

open Polynomial

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- If `c x^k + L(x) = 0` with `L` of degree below `k`, then `c x` is integral over `R`. -/
private theorem isIntegral_smul_of_aeval_C_mul_X_pow_add {k : ℕ} {c : R} {L : R[X]}
    (hL : L.degree < k) {x : S} (h : aeval x (C c * X ^ k + L) = 0) : IsIntegral R (c • x) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simpa using isIntegral_zero
  have hdeg : L.degree < (C c * X ^ k).degree := by rwa [degree_C_mul_X_pow k hc]
  have := isIntegral_leadingCoeff_smul _ x h
  rwa [add_comm, leadingCoeff_add_of_degree_lt hdeg, leadingCoeff_C_mul_X_pow] at this

/-- **Tails of a polynomial relation are integral.** If `x` is a root of `p`, then for every `k`
the element `x * (divX^[k] p)(x) = a_k x + a_{k+1} x² + ⋯ + a_d x^(d-k+1)` is integral over `R`.
For `k = natDegree p` this is `isIntegral_leadingCoeff_smul`. -/
theorem isIntegral_mul_aeval_iterate_divX {p : R[X]} {x : S} (hx : aeval x p = 0) (k : ℕ) :
    IsIntegral R (x * aeval x (divX^[k] p)) := by
  -- downward induction on `k`, starting above the degree of `p`
  suffices ∀ m k, p.natDegree < k + m → IsIntegral R (x * aeval x (divX^[k] p)) from
    this (p.natDegree + 1) k (by omega)
  intro m
  induction m with
  | zero =>
    intro k hk
    rw [iterate_divX_eq_zero_of_natDegree_lt (m := k) (by omega), map_zero, mul_zero]
    exact isIntegral_zero
  | succ m ih =>
    intro k hk
    -- the value `c` of `divX^[k] p` at `x` is integral, by the tail at `k + 1`
    have hc : IsIntegral R (aeval x (divX^[k] p)) := by
      rw [← iterate_divX_succ_mul_X_add_C, map_add, map_mul, aeval_X, aeval_C, mul_comm]
      exact (ih (k + 1) (by omega)).add (isIntegral_algebraMap (R := R) (A := S))
    -- over the integral closure, `x` is a root of `c X^k + L`
    let c : integralClosure R S := ⟨_, hc⟩
    set L := p - X ^ k * divX^[k] p
    have hroot : aeval x (C c * X ^ k + L.map (algebraMap R (integralClosure R S))) = 0 := by
      rw [map_add, aeval_map_algebraMap, map_mul, aeval_C, Subalgebra.algebraMap_apply, map_pow,
        aeval_X, map_sub, map_mul, map_pow, aeval_X, hx, mul_comm, zero_sub, add_neg_cancel]
    have := isIntegral_smul_of_aeval_C_mul_X_pow_add
      (degree_map_le.trans_lt (degree_sub_X_pow_mul_iterate_divX_lt k p)) hroot
    rw [Subalgebra.smul_def, smul_eq_mul, mul_comm] at this
    exact isIntegral_trans _ this

end Polynomial

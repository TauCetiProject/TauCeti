/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# `p`-th powers of polynomials in characteristic `p`

In exponential characteristic `p`, the `p`-th power of a polynomial `f` is `f` with `X` replaced
by `X ^ p` and each coefficient raised to the `p`-th power. This file records the resulting
coefficient formula, and the expansion of `∑ gᵢ ^ p (a + b X ^ p) ^ i` in the monomials
`a ^ m b ^ j` with coefficients that are again `p`-th powers.

## Main results

* `Polynomial.coeff_pow_char_mul`: the coefficient of `X ^ (p n)` in `f ^ p` is `f.coeff n ^ p`.
* `TauCeti.sum_pow_mul_C_add_C_mul_X_pow`: `∑_{i < p} gᵢ ^ p (a + b X ^ p) ^ i` written in the
  monomials `a ^ m b ^ j` with `m, j < p`.
-/

public section

open Polynomial Finset

variable {R : Type*} [CommSemiring R] {p : ℕ} [ExpChar R p]

namespace Polynomial

/-- In exponential characteristic `p`, the coefficient of `X ^ (p n)` in `f ^ p` is the `p`-th
power of the coefficient of `X ^ n` in `f`. -/
@[simp]
theorem coeff_pow_char_mul (f : R[X]) (n : ℕ) : (f ^ p).coeff (p * n) = f.coeff n ^ p := by
  rw [← map_frobenius_expand, coeff_map, coeff_expand_mul' (expChar_pos R p), frobenius_def]

end Polynomial

namespace TauCeti

/-- In exponential characteristic `p`, expanding `(a + b X ^ p) ^ i` writes
`∑_{i < p} gᵢ ^ p (a + b X ^ p) ^ i` in the monomials `a ^ m b ^ j`, whose coefficient is
`(binom(m + j, j) g_{m + j} X ^ j) ^ p` for `m + j < p`. -/
theorem sum_pow_mul_C_add_C_mul_X_pow (a b : R) (g : ℕ → R[X]) :
    ∑ i ∈ range p, g i ^ p * (C a + C b * X ^ p) ^ i =
      ∑ m ∈ range p, ∑ j ∈ range p, (if m + j < p then
        ((m + j).choose j : R[X]) * g (m + j) * X ^ j else 0) ^ p * C (a ^ m * b ^ j) := by
  have key : ∀ i ∈ range p, g i ^ p * (C a + C b * X ^ p) ^ i =
      ∑ j ∈ range (i + 1), (((i - j + j).choose j : R[X]) * g (i - j + j) * X ^ j) ^ p *
        C (a ^ (i - j) * b ^ j) := by
    intro i _
    rw [add_comm, add_pow, mul_sum]
    refine sum_congr rfl fun j hj ↦ ?_
    rw [Nat.sub_add_cancel (Nat.lt_succ_iff.mp (mem_range.mp hj))]
    have hc : ((i.choose j : ℕ) : R[X]) ^ p = i.choose j := by
      rw [← frobenius_def, map_natCast]
    simp only [mul_pow, hc, map_mul, map_pow]
    ring
  rw [sum_congr rfl key]
  simp only [ite_pow, zero_pow (expChar_ne_zero R p), ite_mul, zero_mul]
  rw [sum_sigma', ← sum_product', ← sum_filter]
  refine sum_nbij' (fun s ↦ (s.1 - s.2, s.2)) (fun q ↦ ⟨q.1 + q.2, q.2⟩) ?_ ?_ ?_ ?_ ?_
  · simp only [mem_sigma, mem_range, mem_filter, mem_product]
    omega
  · simp only [mem_sigma, mem_range, mem_filter, mem_product]
    omega
  · rintro ⟨i, j⟩ h
    simp only [mem_sigma, mem_range] at h
    simp only [Sigma.mk.injEq, heq_eq_eq, and_true]
    omega
  · rintro ⟨m, j⟩ _
    simp
  · rintro ⟨i, j⟩ _
    rfl

end TauCeti

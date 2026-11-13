/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Mathlib.Algebra.BigOperators.Field

/-!
# The finite product of `sin(πk/m)`

This file proves `∏_{k=1}^{m-1} sin(π k / m) = m / 2^{m-1}`, from the product of `1 − μ` over
the nontrivial `m`-th roots of unity `μ`.

## Main results

* `Complex.one_sub_exp_mul_I`: `1 − e^{iθ} = −2i e^{iθ/2} sin(θ/2)`.
* `Complex.prod_one_sub_exp_two_pi_mul_I_div_pow`: `∏_{k=1}^{m-1} (1 − e^{2πik/m}) = m`.
* `Real.prod_sin_pi_mul_div`: `∏_{k=1}^{m-1} sin(π k / m) = m / 2^{m-1}`.

## References

* G. E. Andrews, R. Askey, R. Roy, *Special Functions*, proof of Theorem 1.5.2.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>),
file `DLMF/Gamma/Multiplication.lean`.
-/

@[expose] public section

open Finset

open scoped Real

namespace Complex

/-- `1 − e^{iθ} = −2i e^{iθ/2} sin(θ/2)`. -/
theorem one_sub_exp_mul_I (θ : ℂ) :
    1 - exp (I * θ) = -2 * I * exp (I * θ / 2) * sin (θ / 2) := by
  convert_to 1 - exp (2 * I * (θ / 2)) = -2 * I * exp (I * (θ / 2)) * sin (θ / 2)
  · congr 1; ring_nf
  · ring_nf
  generalize θ / 2 = ω
  have h0 : exp (I * ω) * exp (-I * ω) = 1 := by
    rw [← exp_add, ← exp_zero]
    congr 1
    ring
  have h1 : exp (I * ω) * exp (I * ω) = exp (2 * I * ω) := by
    rw [← exp_add]
    congr 1
    ring
  have hL : -2 * I * exp (I * ω) * sin ω = -I * exp (I * ω) * (2 * sin ω) := by ring
  rw [hL, two_sin]
  have hneg : -ω * I = -I * ω := by ring
  have hpos : ω * I = I * ω := mul_comm _ _
  simp_rw [hneg, hpos]
  have hR : -I * exp (I * ω) * ((exp (-I * ω) - exp (I * ω)) * I) =
      -(I * I) * (exp (I * ω) * exp (-I * ω) - exp (I * ω) * exp (I * ω)) := by
    ring
  rw [hR, I_mul_I, h0, h1]
  ring

/-- The product of `1 − μ` over the nontrivial `m`-th roots of unity `μ = e^{2πik/m}`,
`1 ≤ k ≤ m − 1`, is `m`. -/
theorem prod_one_sub_exp_two_pi_mul_I_div_pow {m : ℕ} (hm : 0 < m) :
    ∏ k ∈ range (m - 1), (1 - exp (2 * π * I / m) ^ (k + 1)) = m := by
  have hμ : IsPrimitiveRoot (exp (2 * π * I / m)) (m - 1 + 1) := by
    simpa [Nat.sub_one_add_one_eq_of_pos hm] using isPrimitiveRoot_exp m hm.ne'
  have h := hμ.prod_one_sub_pow_eq_order
  have heq : (↑(m - 1) + 1 : ℂ) = m := by
    rw [← Nat.cast_succ, Nat.succ_eq_add_one, Nat.sub_one_add_one_eq_of_pos hm]
  exact h.trans heq

/-- `exp(∑_{k<m-1} iπ(k + 1)/m) = i^(m-1)` for `m > 0`. -/
private theorem exp_sum_pi_div {m : ℕ} (hm : 0 < m) :
    exp (∑ k ∈ range (m - 1), I * π * (k + 1) / m) = I ^ (m - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hm0 : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.succ_ne_zero
  have hgauss : (∑ k ∈ range n, ((k : ℂ) + 1)) * 2 = n * (n + 1) := by
    have h := sum_range_id_mul_two (n + 1)
    rw [sum_range_succ', Nat.add_sub_cancel, add_zero] at h
    have hc : ((∑ k ∈ range n, (k + 1) : ℕ) : ℂ) * 2 = ((n + 1) * n : ℕ) := by
      exact_mod_cast h
    push_cast at hc
    linear_combination hc
  have hsum : ∑ k ∈ range n, I * π * (k + 1) / ((n + 1 : ℕ) : ℂ) = n * (π / 2 * I) := by
    rw [← Finset.sum_div, ← mul_sum, div_eq_iff hm0]
    push_cast
    linear_combination (I * π / 2) * hgauss
  rw [Nat.add_sub_cancel, hsum, exp_nat_mul, exp_pi_div_two_mul_I]

/-- With `ω = e^(2πi/m)`: `1 - ω^(k+1) = -2i e^(iπ(k+1)/m) sin(π(k + 1)/m)`. -/
private theorem one_sub_root_eq_sin {m k : ℕ} (hm : 0 < m) :
    (1 : ℂ) - exp (2 * π * I / m) ^ (k + 1) =
      -2 * I * exp (I * π * (k + 1) / m) * (Real.sin (π * (k + 1 : ℝ) / m) : ℂ) := by
  have hpow : exp (2 * π * I / m) ^ (k + 1) = exp (I * (2 * π * (k + 1) / m)) := by
    rw [← exp_nat_mul]
    congr 1
    push_cast
    ring
  have hid := one_sub_exp_mul_I (2 * π * (k + 1 : ℂ) / m)
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have harg : (2 * π * (k + 1 : ℂ) / m) / 2 = π * (k + 1 : ℂ) / m := by field
  have hcast : (π * (k + 1 : ℂ) / m) = ↑(π * (k + 1 : ℝ) / m) := by
    push_cast
    ring
  rw [hpow, hid, harg, hcast, ofReal_sin]
  congr 2
  ring_nf

/-- `(-2i)ⁿ iⁿ = 2ⁿ`. -/
private theorem pow_neg_two_I_mul_I (n : ℕ) : (-2 * I : ℂ) ^ n * I ^ n = (2 : ℂ) ^ n := by
  rw [mul_pow, mul_assoc, ← pow_add, ← two_mul, pow_mul, I_sq, ← mul_pow]
  norm_num

end Complex

namespace Real

/-- `∏_{k=1}^{m-1} sin(π k / m) = m / 2^{m-1}`. Empty product when `m = 1`. -/
theorem prod_sin_pi_mul_div {m : ℕ} (hm : 0 < m) :
    ∏ k ∈ Ico 1 m, sin (π * k / m) = m / (2 : ℝ) ^ (m - 1) := by
  have hrange :
      ∏ k ∈ range (m - 1), sin (π * (k + 1 : ℝ) / m) =
        ∏ k ∈ Ico 1 m, sin (π * k / m) := by
    simpa [add_comm] using
      (prod_Ico_eq_prod_range (fun k : ℕ => sin (π * k / m)) 1 m).symm
  have hμ := Complex.prod_one_sub_exp_two_pi_mul_I_div_pow hm
  have hprod :
      ∏ k ∈ range (m - 1),
          ((1 : ℂ) - Complex.exp (2 * π * Complex.I / m) ^ (k + 1)) =
        (-2 * Complex.I) ^ (m - 1) * Complex.I ^ (m - 1) *
          ∏ k ∈ range (m - 1), (sin (π * (k + 1 : ℝ) / m) : ℂ) := by
    simp_rw [Complex.one_sub_root_eq_sin hm]
    rw [prod_mul_distrib, prod_mul_distrib, prod_const, card_range,
      ← Complex.exp_sum, Complex.exp_sum_pi_div hm]
  have hmain : (m : ℂ) =
      (2 : ℂ) ^ (m - 1) *
        ↑(∏ k ∈ range (m - 1), sin (π * (k + 1 : ℝ) / m)) := by
    calc
      (m : ℂ) = ∏ k ∈ range (m - 1),
          (1 - Complex.exp (2 * π * Complex.I / m) ^ (k + 1)) := hμ.symm
      _ = (-2 * Complex.I) ^ (m - 1) * Complex.I ^ (m - 1) *
            ∏ k ∈ range (m - 1), (sin (π * (k + 1 : ℝ) / m) : ℂ) := hprod
      _ = (2 : ℂ) ^ (m - 1) *
            ↑(∏ k ∈ range (m - 1), sin (π * (k + 1 : ℝ) / m)) := by
          rw [Complex.pow_neg_two_I_mul_I, Complex.ofReal_prod]
  have hreal : (m : ℝ) =
      (2 : ℝ) ^ (m - 1) *
        ∏ k ∈ range (m - 1), sin (π * (k + 1 : ℝ) / m) := by
    apply Complex.ofReal_injective
    simpa [Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_natCast] using hmain
  have hne : ((2 : ℝ) ^ (m - 1)) ≠ 0 := pow_ne_zero _ two_ne_zero
  calc
    ∏ k ∈ Ico 1 m, sin (π * k / m)
      = ∏ k ∈ range (m - 1), sin (π * (k + 1 : ℝ) / m) := hrange.symm
    _ = m / (2 : ℝ) ^ (m - 1) :=
        (eq_div_iff_mul_eq hne).2 (by rw [mul_comm]; exact hreal.symm)

end Real

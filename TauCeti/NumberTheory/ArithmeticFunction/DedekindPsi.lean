/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticFunction.JordanTotient
import Mathlib.Tactic.FieldSimp

/-!
# The Dedekind ψ function

The Dedekind ψ function `ψ = μ² * id`, so `ψ n = ∑_{d ∣ n} μ d ^ 2 * (n / d)`, has the Euler
product `ψ n = n * ∏_{p ∣ n} (1 + p⁻¹)`, and it is the factor of Jordan's totient function `J₂`
complementary to Euler's totient function: `ψ n * φ n = J₂ n`.

## Main definitions and results

* `ArithmeticFunction.dedekindPsi`: the Dedekind ψ function `ψ = μ² * id`, with integer values.
* `ArithmeticFunction.dedekindPsi_eq_prod`: the Euler product `ψ n = n * ∏_{p ∣ n} (1 + p⁻¹)`.
* `ArithmeticFunction.dedekindPsi_apply_prime_pow`: `ψ (p ^ k) = p ^ (k - 1) * (p + 1)`.
* `ArithmeticFunction.dedekindPsi_mul_totient`: `ψ n * φ n = J₂ n`.

## References

* L. E. Dickson, *History of the theory of numbers*, Vol. I, Chapter V.
-/

public section

open Finset

namespace ArithmeticFunction

open scoped ArithmeticFunction.Moebius

/-- The Dedekind ψ function `ψ = μ² * id`, so that `ψ n = ∑_{d ∣ n} μ d ^ 2 * (n / d)`
(`dedekindPsi_apply`) and `ψ n = n * ∏_{p ∣ n} (1 + p⁻¹)` for `n ≠ 0` (`dedekindPsi_eq_prod`).
For `N ≠ 0`, `ψ N` is the index of the congruence subgroup `Γ₀(N)` in `SL₂(ℤ)`, compare
`CongruenceSubgroup.Gamma0_index_mul_prod_primeFactors`. -/
def dedekindPsi : ArithmeticFunction ℤ :=
  pmul μ μ * (ArithmeticFunction.id : ArithmeticFunction ℤ)

theorem dedekindPsi_def :
    dedekindPsi = pmul μ μ * (ArithmeticFunction.id : ArithmeticFunction ℤ) := (rfl)

theorem dedekindPsi_apply (n : ℕ) :
    dedekindPsi n = ∑ d ∈ n.divisors, μ d ^ 2 * ((n / d : ℕ) : ℤ) := by
  rw [dedekindPsi_def, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal
      (fun a b ↦ pmul μ μ a * (ArithmeticFunction.id : ArithmeticFunction ℤ) b)]
  simp [pmul_apply, natCoe_apply, sq]

/-- `ψ` is multiplicative. -/
@[arith_mult]
theorem isMultiplicative_dedekindPsi : dedekindPsi.IsMultiplicative :=
  (isMultiplicative_moebius.pmul isMultiplicative_moebius).mul isMultiplicative_id.natCast

/-- `ψ 1 = 1`. -/
@[simp]
theorem dedekindPsi_apply_one : dedekindPsi 1 = 1 :=
  isMultiplicative_dedekindPsi.map_one

/-- The Euler product of the Dedekind ψ function: `ψ n = n * ∏_{p ∣ n} (1 + p⁻¹)` for
`n ≠ 0`. -/
theorem dedekindPsi_eq_prod {R : Type*} [Field R] [CharZero R] {n : ℕ} (hn : n ≠ 0) :
    (dedekindPsi n : R) = n * ∏ p ∈ n.primeFactors, (1 + (p : R)⁻¹) := by
  -- the multiplicative function `d ↦ μ d * d⁻¹`, made zero at `0`
  let f : ArithmeticFunction R := ⟨fun d ↦ if d = 0 then 0 else μ d * (d : R)⁻¹, by simp⟩
  have hf : f.IsMultiplicative := by
    refine IsMultiplicative.iff_ne_zero.2 ⟨by simp [f], fun {m d} hm hd hmd ↦ ?_⟩
    simp only [f, coe_mk, mul_ne_zero hm hd, hm, hd, ite_false,
      isMultiplicative_moebius.map_mul_of_coprime hmd]
    push_cast
    ring
  have hprod : ∏ p ∈ n.primeFactors, (1 + (p : R)⁻¹) = ∏ p ∈ n.primeFactors, (1 - f p) :=
    Finset.prod_congr rfl fun p hp ↦ by
      have hp := Nat.prime_of_mem_primeFactors hp
      simp [f, hp.ne_zero, moebius_apply_prime hp]
  rw [hprod, hf.prodPrimeFactors_one_sub f hn, dedekindPsi_apply, Int.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  have hdR : (d : R) ≠ 0 := Nat.cast_ne_zero.2 hd0
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, coe_mk, f, hd0, ite_false,
    Nat.cast_div (Nat.dvd_of_mem_divisors hd) hdR]
  field_simp

/-- At a prime power, `ψ (p ^ k) = p ^ (k - 1) * (p + 1)` for `k ≠ 0`. -/
theorem dedekindPsi_apply_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    dedekindPsi (p ^ k) = (p : ℤ) ^ (k - 1) * (p + 1) := by
  have h := dedekindPsi_eq_prod (R := ℚ) (pow_ne_zero k hp.ne_zero)
  rw [Nat.primeFactors_prime_pow hk hp, Finset.prod_singleton] at h
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt (Nat.pos_of_ne_zero hk)
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  refine Int.cast_injective (α := ℚ) (h.trans ?_)
  push_cast
  field_simp
  ring

/-- At a prime `p`, `ψ p = p + 1`. -/
@[simp]
theorem dedekindPsi_apply_prime {p : ℕ} (hp : p.Prime) : dedekindPsi p = p + 1 := by
  simpa using dedekindPsi_apply_prime_pow hp one_ne_zero

/-- `ψ` and Euler's totient function multiply to `J₂`: `ψ n * φ n = J₂ n`. -/
theorem dedekindPsi_mul_totient (n : ℕ) : dedekindPsi n * n.totient = jordanTotient 2 n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  refine Int.cast_injective (α := ℚ) ?_
  push_cast
  rw [dedekindPsi_eq_prod hn, Nat.totient_eq_mul_prod_factors, jordanTotient_eq_prod 2 hn,
    mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← sq]
  congr 1
  refine Finset.prod_congr rfl fun p _ ↦ ?_
  ring

/-- The Dedekind ψ function is positive away from `0`. -/
theorem dedekindPsi_pos {n : ℕ} (hn : n ≠ 0) : 0 < dedekindPsi n := by
  have h := dedekindPsi_eq_prod (R := ℚ) hn
  have hpos : (0 : ℚ) < n * ∏ p ∈ n.primeFactors, (1 + (p : ℚ)⁻¹) :=
    mul_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn))
      (Finset.prod_pos fun p _ ↦ add_pos_of_pos_of_nonneg one_pos (inv_nonneg.2 p.cast_nonneg))
  exact_mod_cast h ▸ hpos

end ArithmeticFunction

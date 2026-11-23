/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk, OpenAI Codex
-/
module

public import TauCeti.NumberTheory.Divisors
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Finite Euler products over squarefree integers

These identities evaluate finite divisor sums over powers of squarefree integers.
The geometric estimates bound them by the corresponding Euler factors.

Adapted from Arend Mellendijk's PNT+ SelbergBounds.lean at revision
 e1ed50ef52b80922d0cf26293cdc74b84039b5d6, in
 https://github.com/TauCetiProject/PrimeNumberTheoremAnd.
-/

public section

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.zeta

namespace ArithmeticFunction

/-- The divisor sum of a multiplicative function over a power of a squarefree integer
factors into finite sums over the powers of its primes. -/
theorem IsMultiplicative.sum_divisors_pow_eq_prod_primeFactors
    {R : Type*} [CommSemiring R] {f : ArithmeticFunction R} (hf : f.IsMultiplicative)
    (d k : ℕ) (hd : Squarefree d) :
    ∑ m ∈ (d ^ k).divisors, f m =
      ∏ p ∈ d.primeFactors, ∑ i ∈ Finset.range (k + 1), f (p ^ i) := by
  have hmult : (f * (ζ : ArithmeticFunction R)).IsMultiplicative :=
    hf.mul isMultiplicative_zeta.natCast
  have hcop : (d.primeFactors : Set ℕ).Pairwise
      (fun p q ↦ (p ^ k).Coprime (q ^ k)) := by
    intro p hp q hq hpq
    exact Nat.Coprime.pow k k
      ((Nat.coprime_primes (prime_of_mem_primeFactors hp)
        (prime_of_mem_primeFactors hq)).mpr hpq)
  calc
    _ = (f * (ζ : ArithmeticFunction R)) (d ^ k) := coe_mul_zeta_apply.symm
    _ = (f * (ζ : ArithmeticFunction R)) (∏ p ∈ d.primeFactors, p ^ k) := by
      rw [Finset.prod_pow, Nat.prod_primeFactors_of_squarefree hd]
    _ = ∏ p ∈ d.primeFactors, (f * (ζ : ArithmeticFunction R)) (p ^ k) :=
      ArithmeticFunction.IsMultiplicative.map_prod _ hmult _ hcop
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow (prime_of_mem_primeFactors hp)]

end ArithmeticFunction

namespace MonoidHom

/-- A finite geometric product over the prime support of a squarefree integer. -/
theorem prod_sum_Icc_pow_eq_sum_divisors_pow_filter_dvd {R : Type*} [CommSemiring R]
    (F : ℕ →* R) (M d : ℕ) (hd : Squarefree d) :
    ∏ p ∈ d.primeFactors, ∑ j ∈ Icc 1 M, F (p ^ j) =
      ∑ m ∈ (d ^ M).divisors.filter (d ∣ ·), F m := by
  cases M with
  | zero =>
    by_cases hd1 : d = 1
    · simp [hd1]
    · have hne : d.primeFactors.Nonempty :=
        Nat.nonempty_primeFactors.mpr (by have := hd.ne_zero; omega)
      have hnot : ¬d ∣ 1 := by simpa only [Nat.dvd_one] using hd1
      simp only [pow_zero, Nat.divisors_one, Finset.filter_singleton]
      simp [hne.card_pos.ne', hnot]
  | succ k =>
      let f : ArithmeticFunction R := ⟨fun n ↦ if n = 0 then 0 else F n, by simp⟩
      have hf : f.IsMultiplicative := by
        refine ⟨by simp [f], ?_⟩
        intro m n _
        by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp [f, hm, hn, map_mul]
      have hsum (n : ℕ) : ∑ m ∈ n.divisors, f m = ∑ m ∈ n.divisors, F m := by
        apply Finset.sum_congr rfl
        intro m hm
        simp [f, (Nat.pos_of_mem_divisors hm).ne']
      have hpowers (p : ℕ) (hp : p ∈ d.primeFactors) :
          ∑ j ∈ Icc 1 (k + 1), F (p ^ j) =
            F p * ∑ j ∈ Finset.range (k + 1), f (p ^ j) := by
        rw [Finset.mul_sum]
        have hshift := Finset.sum_Ico_add' (fun j ↦ F (p ^ j)) 0 (k + 1) 1
        rw [zero_add, Ico_zero_eq_range, Ico_add_one_right_eq_Icc] at hshift
        rw [← hshift]
        apply Finset.sum_congr rfl
        intro j _
        simp [pow_succ, map_mul, f, (prime_of_mem_primeFactors hp).ne_zero, mul_comm]
      calc
        _ = (∏ p ∈ d.primeFactors, F p) *
            ∏ p ∈ d.primeFactors, ∑ j ∈ Finset.range (k + 1), f (p ^ j) := by
          rw [← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl hpowers
        _ = F d * ∑ m ∈ (d ^ k).divisors, F m := by
          rw [← map_prod F, Nat.prod_primeFactors_of_squarefree hd,
            ← hf.sum_divisors_pow_eq_prod_primeFactors d k hd, hsum]
        _ = _ := by
          rw [pow_succ, mul_comm (d ^ k) d,
            Nat.sum_divisors_filter_dvd (dvd_mul_right d (d ^ k)) F,
            Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd.ne_zero)]
          simp only [map_mul, Finset.mul_sum]

/-- A finite Euler product of geometric sums is bounded by the corresponding infinite factors. -/
theorem prod_sum_Icc_pow_le {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] (F : ℕ →* R) (M d : ℕ) (hd : Squarefree d)
    (hF : ∀ p ∈ d.primeFactors, 0 ≤ F p) (hFlt : ∀ p ∈ d.primeFactors, F p < 1) :
    ∏ p ∈ d.primeFactors, ∑ j ∈ Icc 1 M, F (p ^ j) ≤
      F d * ∏ p ∈ d.primeFactors, (1 - F p)⁻¹ := by
  calc
    _ = ∏ p ∈ d.primeFactors, ∑ j ∈ Ico 1 (M + 1), (F p) ^ j := by
      simp only [Ico_add_one_right_eq_Icc, map_pow]
    _ ≤ ∏ p ∈ d.primeFactors, F p / (1 - F p) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        exact Finset.sum_nonneg fun j _ ↦ pow_nonneg (hF p hp) j
      · intro p hp
        simpa only [pow_one] using
          (geom_sum_Ico_le_of_lt_one (m := 1) (n := M + 1) (hF p hp) (hFlt p hp))
    _ = _ := by
      simp only [div_eq_mul_inv]
      rw [Finset.prod_mul_distrib, ← map_prod F, Nat.prod_primeFactors_of_squarefree hd]

end MonoidHom

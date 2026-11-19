/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk, OpenAI Codex
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.NumberTheory.Primorial
public import Mathlib.NumberTheory.SelbergSieve
import TauCeti.Data.Nat.Interval

/-!
# The prime-interval sieve and its remainder

Sift the positive integers in the half-open interval `(x, x + y]` by primes at most `z`.
Their local density is `1 / d`. For `0 ≤ x` and `0 ≤ y`, the multiple count is a difference
of floors and the remainder has absolute value less than one, uniformly in the interval's
position and in every natural index. Primes lost by sifting are counted by `π(⌊z⌋₊)`.

These are the interval-counting inputs to the classical Selberg prime-interval upper bound.
The construction and prime comparison are adapted from
[Arend Mellendijk, PNT+, BrunTitchmarsh.lean]
(https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/7c7892801a0937aa6925e531a5e2c105bd20690b/PrimeNumberTheoremAnd/BrunTitchmarsh.lean).
-/

public noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

namespace BoundingSieve

/-- Sift the positive integers in `(x, x + y]` by primes at most `z`, with reciprocal densities. -/
def primeInterval (x y z : ℝ) : BoundingSieve where
  support := Ioc ⌊x⌋₊ ⌊x + y⌋₊
  prodPrimes := primorial ⌊z⌋₊
  prodPrimes_squarefree := squarefree_primorial _
  weights := fun _ ↦ 1
  weights_nonneg := fun _ ↦ zero_le_one
  totalMass := y
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := by
    intro p hp _
    simp [ite_eq_right hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := by
    intro p hp _
    simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply, hp.ne_zero, ↓reduceIte, Nat.cast_one,
      ArithmeticFunction.id_apply, one_div]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

/-- The interval sieve is supported on the natural numbers between its floored endpoints. -/
@[simp]
theorem primeInterval_support (x y z : ℝ) :
    (primeInterval x y z).support = Ioc ⌊x⌋₊ ⌊x + y⌋₊ := by
  rfl

/-- The interval sieve removes all primes at most its cutoff. -/
@[simp]
theorem primeInterval_prodPrimes (x y z : ℝ) :
    (primeInterval x y z).prodPrimes = primorial ⌊z⌋₊ := by
  rfl

/-- Every member of an interval sieve has unit weight. -/
@[simp]
theorem primeInterval_weights (x y z : ℝ) :
    (primeInterval x y z).weights = fun _ ↦ 1 := by
  rfl

/-- The main-term mass of an interval sieve is its interval length. -/
@[simp]
theorem primeInterval_totalMass (x y z : ℝ) :
    (primeInterval x y z).totalMass = y := by
  rfl

/-- The local density is the reciprocal of the natural index, including zero. -/
@[simp]
theorem primeInterval_nu_apply (x y z : ℝ) (d : ℕ) :
    (primeInterval x y z).nu d = (d : ℝ)⁻¹ := by
  by_cases hd : d = 0 <;> simp [primeInterval, hd]

/-- The multiple count for an interval sieve is an exact difference of integer quotients. -/
theorem multSum_primeInterval (x y z : ℝ) (d : ℕ) :
    (primeInterval x y z).multSum d = (⌊x + y⌋₊ / d - ⌊x⌋₊ / d : ℕ) := by
  simp only [multSum, primeInterval_support, primeInterval_weights, sum_boole, Nat.cast_inj]
  exact Nat.Ioc_filter_dvd_card _ _ _

/-- On intervals of nonnegative length, the remainder is a difference of floor errors. -/
theorem rem_primeInterval (x y z : ℝ) (hy : 0 ≤ y) (d : ℕ) :
    (primeInterval x y z).rem d =
      (⌊(x + y) / d⌋₊ : ℝ) - ⌊x / d⌋₊ - y / d := by
  rw [rem, multSum_primeInterval, primeInterval_nu_apply, primeInterval_totalMass, Nat.cast_sub
    (Nat.div_le_div_right (Nat.floor_mono (by linarith : x ≤ x + y)))]
  rw [Nat.floor_div_natCast, Nat.floor_div_natCast]
  simp [div_eq_mul_inv, mul_comm]

/-- The interval remainder is strictly less than one at every natural index. -/
theorem abs_rem_primeInterval_lt_one (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (d : ℕ) : |(primeInterval x y z).rem d| < 1 := by
  have hxy : 0 ≤ (x + y) / d := by positivity
  have hx' : 0 ≤ x / d := by positivity
  have h₁ := Nat.floor_le hxy
  have h₂ := Nat.lt_floor_add_one ((x + y) / d)
  have h₃ := Nat.floor_le hx'
  have h₄ := Nat.lt_floor_add_one (x / d)
  rw [rem_primeInterval x y z hy d, abs_lt]
  constructor <;> linarith [add_div x y (d : ℝ)]

/-- The sifted interval sum counts exactly the integers coprime to its prime product. -/
theorem siftedSum_primeInterval (x y z : ℝ) :
    (primeInterval x y z).siftedSum =
      (((Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter (Nat.Coprime (primorial ⌊z⌋₊))).card : ℝ) := by
  classical
  simp only [siftedSum, primeInterval_support, primeInterval_prodPrimes, primeInterval_weights]
  exact (natCast_card_filter _ _).symm

/-- A prime in the interval either survives sifting or is at most the sieving cutoff. -/
theorem filter_prime_subset_primeInterval_union (x y z : ℝ) :
    (Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter Nat.Prime ⊆
      (Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter (Nat.Coprime (primorial ⌊z⌋₊)) ∪
        Nat.primesLE ⌊z⌋₊ := by
  intro p hp
  obtain ⟨hpI, hp⟩ := mem_filter.mp hp
  by_cases hpz : p ≤ ⌊z⌋₊
  · exact mem_union_right _ (Nat.mem_primesLE.mpr ⟨hpz, hp⟩)
  · refine mem_union_left _ (mem_filter.mpr ⟨hpI, ?_⟩)
    apply Nat.Coprime.symm
    rw [hp.coprime_iff_not_dvd]
    exact fun h ↦ hpz (hp.dvd_primorial_iff.mp h)

/-- Every prime in `(x, x + y]` survives the sieve except for primes at most `z`. -/
theorem card_primes_primeInterval_le (x y z : ℝ) :
    (((Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter Nat.Prime).card : ℝ) ≤
      (primeInterval x y z).siftedSum + Nat.primeCounting ⌊z⌋₊ := by
  rw [siftedSum_primeInterval, ← Nat.primesLE_card_eq_primeCounting]
  exact_mod_cast (card_le_card (filter_prime_subset_primeInterval_union x y z)).trans
    (card_union_le _ _)

/-- The canonical prime-counting difference is bounded by the sifted interval and the
number of primes at most the sieving cutoff. -/
theorem primeCounting_sub_le_primeInterval (x y z : ℝ) :
    ((Nat.primeCounting ⌊x + y⌋₊ - Nat.primeCounting ⌊x⌋₊ : ℕ) : ℝ) ≤
      (primeInterval x y z).siftedSum + Nat.primeCounting ⌊z⌋₊ := by
  by_cases hfloor : ⌊x⌋₊ ≤ ⌊x + y⌋₊
  swap
  · rw [Nat.sub_eq_zero_of_le (Nat.monotone_primeCounting (not_le.mp hfloor).le),
      Nat.cast_zero, siftedSum_primeInterval]
    positivity
  have heq : (Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter Nat.Prime =
      Nat.primesLE ⌊x + y⌋₊ \ Nat.primesLE ⌊x⌋₊ := by
    ext p
    simp only [mem_filter, mem_Ioc, mem_sdiff, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨ha, hb⟩, hp⟩
      exact ⟨⟨hb, hp⟩, fun h ↦ (not_le.mpr ha) h.1⟩
    · rintro ⟨⟨hb, hp⟩, ha⟩
      exact ⟨⟨lt_of_not_ge fun h ↦ ha ⟨h, hp⟩, hb⟩, hp⟩
  have hcard := card_primes_primeInterval_le x y z
  rwa [heq, card_sdiff_of_subset (Nat.primesLE_mono hfloor),
    Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting] at hcard

end BoundingSieve

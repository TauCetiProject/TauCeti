/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.PSeries
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.NumberTheory.ArithmeticFunction.Moebius
import TauCeti.NumberTheory.Chebyshev.Mertens
import TauCeti.NumberTheory.Mertens.Basic

/-!
# Euler-product lower bounds for squarefree logarithmic sums

Let `f` be a real multiplicative function whose prime values lie in `[0, k]`. This file proves
that the squarefree logarithmic sum `∑_{n ≤ z} μ(n)² f(n) / n` is bounded below by a constant
multiple of its Euler product `∏_{p ≤ z} (1 + f(p) / p)`, with a constant depending only on `k`,
uniformly in `f` and in `z ≥ 1`.

The proof uses Rankin's trick. Expanding `∏_{p ≤ y} (1 + f(p) / p)` over the subsets of the primes
up to `y` writes it as the sum of `f(n) / n` over squarefree `n` with prime factors at most `y`.
The terms with `n > z` are at most `z^{-σ}` times the product with `f(p)` replaced by `f(p) p^σ`
(`TauCeti.sum_powerset_filter_lt_prod_le_exp_mul_prod`). With `σ = 1 / log y` and
`y = z^{1/B}`, Mertens's first theorem shows that this tail is at most half of the product once
`B` is large in terms of `k`. Mertens's second theorem bounds the primes in `(y, z]`.

The form needed for Selberg's sieve with several excluded residue classes compares the sum with
the reciprocal local densities instead: if `0 ≤ g(p) ≤ d`, then
`∑_{n ≤ z} μ(n)² g(n) / n ≥ c_d ∏_{d < p ≤ z} (1 - g(p) / p)⁻¹`
(`TauCeti.exists_pos_mul_prod_one_sub_div_inv_le_sum_moebius_sq_mul_div`). With `g(p) ≤ 2` (the
local densities of the twin-prime and Goldbach sieves) this is their denominator estimate.

## Main results

* `TauCeti.sum_powerset_filter_lt_prod_le_exp_mul_prod`: Rankin's bound for the subsets of a
  finite set of naturals whose product exceeds `z`.
* `TauCeti.exists_pos_mul_prod_one_add_div_le_sum_moebius_sq_mul_div`: for every `k` there is
  `c > 0` with `c ∏_{p ≤ z} (1 + f(p) / p) ≤ ∑_{n ≤ z} μ(n)² f(n) / n` for every multiplicative `f`
  with prime values in `[0, k]` and every `z ≥ 1`.
* `TauCeti.exists_pos_mul_prod_one_sub_div_inv_le_sum_moebius_sq_mul_div`: the same lower bound
  against `∏_{d < p ≤ z} (1 - g(p) / p)⁻¹` for prime values in `[0, d]`.

## References

* A. Khayutin, *Joint equidistribution of CM points*, Ann. of Math. 189 (2019), Lemma 9.8.
* R. A. Rankin, *The difference between consecutive prime numbers*, J. London Math. Soc. 13
  (1938), 242–247.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter III.5.
-/

public section

open Finset
open scoped ArithmeticFunction.Moebius

namespace TauCeti

/-- **Rankin's trick.** For a finite set `S` of naturals, nonnegative weights `a`, `z ≥ 0` and
`σ ≥ 0`, the sum of `∏_{p ∈ T} a p` over the subsets `T ⊆ S` whose product exceeds `z` is at most
`z^{-σ} ∏_{p ∈ S} (1 + a p p^σ)`, with the powers written through `exp` and `log`. -/
theorem sum_powerset_filter_lt_prod_le_exp_mul_prod (S : Finset ℕ) {a : ℕ → ℝ}
    (ha : ∀ p ∈ S, 0 ≤ a p) {z σ : ℝ} (hz : 0 ≤ z) (hσ : 0 ≤ σ) :
    ∑ T ∈ S.powerset with z < ((∏ p ∈ T, p : ℕ) : ℝ), ∏ p ∈ T, a p ≤
      Real.exp (-(σ * Real.log z)) * ∏ p ∈ S, (1 + a p * Real.exp (σ * Real.log p)) := by
  rw [prod_one_add, mul_sum]
  refine (sum_le_sum fun T hT ↦ ?_).trans
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun T hT _ ↦ ?_)
  · obtain ⟨hTS, hzT⟩ := mem_filter.1 hT
    have hT0 : ∀ p ∈ T, (p : ℝ) ≠ 0 := fun p hp h0 ↦ by
      have : ∏ q ∈ T, q = 0 := prod_eq_zero hp (by exact_mod_cast h0)
      rw [this, Nat.cast_zero] at hzT
      exact hz.not_gt hzT
    have hlog : Real.log z ≤ ∑ p ∈ T, Real.log p := by
      rw [← Real.log_prod hT0, ← Nat.cast_prod]
      rcases hz.eq_or_lt with rfl | hz
      · exact Real.log_zero.trans_le (Real.log_natCast_nonneg _)
      · exact Real.log_le_log hz hzT.le
    have hone : 1 ≤ Real.exp (-(σ * Real.log z)) * Real.exp (σ * ∑ p ∈ T, Real.log p) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      nlinarith
    rw [prod_mul_distrib, ← Real.exp_sum, ← mul_sum, mul_left_comm]
    exact le_mul_of_one_le_right (prod_nonneg fun p hp ↦ ha p (mem_powerset.1 hTS hp)) hone
  · exact mul_nonneg (Real.exp_pos _).le
      (prod_nonneg fun p hp ↦ mul_nonneg (ha p (mem_powerset.1 hT hp)) (Real.exp_pos _).le)

/-- The subsets of a finite set of primes whose product is at most `z` contribute at most the
squarefree logarithmic sum `∑_{n ≤ z} μ(n)² f(n) / n`. -/
private theorem sum_powerset_filter_le_sum_moebius_sq_mul_div {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (hf0 : ∀ p : ℕ, p.Prime → 0 ≤ f p) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (z : ℝ) :
    ∑ T ∈ S.powerset with ((∏ p ∈ T, p : ℕ) : ℝ) ≤ z, ∏ p ∈ T, f p / p ≤
      ∑ n ∈ Ioc 0 ⌊z⌋₊, (μ n : ℝ) ^ 2 * f n / n := by
  have hprime : ∀ T ∈ S.powerset, ∀ p ∈ T, p.Prime := fun T hT p hp ↦
    hS p (mem_powerset.1 hT hp)
  have hinj : Set.InjOn (fun T : Finset ℕ ↦ ∏ p ∈ T, p)
      (S.powerset.filter fun T ↦ ((∏ p ∈ T, p : ℕ) : ℝ) ≤ z) := fun T hT U hU hTU ↦ by
    rw [← Nat.primeFactors_prod (hprime T (mem_filter.1 hT).1),
      ← Nat.primeFactors_prod (hprime U (mem_filter.1 hU).1)]
    exact congrArg Nat.primeFactors hTU
  have hterm : ∀ T ∈ S.powerset.filter (fun T ↦ ((∏ p ∈ T, p : ℕ) : ℝ) ≤ z),
      ∏ p ∈ T, f p / p = (μ (∏ p ∈ T, p) : ℝ) ^ 2 * f (∏ p ∈ T, p) / ((∏ p ∈ T, p : ℕ) : ℝ) := by
    intro T hT
    have hTp := hprime T (mem_filter.1 hT).1
    have hμ : (μ (∏ p ∈ T, p) : ℝ) ^ 2 = 1 := by
      rw [ArithmeticFunction.IsMultiplicative.map_prod_of_prime
        ArithmeticFunction.isMultiplicative_moebius T hTp, Int.cast_prod, ← prod_pow]
      exact prod_eq_one fun p hp ↦ by simp [ArithmeticFunction.moebius_apply_prime (hTp p hp)]
    rw [hμ, one_mul, hf.map_prod_of_prime T hTp, Nat.cast_prod, prod_div_distrib]
  rw [sum_congr rfl hterm, ← sum_image (f := fun n ↦ (μ n : ℝ) ^ 2 * f n / n) hinj]
  refine sum_le_sum_of_subset_of_nonneg (fun n hn ↦ ?_) fun n _ _ ↦
    div_nonneg (hf.moebius_sq_mul_nonneg hf0 n) n.cast_nonneg
  obtain ⟨T, hT, rfl⟩ := mem_image.1 hn
  obtain ⟨hTS, hTz⟩ := mem_filter.1 hT
  exact mem_Ioc.2 ⟨prod_pos fun p hp ↦ (hprime T hTS p hp).pos,
    Nat.le_floor hTz⟩

/-- With `σ = 1 / log y` for `y ≥ 2`, the perturbation `∑_{p ≤ y} (f(p) / p) (p^σ - 1)` caused by
the Rankin weight is at most `k e (1 + (log 4 + 4) / log 2)` when `f(p) ≤ k`, by Mertens's first
theorem. -/
private theorem sum_primesLE_div_mul_exp_sub_one_le {f : ℕ → ℝ} {k : ℝ}
    (hk : 0 ≤ k) (hfk : ∀ p : ℕ, p.Prime → f p ≤ k) {y : ℝ} (hy : 2 ≤ y) :
    ∑ p ∈ Nat.primesLE ⌊y⌋₊, f p / p * (Real.exp ((Real.log y)⁻¹ * Real.log p) - 1) ≤
      k * Real.exp 1 * (1 + (Real.log 4 + 4) / Real.log 2) := by
  have hlogy : 0 < Real.log y := Real.log_pos (one_lt_two.trans_le hy)
  set σ := (Real.log y)⁻¹
  -- Each exponent `σ log p` lies in `[0, 1]`, so `p^σ - 1 ≤ e σ log p`.
  have hexp : ∀ p ∈ Nat.primesLE ⌊y⌋₊, f p / p * (Real.exp (σ * Real.log p) - 1) ≤
      k * Real.exp 1 * σ * (Real.log p / p) := fun p hp ↦ by
    obtain ⟨hpy, hpr⟩ := Nat.mem_primesLE.1 hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpr.pos
    have hu0 : 0 ≤ σ * Real.log p :=
      mul_nonneg (inv_nonneg.2 hlogy.le) (Real.log_nonneg (by exact_mod_cast hpr.one_le))
    have hu1 : σ * Real.log p ≤ 1 := by
      rw [inv_mul_le_iff₀ hlogy, mul_one]
      exact Real.log_le_log hp0 ((Nat.le_floor_iff (by linarith)).1 hpy)
    have h1 : Real.exp (σ * Real.log p) - 1 ≤ σ * Real.log p * Real.exp 1 := by
      have := abs_exp_sub_one_le_mul_exp_abs (σ * Real.log p)
      rw [abs_of_nonneg (sub_nonneg.2 (Real.one_le_exp hu0)), abs_of_nonneg hu0] at this
      exact this.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hu1) hu0)
    calc f p / p * (Real.exp (σ * Real.log p) - 1) ≤ k / p * (σ * Real.log p * Real.exp 1) :=
          mul_le_mul (div_le_div_of_nonneg_right (hfk p hpr) hp0.le) h1
            (sub_nonneg.2 (Real.one_le_exp hu0)) (div_nonneg hk hp0.le)
      _ = k * Real.exp 1 * σ * (Real.log p / p) := by ring
  refine (sum_le_sum hexp).trans ?_
  rw [← mul_sum]
  have hmertens := Chebyshev.sum_primesLE_log_div_le (one_le_two.trans hy)
  have hfrac : σ * (Real.log y + (Real.log 4 + 4)) ≤ 1 + (Real.log 4 + 4) / Real.log 2 := by
    rw [mul_add, inv_mul_cancel₀ hlogy.ne', inv_mul_eq_div]
    gcongr
  calc k * Real.exp 1 * σ * ∑ p ∈ Nat.primesLE ⌊y⌋₊, Real.log p / p
      ≤ k * Real.exp 1 * (σ * (Real.log y + (Real.log 4 + 4))) := by
        rw [mul_assoc (k * Real.exp 1)]
        gcongr
    _ ≤ k * Real.exp 1 * (1 + (Real.log 4 + 4) / Real.log 2) :=
        mul_le_mul_of_nonneg_left hfrac (by positivity)

/-- The tail half of Rankin's argument: if `f` has prime values in `[0, k]` with `k ≥ 0`, then
for `y ≥ 2` and `z = y^B` with `B = k e (1 + (log 4 + 4) / log 2) + 1`, the subsets of the
primes up to `y` with product exceeding `z` carry at most half of `∏_{p ≤ y} (1 + f(p) / p)`. -/
private theorem sum_powerset_filter_lt_le_half_mul_prod {f : ArithmeticFunction ℝ} {k : ℝ}
    (hk : 0 ≤ k) (hf0 : ∀ p : ℕ, p.Prime → 0 ≤ f p) (hfk : ∀ p : ℕ, p.Prime → f p ≤ k)
    {y z : ℝ} (hy : 2 ≤ y) (hz : 0 < z)
    (hyz : Real.log z = (k * Real.exp 1 * (1 + (Real.log 4 + 4) / Real.log 2) + 1) *
      Real.log y) :
    ∑ T ∈ (Nat.primesLE ⌊y⌋₊).powerset with z < ((∏ p ∈ T, p : ℕ) : ℝ), ∏ p ∈ T, f p / p ≤
      2⁻¹ * ∏ p ∈ Nat.primesLE ⌊y⌋₊, (1 + f p / p) := by
  set S := Nat.primesLE ⌊y⌋₊
  set M := k * Real.exp 1 * (1 + (Real.log 4 + 4) / Real.log 2)
  have hlogy : 0 < Real.log y := Real.log_pos (one_lt_two.trans_le hy)
  have ha : ∀ p ∈ S, 0 ≤ f p / p := fun p hp ↦ div_nonneg (hf0 p (Nat.mem_primesLE.1 hp).2)
    (Nat.cast_nonneg p)
  have hP : 0 ≤ ∏ p ∈ S, (1 + f p / p) := prod_nonneg fun p hp ↦ by
    have := ha p hp
    positivity
  set σ := (Real.log y)⁻¹
  have hσz : σ * Real.log z = M + 1 := by
    simp only [σ, hyz]
    field_simp
  calc _ ≤ Real.exp (-(σ * Real.log z)) * ∏ p ∈ S, (1 + f p / p * Real.exp (σ * Real.log p)) :=
        sum_powerset_filter_lt_prod_le_exp_mul_prod S ha hz.le (inv_nonneg.2 hlogy.le)
    _ ≤ Real.exp (-(M + 1)) * ((∏ p ∈ S, (1 + f p / p)) *
          Real.exp (∑ p ∈ S, f p / p * (Real.exp (σ * Real.log p) - 1))) := by
        rw [hσz, Real.exp_sum, ← prod_mul_distrib]
        gcongr with p hp
        · exact fun p hp ↦ by have := ha p hp; positivity
        · exact one_add_mul_le_one_add_mul_exp_mul_sub_one (ha p hp) (Real.one_le_exp
            (mul_nonneg (inv_nonneg.2 hlogy.le)
              (Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.1 hp).2.one_le))))
    _ ≤ Real.exp (-(M + 1)) * ((∏ p ∈ S, (1 + f p / p)) * Real.exp M) := by
        gcongr
        exact sum_primesLE_div_mul_exp_sub_one_le hk hfk hy
    _ = Real.exp (-1) * ∏ p ∈ S, (1 + f p / p) := by
        rw [mul_left_comm, ← Real.exp_add, show -(M + 1) + M = -1 by ring, mul_comm]
    _ ≤ 2⁻¹ * ∏ p ∈ S, (1 + f p / p) := by
        gcongr
        rw [Real.exp_neg]
        exact inv_anti₀ two_pos (by linarith [Real.add_one_le_exp (1 : ℝ)])

/-- The head half of Rankin's argument: with `B` as in `sum_powerset_filter_lt_le_half_mul_prod`
and `y = z^{1/B}`, the squarefree sum up to `z` is at least half of
`∏_{p ≤ y} (1 + f(p) / p)`. -/
private theorem half_mul_prod_le_sum_moebius_sq_mul_div {f : ArithmeticFunction ℝ} {k : ℝ}
    (hk : 0 ≤ k) (hf : f.IsMultiplicative) (hf0 : ∀ p : ℕ, p.Prime → 0 ≤ f p)
    (hfk : ∀ p : ℕ, p.Prime → f p ≤ k) {z : ℝ} (hz : 1 ≤ z) :
    2⁻¹ * ∏ p ∈ Nat.primesLE ⌊Real.exp (Real.log z /
        (k * Real.exp 1 * (1 + (Real.log 4 + 4) / Real.log 2) + 1))⌋₊, (1 + f p / p) ≤
      ∑ n ∈ Ioc 0 ⌊z⌋₊, (μ n : ℝ) ^ 2 * f n / n := by
  set B := k * Real.exp 1 * (1 + (Real.log 4 + 4) / Real.log 2) + 1
  set y := Real.exp (Real.log z / B)
  have hB : 0 < B := by positivity
  have hS : ∀ p ∈ Nat.primesLE ⌊y⌋₊, p.Prime := fun p hp ↦ (Nat.mem_primesLE.1 hp).2
  rcases le_or_gt 2 y with hy | hy
  · have hlogz : Real.log z = B * Real.log y := by
      rw [Real.log_exp, mul_div_cancel₀ _ hB.ne']
    have hsplit := sum_filter_add_sum_filter_not (Nat.primesLE ⌊y⌋₊).powerset
      (fun T ↦ ((∏ p ∈ T, p : ℕ) : ℝ) ≤ z) fun T ↦ ∏ p ∈ T, f p / p
    simp_rw [not_le] at hsplit
    rw [← prod_one_add] at hsplit
    have htail := sum_powerset_filter_lt_le_half_mul_prod hk hf0 hfk hy
      (zero_lt_one.trans_le hz) hlogz
    have hhead := sum_powerset_filter_le_sum_moebius_sq_mul_div hf hf0 hS z
    linarith
  · have hempty : ∏ p ∈ Nat.primesLE ⌊y⌋₊, (1 + f p / p) = 1 := prod_eq_one fun p hp ↦ by
      have h2 := (hS p hp).two_le
      have h3 : p < 2 := (Nat.mem_primesLE.1 hp).1.trans_lt
        ((Nat.floor_lt (Real.exp_pos _).le).2 (by exact_mod_cast hy))
      omega
    have h1 : (1 : ℝ) ≤ ∑ n ∈ Ioc 0 ⌊z⌋₊, (μ n : ℝ) ^ 2 * f n / n := by
      have := single_le_sum (fun n _ ↦ div_nonneg (hf.moebius_sq_mul_nonneg hf0 n) n.cast_nonneg)
        (mem_Ioc.2 ⟨zero_lt_one, Nat.le_floor (by exact_mod_cast hz)⟩ : 1 ∈ Ioc 0 ⌊z⌋₊)
      simpa [hf.map_one] using this
    rw [hempty]
    linarith

/-- The primes in `(y, z]` change the Euler product by at most the factor
`exp (k ∑_{y < p ≤ z} 1 / p)`. -/
private theorem prod_primesLE_one_add_div_le {f : ArithmeticFunction ℝ} {k : ℝ}
    (hf0 : ∀ p : ℕ, p.Prime → 0 ≤ f p) (hfk : ∀ p : ℕ, p.Prime → f p ≤ k) {y z : ℝ}
    (hyz : y ≤ z) :
    ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 + f p / p) ≤ (∏ p ∈ Nat.primesLE ⌊y⌋₊, (1 + f p / p)) *
      Real.exp (k * ∑ p ∈ Nat.primesLE ⌊z⌋₊ \ Nat.primesLE ⌊y⌋₊, (p : ℝ)⁻¹) := by
  have hpos : ∀ p ∈ Nat.primesLE ⌊z⌋₊, 0 ≤ 1 + f p / p := fun p hp ↦ by
    have := hf0 p (Nat.mem_primesLE.1 hp).2
    positivity
  rw [← prod_sdiff (Nat.primesLE_mono (Nat.floor_mono hyz)), mul_comm, mul_sum, Real.exp_sum]
  refine mul_le_mul_of_nonneg_left (prod_le_prod₀ (fun p hp ↦ hpos p (mem_sdiff.1 hp).1)
    fun p hp ↦ ?_) (prod_nonneg fun p hp ↦ hpos p (Nat.primesLE_mono (Nat.floor_mono hyz) hp))
  have hp := (Nat.mem_primesLE.1 (mem_sdiff.1 hp).1).2
  rw [add_comm, ← div_eq_mul_inv]
  exact (Real.add_one_le_exp _).trans (Real.exp_le_exp.2
    (div_le_div_of_nonneg_right (hfk p hp) (by exact_mod_cast hp.pos.le)))

/-- **Euler-product lower bound for squarefree logarithmic sums.** For every real `k` there is
`c > 0` such that for every multiplicative `f` with `0 ≤ f p ≤ k` at all primes `p` and every real
`z ≥ 1`, `c ∏_{p ≤ z} (1 + f(p) / p) ≤ ∑_{n ≤ z} μ(n)² f(n) / n`. -/
theorem exists_pos_mul_prod_one_add_div_le_sum_moebius_sq_mul_div (k : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : ArithmeticFunction ℝ, f.IsMultiplicative →
      (∀ p : ℕ, p.Prime → 0 ≤ f p) → (∀ p : ℕ, p.Prime → f p ≤ k) → ∀ z : ℝ, 1 ≤ z →
        c * ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 + f p / p) ≤
          ∑ n ∈ Ioc 0 ⌊z⌋₊, (μ n : ℝ) ^ 2 * f n / n := by
  set k' := max k 0
  set B := k' * Real.exp 1 * (1 + (Real.log 4 + 4) / Real.log 2) + 1
  have hk' : 0 ≤ k' := le_max_right _ _
  have hB : 1 ≤ B := by
    have : 0 ≤ k' * Real.exp 1 * (1 + (Real.log 4 + 4) / Real.log 2) := by positivity
    linarith
  obtain ⟨K, hK⟩ := exists_sum_sdiff_primesLE_inv_le (zero_lt_one.trans_le hB)
  refine ⟨2⁻¹ * (Real.exp (k' * K))⁻¹, by positivity, fun f hf hf0 hfk z hz ↦ ?_⟩
  have hfk' : ∀ p : ℕ, p.Prime → f p ≤ k' := fun p hp ↦ (hfk p hp).trans (le_max_left _ _)
  have hyz : Real.exp (Real.log z / B) ≤ z :=
    (Real.exp_le_exp.2 (div_le_self (Real.log_nonneg hz) hB)).trans_eq
      (Real.exp_log (zero_lt_one.trans_le hz))
  calc 2⁻¹ * (Real.exp (k' * K))⁻¹ * ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 + f p / p)
      ≤ 2⁻¹ * (Real.exp (k' * K))⁻¹ *
          ((∏ p ∈ Nat.primesLE ⌊Real.exp (Real.log z / B)⌋₊, (1 + f p / p)) *
            Real.exp (k' * K)) := by
        refine mul_le_mul_of_nonneg_left ((prod_primesLE_one_add_div_le hf0 hfk' hyz).trans ?_)
          (by positivity)
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
          (mul_le_mul_of_nonneg_left (hK z hz) hk')) (prod_nonneg fun p hp ↦ ?_)
        have := hf0 p (Nat.mem_primesLE.1 hp).2
        positivity
    _ = 2⁻¹ * ∏ p ∈ Nat.primesLE ⌊Real.exp (Real.log z / B)⌋₊, (1 + f p / p) := by
        field_simp
    _ ≤ ∑ n ∈ Ioc 0 ⌊z⌋₊, (μ n : ℝ) ^ 2 * f n / n :=
        half_mul_prod_le_sum_moebius_sq_mul_div hk' hf hf0 hfk' hz

/-- The quadratic local corrections `(d / n)² / (1 - (d / n)²)` over `n > d` form a summable
sequence. -/
private theorem summable_ite_div_sq_div_one_sub (d : ℝ) :
    Summable fun n : ℕ ↦ if d < n then (d / n) ^ 2 / (1 - (d / n) ^ 2) else 0 := by
  refine Summable.of_norm_bounded_eventually_nat
    ((Real.summable_nat_pow_inv.2 one_lt_two).mul_left (2 * d ^ 2)) ?_
  filter_upwards [Filter.eventually_ge_atTop (⌈2 * |d|⌉₊ + 1)] with n hn
  have hn' : 2 * |d| + 1 ≤ n := by
    have := Nat.le_ceil (2 * |d|)
    have : ((⌈2 * |d|⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at this
    linarith
  have hn0 : (0 : ℝ) < n := by linarith [abs_nonneg d]
  have hdn : d < n := by linarith [le_abs_self d, abs_nonneg d]
  have ht : (d / n) ^ 2 ≤ 1 / 4 := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    nlinarith [sq_abs d, abs_nonneg d]
  simp only [hdn, ↓reduceIte]
  rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (by linarith)),
    div_le_iff₀ (by linarith)]
  have : 2 * d ^ 2 * ((n : ℝ) ^ 2)⁻¹ = 2 * (d / n) ^ 2 := by rw [div_pow]; ring
  rw [this]
  nlinarith [sq_nonneg (d / n)]

/-- Removing the quadratic local corrections: if `0 ≤ g p ≤ d` on a finite set `s` of primes,
then `∏_{p ∈ s, d < p} (1 - g(p) / p)⁻¹` is at most `∏_{p ∈ s} (1 + g(p) / p)` times a constant
depending only on `d`. -/
private theorem prod_filter_inv_one_sub_div_le {g : ArithmeticFunction ℝ} {d : ℝ} (hd : 0 ≤ d)
    (hg0 : ∀ p : ℕ, p.Prime → 0 ≤ g p) (hgd : ∀ p : ℕ, p.Prime → g p ≤ d) {s : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s with d < ((p : ℕ) : ℝ), (1 - g p / p)⁻¹ ≤ (∏ p ∈ s, (1 + g p / p)) *
      Real.exp (∑' n : ℕ, if d < n then (d / n) ^ 2 / (1 - (d / n) ^ 2) else 0) := by
  set φ : ℕ → ℝ := fun n ↦ if d < n then (d / n) ^ 2 / (1 - (d / n) ^ 2) else 0
  have hφ0 : ∀ n, 0 ≤ φ n := fun n ↦ by
    simp only [φ]
    split_ifs with hdn
    · have hn : (0 : ℝ) < n := hd.trans_lt hdn
      have : d / n < 1 := (div_lt_one hn).2 hdn
      have : (d / n) ^ 2 < 1 := by nlinarith [div_nonneg hd hn.le]
      exact div_nonneg (sq_nonneg _) (by linarith)
    · exact le_rfl
  have hx : ∀ p ∈ s, 0 ≤ g p / p := fun p hp ↦ div_nonneg (hg0 p (hs p hp)) (Nat.cast_nonneg p)
  calc ∏ p ∈ s with d < ((p : ℕ) : ℝ), (1 - g p / p)⁻¹
      ≤ ∏ p ∈ s with d < ((p : ℕ) : ℝ), ((1 + g p / p) * Real.exp (φ p)) := by
        refine prod_le_prod₀ (fun p hp ↦ ?_) fun p hp ↦ ?_ <;>
          obtain ⟨hp, hdp⟩ := mem_filter.1 hp <;>
          have hp0 : (0 : ℝ) < p := hd.trans_lt hdp
        · exact inv_nonneg.2 (sub_nonneg.2 ((div_le_one hp0).2 ((hgd p (hs p hp)).trans hdp.le)))
        · simp only [φ, hdp, ↓reduceIte]
          exact inv_one_sub_le_one_add_mul_exp_sq_div_one_sub_sq (hx p hp)
            (div_le_div_of_nonneg_right (hgd p (hs p hp)) hp0.le) ((div_lt_one hp0).2 hdp)
    _ = (∏ p ∈ s with d < ((p : ℕ) : ℝ), (1 + g p / p)) *
          Real.exp (∑ p ∈ s with d < ((p : ℕ) : ℝ), φ p) := by
        rw [prod_mul_distrib, Real.exp_sum]
    _ ≤ (∏ p ∈ s, (1 + g p / p)) * Real.exp (∑' n, φ n) := by
        refine mul_le_mul (prod_le_prod_of_subset_of_one_le₀ (filter_subset _ _)
          (fun p hp ↦ by have := hx p (mem_filter.1 hp).1; positivity)
          fun p hp _ ↦ by have := hx p hp; linarith)
          (Real.exp_le_exp.2 ((summable_ite_div_sq_div_one_sub d).sum_le_tsum _
            fun n _ ↦ hφ0 n)) (Real.exp_pos _).le
          (prod_nonneg fun p hp ↦ by have := hx p hp; positivity)

/-- **Euler denominator of the binary sieve.** For every real `d` there is `c > 0` such that for
every multiplicative `g` with `0 ≤ g p ≤ d` at all primes `p` and every real `z ≥ 1`,
`c ∏_{d < p ≤ z} (1 - g(p) / p)⁻¹ ≤ ∑_{n ≤ z} μ(n)² g(n) / n`. -/
theorem exists_pos_mul_prod_one_sub_div_inv_le_sum_moebius_sq_mul_div (d : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ g : ArithmeticFunction ℝ, g.IsMultiplicative →
      (∀ p : ℕ, p.Prime → 0 ≤ g p) → (∀ p : ℕ, p.Prime → g p ≤ d) → ∀ z : ℝ, 1 ≤ z →
        c * ∏ p ∈ Nat.primesLE ⌊z⌋₊ with d < ((p : ℕ) : ℝ), (1 - g p / p)⁻¹ ≤
          ∑ n ∈ Ioc 0 ⌊z⌋₊, (μ n : ℝ) ^ 2 * g n / n := by
  obtain ⟨c, hc, hA⟩ := exists_pos_mul_prod_one_add_div_le_sum_moebius_sq_mul_div d
  set E := Real.exp (∑' n : ℕ, if d < n then (d / n) ^ 2 / (1 - (d / n) ^ 2) else 0)
  have hE : 0 < E := Real.exp_pos _
  refine ⟨c * E⁻¹, by positivity, fun g hg hg0 hgd z hz ↦ ?_⟩
  have hd : 0 ≤ d := (hg0 2 Nat.prime_two).trans (hgd 2 Nat.prime_two)
  calc c * E⁻¹ * ∏ p ∈ Nat.primesLE ⌊z⌋₊ with d < ((p : ℕ) : ℝ), (1 - g p / p)⁻¹
      ≤ c * E⁻¹ * ((∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 + g p / p)) * E) := by
        gcongr
        exact prod_filter_inv_one_sub_div_le hd hg0 hgd fun p hp ↦ (Nat.mem_primesLE.1 hp).2
    _ = c * ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 + g p / p) := by
        field_simp
    _ ≤ ∑ n ∈ Ioc 0 ⌊z⌋₊, (μ n : ℝ) ^ 2 * g n / n := hA g hg hg0 hgd z hz

end TauCeti

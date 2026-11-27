/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.SmoothNumbers
public import TauCeti.NumberTheory.Padics.PadicValRat

/-!
# `S`-factored numbers and `p`-adic valuations

Mathlib's `Nat.factoredNumbers S` is the set of positive integers all of whose prime factors lie
in the finite set `S`. This file describes these numbers through `p`-adic valuations:

* `TauCeti.forall_padicValRat_eq_zero_iff_mem_factoredNumbers`: a nonzero rational number has
  `p`-adic valuation zero at every prime `p ∉ S` exactly when its numerator (in absolute value)
  and its denominator are `S`-factored;
* `TauCeti.prod_pow_padicValNat_eq_self_of_mem_factoredNumbers`: if `S` consists of primes, an
  `S`-factored number is the product of the powers `p ^ v_p(n)` over `p ∈ S`;
* `TauCeti.hasSum_rpow_neg_factoredNumbers`: for every real `σ > 0`, the powers `n ^ (-σ)` of the
  `S`-factored numbers sum to the finite Euler product `∏_{p ∈ S prime} (1 - p ^ (-σ))⁻¹`, with
  the reciprocal case `TauCeti.hasSum_inv_factoredNumbers` and the version
  `TauCeti.hasSum_rpow_neg_smoothNumbers` for the `N`-smooth numbers.

The valuation results are the arithmetic inputs for describing the rational `S`-units. The
reciprocal sum bounds harmonic sums over integers whose prime factors are restricted, as in the
denominators of Selberg's sieve. The sum of `n ^ (-σ)` over the smooth numbers needs only
`σ > 0`, not `σ > 1`, because only finitely many primes occur; it is the series behind Rankin's
upper bound for the number of smooth integers.
-/

public section

namespace TauCeti

/-- A nonzero rational number has `p`-adic valuation zero at every prime `p ∉ S` exactly when the
absolute value of its numerator and its denominator are `S`-factored. -/
theorem forall_padicValRat_eq_zero_iff_mem_factoredNumbers {S : Finset ℕ} {q : ℚ} (hq : q ≠ 0) :
    (∀ p : ℕ, p.Prime → p ∉ S → padicValRat p q = 0) ↔
      q.num.natAbs ∈ Nat.factoredNumbers S ∧ q.den ∈ Nat.factoredNumbers S := by
  have hn : q.num.natAbs ≠ 0 := by simpa using hq
  simp only [Nat.mem_factoredNumbers_iff_primeFactors_subset, Finset.subset_iff,
    Nat.mem_primeFactors]
  refine ⟨fun h ↦ ⟨⟨hn, fun p ⟨hp, hpq, _⟩ ↦ ?_⟩, ⟨q.den_ne_zero, fun p ⟨hp, hpq, _⟩ ↦ ?_⟩⟩,
    fun ⟨⟨_, hnum⟩, ⟨_, hden⟩⟩ p hp hpS ↦ ?_⟩
  · have : Fact p.Prime := ⟨hp⟩
    by_contra hpS
    exact ((padicValRat.eq_zero_iff hq).1 (h p hp hpS)).1 hpq
  · have : Fact p.Prime := ⟨hp⟩
    by_contra hpS
    exact ((padicValRat.eq_zero_iff hq).1 (h p hp hpS)).2 hpq
  · have : Fact p.Prime := ⟨hp⟩
    rw [padicValRat.eq_zero_iff hq]
    exact ⟨fun hd ↦ hpS (hnum ⟨hp, hd, hn⟩), fun hd ↦ hpS (hden ⟨hp, hd, q.den_ne_zero⟩)⟩

/-- If `S` consists of primes, an `S`-factored number `n` is the product of the prime powers
`p ^ v_p(n)` over `p ∈ S`. -/
theorem prod_pow_padicValNat_eq_self_of_mem_factoredNumbers {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) {n : ℕ} (hn : n ∈ Nat.factoredNumbers S) :
    ∏ p ∈ S, p ^ padicValNat p n = n := by
  rw [Nat.mem_factoredNumbers_iff_primeFactors_subset] at hn
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn.1]
  rw [Finsupp.prod_of_support_subset _ (by simpa using hn.2) _ (fun _ _ ↦ pow_zero _)]
  exact Finset.prod_congr rfl fun p hp ↦ by
    rw [Nat.padicValNat_def, Nat.factorization_def n (hS p hp)]

/-- For every real `σ > 0`, the powers `n ^ (-σ)` of the `S`-factored numbers sum to the finite
Euler product `∏_{p ∈ S prime} (1 - p ^ (-σ))⁻¹`. No condition `σ > 1` is needed, since only the
finitely many primes of `S` occur. -/
theorem hasSum_rpow_neg_factoredNumbers {σ : ℝ} (hσ : 0 < σ) (S : Finset ℕ) :
    HasSum (fun n : Nat.factoredNumbers S ↦ ((n : ℕ) : ℝ) ^ (-σ))
      (∏ p ∈ S with p.Prime, (1 - (p : ℝ) ^ (-σ))⁻¹) := by
  let f : ℕ →* ℝ :=
    { toFun := fun n ↦ (n : ℝ) ^ (-σ)
      map_one' := by simp
      map_mul' := fun m n ↦ by rw [Nat.cast_mul, Real.mul_rpow m.cast_nonneg n.cast_nonneg] }
  have hf : ∀ {p : ℕ}, p.Prime → ‖f p‖ < 1 := fun {p} hp ↦ by
    simp only [f, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg p.cast_nonneg _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (neg_neg_of_pos hσ)
  have h := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric hf S).2
  simpa only [f, MonoidHom.coe_mk, OneHom.coe_mk] using h

/-- The reciprocals of the `S`-factored numbers sum to the finite Euler product
`∏_{p ∈ S prime} (1 - 1/p)⁻¹`. -/
theorem hasSum_inv_factoredNumbers (S : Finset ℕ) :
    HasSum (fun n : Nat.factoredNumbers S ↦ ((n : ℕ) : ℝ)⁻¹)
      (∏ p ∈ S with p.Prime, (1 - (p : ℝ)⁻¹)⁻¹) := by
  simpa only [Real.rpow_neg_one] using hasSum_rpow_neg_factoredNumbers one_pos S

/-- For every real `σ > 0`, the powers `n ^ (-σ)` of the `N`-smooth numbers (the positive integers
all of whose prime factors are less than `N`) sum to the finite Euler product
`∏_{p < N prime} (1 - p ^ (-σ))⁻¹`. -/
theorem hasSum_rpow_neg_smoothNumbers {σ : ℝ} (hσ : 0 < σ) (N : ℕ) :
    HasSum (fun n : N.smoothNumbers ↦ ((n : ℕ) : ℝ) ^ (-σ))
      (∏ p ∈ N.primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹) := by
  rw [Nat.smoothNumbers_eq_factoredNumbers, Nat.primesBelow]
  exact hasSum_rpow_neg_factoredNumbers hσ _

end TauCeti

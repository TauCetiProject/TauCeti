/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticFunction.TwistedDivisorSum
public import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Bounds for twisted divisor sums

The absolute value of a complex twisted divisor sum is bounded by the ordinary divisor
sum. For exponent `e > 1`, exchanging complementary divisors bounds the latter by
`n^e ∑' d, d^(-e)`. In particular, the twisted sums are `O(n^e)`, uniformly in the
characters. These estimates control the Fourier coefficients of character Eisenstein series
of weight at least three. The restriction `e > 1` is essential: the reciprocal series
diverges at exponent one.

More generally, `sigma_le_rpow_mul_tsum` bounds `σₖ(n)` by `n^s ∑' d, d^(-s)`
when `k ≤ s` and `s > 1`. In particular, it bounds `σ₁(n)`
by `n^s ∑' d, d^(-s)` for every real `s > 1`. Thus `σ₁(n) = O(n^(1+ε))` for
every `ε > 0`, as needed for the exceptional weight-two Eisenstein series.

The divisor count also satisfies `d(n) ≤ Cε n^ε` for every `ε > 0`
(`exists_pos_card_divisors_le_rpow`). This controls weight-one Eisenstein coefficients.
The estimate follows from the prime-factor product for `d(n)`: sufficiently large primes
need no constant, while the finitely many small primes contribute a bounded factor.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §5.9, Proposition 5.9.1.
-/

public noncomputable section

namespace TauCeti

/-- The norm of a twisted divisor sum is at most the ordinary real divisor sum. -/
theorem norm_twistedDivisorSum_le (e : ℕ) {u v : ℕ}
    (psi : DirichletCharacter ℂ u) (phi : DirichletCharacter ℂ v) (n : ℕ) :
    ‖DirichletCharacter.twistedDivisorSum e psi phi n‖ ≤
      ∑ d ∈ n.divisors, (d : ℝ) ^ e := by
  rw [DirichletCharacter.twistedDivisorSum_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ ↦ ?_)
  simp only [norm_mul, norm_pow, Complex.norm_natCast]
  calc
    ‖psi (n / d)‖ * ‖phi d‖ * (d : ℝ) ^ e ≤ 1 * 1 * (d : ℝ) ^ e := by
      gcongr
      · exact DirichletCharacter.norm_le_one _ _
      · exact DirichletCharacter.norm_le_one _ _
    _ = (d : ℝ) ^ e := by ring

/-- For `k ≤ s` and `s > 1`, the divisor sum `σₖ(n)` is bounded by `n^s` times the
convergent reciprocal-power series. This includes `n = 0`, where the divisor sum is zero. -/
theorem sigma_le_rpow_mul_tsum (k : ℕ) {s : ℝ} (hk : (k : ℝ) ≤ s) (hs : 1 < s)
    (n : ℕ) :
    (ArithmeticFunction.sigma k n : ℝ) ≤
      (n : ℝ) ^ s * ∑' d : ℕ, ((d : ℝ) ^ s)⁻¹ := by
  have hsum := Real.summable_nat_rpow_inv.mpr hs
  rw [ArithmeticFunction.sigma_eq_sum_div, Nat.cast_sum]
  calc
    (∑ d ∈ n.divisors, (((n / d) ^ k : ℕ) : ℝ)) ≤
        ∑ d ∈ n.divisors, (n : ℝ) ^ s * ((d : ℝ) ^ s)⁻¹ := by
      refine Finset.sum_le_sum fun d hd ↦ ?_
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
      have hq : 1 ≤ ((n / d : ℕ) : ℝ) := by
        exact_mod_cast Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)
      calc
        _ = ((n / d : ℕ) : ℝ) ^ (k : ℝ) := by
          rw [Nat.cast_pow, Real.rpow_natCast]
        _ ≤ ((n / d : ℕ) : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le hq hk
        _ = (n : ℝ) ^ s * ((d : ℝ) ^ s)⁻¹ := by
          rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hd0,
            Real.div_rpow (Nat.cast_nonneg n) (Nat.cast_nonneg d), div_eq_mul_inv]
    _ = (n : ℝ) ^ s * ∑ d ∈ n.divisors, ((d : ℝ) ^ s)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ (n : ℝ) ^ s * ∑' d : ℕ, ((d : ℝ) ^ s)⁻¹ := by
      gcongr
      exact hsum.sum_le_tsum n.divisors (fun d _ ↦ by positivity)

/-- For exponent greater than one, a divisor sum is bounded by `n^e` times the convergent
reciprocal-power series. This includes `n = 0`, whose divisor set is empty. -/
theorem sum_divisors_pow_le (e : ℕ) (he : 1 < e) (n : ℕ) :
    ∑ d ∈ n.divisors, (d : ℝ) ^ e ≤
      (n : ℝ) ^ e * ∑' d : ℕ, ((d : ℝ) ^ e)⁻¹ := by
  simpa only [ArithmeticFunction.sigma_apply, Nat.cast_sum, Nat.cast_pow,
    Real.rpow_natCast] using sigma_le_rpow_mul_tsum e le_rfl (by exact_mod_cast he) n

/-- Bound a factor in the divisor-count product, with a correction only below the cutoff. -/
private theorem prime_factor_divisor_count_le {ε : ℝ} (hε : 0 < ε) {P : ℕ}
    (hP : ∀ p : ℕ, P ≤ p → 2 ≤ (p : ℝ) ^ ε) {n p : ℕ} (hp : p ∈ n.primeFactors) :
    (n.factorization p + 1 : ℝ) ≤
      (if p < P then 2 ^ ε / (2 ^ ε - 1) else 1) *
        ((p : ℝ) ^ ε) ^ n.factorization p := by
  let b : ℝ := 2 ^ ε
  have hb : 1 < b := Real.one_lt_rpow (by norm_num) hε
  split_ifs with h
  · -- Bernoulli's inequality bounds the contribution of every small prime uniformly.
    have he := one_add_mul_le_pow (a := b - 1) (by linarith : -2 ≤ b - 1)
      (n.factorization p)
    rw [add_sub_cancel] at he
    have hpow : 1 ≤ b ^ n.factorization p := one_le_pow₀ hb.le
    have hmul : (n.factorization p + 1 : ℝ) * (b - 1) ≤ b * b ^ n.factorization p := by
      nlinarith
    calc
      _ ≤ b / (b - 1) * b ^ n.factorization p := by
        simpa only [div_mul_eq_mul_div] using (le_div_iff₀ (sub_pos.mpr hb)).mpr hmul
      _ ≤ b / (b - 1) * ((p : ℝ) ^ ε) ^ n.factorization p := by
        gcongr
        exact Real.rpow_le_rpow (by norm_num)
          (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le) hε.le
  · rw [one_mul]
    have htwo := hP p (by omega)
    have he : n.factorization p + 1 ≤ 2 ^ n.factorization p := Nat.lt_two_pow_self
    exact (by exact_mod_cast he : (n.factorization p + 1 : ℝ) ≤
      (2 : ℝ) ^ n.factorization p).trans (pow_le_pow_left₀ (by norm_num) htwo _)

/-- For every positive real `ε`, the number of divisors of `n` is bounded by `C n^ε`
with a positive constant independent of `n`. This includes `n = 0`, whose divisor set is empty. -/
theorem exists_pos_card_divisors_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨P, hP⟩ := Filter.eventually_atTop.mp
    (((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop (2 : ℝ)))
  let A : ℝ := 2 ^ ε / (2 ^ ε - 1)
  have hb : 1 < (2 : ℝ) ^ ε := Real.one_lt_rpow (by norm_num) hε
  have hA : 1 ≤ A := (le_div_iff₀ (sub_pos.mpr hb)).mpr (by linarith)
  refine ⟨A ^ P, by positivity, fun n ↦ ?_⟩
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Real.zero_rpow hε.ne']
  have hprod : (∏ p ∈ n.primeFactors, (if p < P then A else 1)) ≤ A ^ P := by
    rw [← Finset.prod_filter]
    simpa using Finset.prod_le_prod_of_subset_of_one_le₀
      (fun p hp ↦ Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
      (fun _ _ ↦ hA.trans' zero_le_one) (fun _ _ _ ↦ hA)
  have hfactor : (∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ n.factorization p) =
      (n : ℝ) ^ ε := by
    simp_rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _), mul_comm ε,
      Real.rpow_natCast_mul (Nat.cast_nonneg _)]
    rw [Real.finsetProd_rpow _ _ (fun p _ ↦ by positivity)]
    norm_cast
    rw [← Nat.prod_primeFactors_pow_factorization hn]
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, (n.factorization p + 1 : ℝ) := by
      rw [Nat.card_divisors hn, Nat.cast_prod]
      simp
    _ ≤ ∏ p ∈ n.primeFactors,
        (if p < P then A else 1) * ((p : ℝ) ^ ε) ^ n.factorization p :=
      Finset.prod_le_prod₀ (fun _ _ ↦ by positivity)
        (fun _ hp ↦ prime_factor_divisor_count_le hε hP hp)
    _ = (∏ p ∈ n.primeFactors, (if p < P then A else 1)) * (n : ℝ) ^ ε := by
      rw [Finset.prod_mul_distrib, hfactor]
    _ ≤ A ^ P * (n : ℝ) ^ ε := mul_le_mul_of_nonneg_right hprod (by positivity)

end TauCeti

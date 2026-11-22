/-
Copyright (c) 2026 The PrimeNumberTheoremAnd and Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The PrimeNumberTheoremAnd contributors, The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticFunction.TwistedDivisorSum
public import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import TauCeti.NumberTheory.ArithmeticFunction.Zeta
public import Mathlib.NumberTheory.Harmonic.Bounds
import TauCeti.NumberTheory.ArithmeticFunction.Sigma.Basic

/-!
# Bounds for divisor sums

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
Comparing every fixed Dirichlet-convolution power of zeta with a power of the divisor count
gives the same subpolynomial bound for every fixed order, including order zero.

The ordered divisor functions also satisfy coefficient-one harmonic and summatory mean
bounds, with natural cutoffs including zero and real cutoffs at least one. The pointwise
coefficient comparisons give explicit mean bounds for three to the number of distinct prime
factors and for the squared ordinary divisor count. The ordinary divisor count itself satisfies
`∑_{n ≤ Z} σ₀(n) ≤ Z (1 + log Z)`. Over the integers, the pairs `(c, d)` with `d ∣ c` and
`0 < |c| < Y` therefore number at most `4 Y (1 + log Y)`, where a pointwise bound for each
`σ₀(|c|)` would lose a power of `Y`.

These mean bounds extend Arend Mellendijk's 2023 formalization of the squarefree divisor
majorants in [Prime Number Theorem and More][PNT-Aux]. Heath-Brown's Lemma 3.1, in notes by
Boris Moroz, treats that squarefree harmonic estimate and a coarser summatory logarithmic
exponent; the bounds here sum over all positive integers and improve the summatory exponent.

[PNT-Aux]: https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/3d28926f52e7cfcb2f872dcff7c6a5266579f7e5/PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/AuxResults.lean

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

namespace ArithmeticFunction

open Finset Nat
open scoped zeta

/-- Every fixed Dirichlet-convolution power of zeta is subpolynomial. The bound includes
order zero, which is the convolution identity, and index zero, where every coefficient is zero. -/
theorem exists_pos_zeta_pow_le_rpow (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ((ζ ^ k : ArithmeticFunction ℕ) n : ℝ) ≤ C * (n : ℝ) ^ ε := by
  cases k with
  | zero =>
    refine ⟨1, by norm_num, fun n ↦ ?_⟩
    by_cases hn : n = 1
    · simp [hn]
    · simp only [pow_zero, ArithmeticFunction.one_apply_ne hn, Nat.cast_zero]
      positivity
  | succ k =>
    obtain ⟨C, hC, hbound⟩ := TauCeti.exists_pos_card_divisors_le_rpow
      (show 0 < ε / (k + 1 : ℝ) by positivity)
    refine ⟨C ^ (k + 1), by positivity, fun n ↦ ?_⟩
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Real.zero_rpow hε.ne']
    have hcard : 1 ≤ n.divisors.card :=
      Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨1, Nat.one_mem_divisors.mpr hn⟩)
    calc
      ((ζ ^ (k + 1)) n : ℝ) ≤ (n.divisors.card : ℝ) ^ k := by
        exact_mod_cast zeta_pow_succ_apply_le_card_divisors_pow k n
      _ ≤ (n.divisors.card : ℝ) ^ (k + 1) :=
        pow_le_pow_right₀ (by exact_mod_cast hcard) (Nat.le_succ _)
      _ ≤ (C * (n : ℝ) ^ (ε / (k + 1 : ℝ))) ^ (k + 1) :=
        pow_le_pow_left₀ (by positivity) (hbound n) _
      _ = C ^ (k + 1) * (n : ℝ) ^ ε := by
        rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n),
          Nat.cast_add, Nat.cast_one, div_mul_cancel₀ _ (by positivity)]


open scoped omega

private theorem sum_zeta_pow_succ_div_eq (k N : ℕ) :
    (∑ n ∈ Ioc 0 N, ((ζ ^ (k + 1)) n : ℝ) / n) =
      ∑ d ∈ Ioc 0 N, ((ζ ^ k) d : ℝ) / d *
        ∑ m ∈ Ioc 0 (N / d), (m : ℝ)⁻¹ := by
  have h := sum_Ioc_mul_eq_sum_sum
    ((((ζ ^ k : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)).pdiv ↑ArithmeticFunction.id)
    (((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℝ).pdiv ↑ArithmeticFunction.id) N
  have hdiv :
      ((((ζ ^ k : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) * ↑ζ).pdiv
        ↑ArithmeticFunction.id) =
      (((ζ ^ k : ArithmeticFunction ℕ) : ArithmeticFunction ℝ).pdiv ↑ArithmeticFunction.id) *
        (((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℝ).pdiv ↑ArithmeticFunction.id) := by
    ext n
    simp only [pdiv_apply, natCoe_apply, id_apply, ArithmeticFunction.mul_apply, sum_div]
    apply sum_congr rfl
    intro a ha
    have hprod := (Nat.mem_divisorsAntidiagonal.mp ha).1
    rw [← hprod, Nat.cast_mul, mul_div_mul_comm]
  rw [← hdiv, ← natCoe_mul, ← pow_succ] at h
  have hinv (m : ℕ) :
      (((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℝ).pdiv ↑ArithmeticFunction.id) m =
        (m : ℝ)⁻¹ := by
    by_cases hm : m = 0 <;> simp [hm, pdiv_apply, natCoe_apply, id_apply, zeta_apply]
  simp_rw [hinv] at h
  simpa only [pdiv_apply, natCoe_apply, id_apply] using h

/-- The harmonic mean of the fixed-order divisor function is bounded by a power of the
ordinary harmonic sum, including cutoff zero and convolution order zero. -/
theorem sum_Ioc_zeta_pow_div_le_harmonic_pow (k N : ℕ) :
    (∑ n ∈ Ioc 0 N, ((ζ ^ k) n : ℝ) / n) ≤ (harmonic N : ℝ) ^ k := by
  have hH : 0 ≤ (harmonic N : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    exact sum_nonneg fun n _ ↦ inv_nonneg.mpr (Nat.cast_nonneg n)
  induction k with
  | zero =>
    simp only [pow_zero, ArithmeticFunction.one_apply, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, ite_div, one_div, zero_div]
    rw [sum_ite_eq']
    split_ifs <;> norm_num
  | succ k ih =>
    rw [sum_zeta_pow_succ_div_eq, pow_succ]
    calc
      _ ≤ ∑ d ∈ Ioc 0 N, ((ζ ^ k) d : ℝ) / d * (harmonic N : ℝ) := by
        apply sum_le_sum
        intro d _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
          ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
        exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.div_le_self N d))
          (by intros; positivity)
      _ = (∑ d ∈ Ioc 0 N, ((ζ ^ k) d : ℝ) / d) * (harmonic N : ℝ) := by
        rw [sum_mul]
      _ ≤ (harmonic N : ℝ) ^ k * (harmonic N : ℝ) :=
        mul_le_mul_of_nonneg_right ih hH

/-- The summatory fixed-order divisor function has the corresponding harmonic bound. -/
theorem sum_Ioc_zeta_pow_le_mul_harmonic_pow (k N : ℕ) :
    (∑ n ∈ Ioc 0 N, ((ζ ^ k) n : ℝ)) ≤
      N * (harmonic N : ℝ) ^ (k - 1) := by
  cases k with
  | zero =>
    by_cases hN : N = 0
    · simp [hN]
    · have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
      simp [ArithmeticFunction.one_apply, sum_ite_eq', hN1]
  | succ k =>
    simp only [Nat.add_sub_cancel]
    have heq := sum_Ioc_mul_zeta_eq_sum (ζ ^ k) N (R := ℕ)
    simp only [natCoe_nat] at heq
    rw [pow_succ, ← Nat.cast_sum, heq, Nat.cast_sum]
    simp only [Nat.cast_mul]
    calc
      _ ≤ ∑ d ∈ Ioc 0 N, ((ζ ^ k) d : ℝ) * ((N : ℝ) / d) := by
        apply sum_le_sum
        intro d _
        exact mul_le_mul_of_nonneg_left Nat.cast_div_le (by positivity)
      _ = N * ∑ d ∈ Ioc 0 N, ((ζ ^ k) d : ℝ) / d := by
        rw [mul_sum]
        apply sum_congr rfl
        intro d _
        ring
      _ ≤ N * (harmonic N : ℝ) ^ k :=
        mul_le_mul_of_nonneg_left (sum_Ioc_zeta_pow_div_le_harmonic_pow k N) (by positivity)

/-- The harmonic ordered-divisor bound with a real cutoff and coefficient one. -/
theorem sum_Ioc_zeta_pow_div_le_one_add_log_pow (k : ℕ) {Z : ℝ} (hZ : 1 ≤ Z) :
    (∑ n ∈ Ioc 0 ⌊Z⌋₊, ((ζ ^ k) n : ℝ) / n) ≤ (1 + Real.log Z) ^ k := by
  have hH : 0 ≤ (harmonic ⌊Z⌋₊ : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    exact sum_nonneg fun n _ ↦ inv_nonneg.mpr (Nat.cast_nonneg n)
  exact (sum_Ioc_zeta_pow_div_le_harmonic_pow k ⌊Z⌋₊).trans
    (pow_le_pow_left₀ hH (harmonic_floor_le_one_add_log Z hZ) k)

/-- The summatory ordered-divisor bound with a real cutoff and coefficient one. -/
theorem sum_Ioc_zeta_pow_le_mul_one_add_log_pow (k : ℕ) {Z : ℝ} (hZ : 1 ≤ Z) :
    (∑ n ∈ Ioc 0 ⌊Z⌋₊, ((ζ ^ k) n : ℝ)) ≤
      Z * (1 + Real.log Z) ^ (k - 1) := by
  have hH : 0 ≤ (harmonic ⌊Z⌋₊ : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    exact sum_nonneg fun n _ ↦ inv_nonneg.mpr (Nat.cast_nonneg n)
  exact (sum_Ioc_zeta_pow_le_mul_harmonic_pow k ⌊Z⌋₊).trans
    (mul_le_mul (Nat.floor_le (zero_le_one.trans hZ))
      (pow_le_pow_left₀ hH (harmonic_floor_le_one_add_log Z hZ) (k - 1))
      (pow_nonneg hH _) (zero_le_one.trans hZ))

/-- A coefficient-one summatory bound for three to the number of distinct prime factors. -/
theorem sum_Ioc_three_pow_cardDistinctFactors_le_mul_one_add_log_sq {Z : ℝ} (hZ : 1 ≤ Z) :
    (∑ n ∈ Ioc 0 ⌊Z⌋₊, (3 : ℝ) ^ ω n) ≤ Z * (1 + Real.log Z) ^ 2 := by
  refine le_trans (sum_le_sum fun n hn ↦ ?_) (sum_Ioc_zeta_pow_le_mul_one_add_log_pow 3 hZ)
  exact_mod_cast pow_cardDistinctFactors_le_zeta_pow 3 (ne_of_gt (mem_Ioc.mp hn).1)

/-- A coefficient-one summatory bound for the squared ordinary divisor function. -/
theorem sum_Ioc_sigma_zero_sq_le_mul_one_add_log_cube {Z : ℝ} (hZ : 1 ≤ Z) :
    (∑ n ∈ Ioc 0 ⌊Z⌋₊, (sigma 0 n : ℝ) ^ 2) ≤ Z * (1 + Real.log Z) ^ 3 := by
  refine le_trans (sum_le_sum fun n _ ↦ ?_) (sum_Ioc_zeta_pow_le_mul_one_add_log_pow 4 hZ)
  exact_mod_cast sigma_zero_sq_le_zeta_pow_four n

/-- The summatory divisor function satisfies `∑_{n ≤ Z} σ₀(n) ≤ Z (1 + log Z)` for `Z ≥ 1`. -/
theorem sum_Ioc_sigma_zero_le_mul_one_add_log {Z : ℝ} (hZ : 1 ≤ Z) :
    (∑ n ∈ Ioc 0 ⌊Z⌋₊, (sigma 0 n : ℝ)) ≤ Z * (1 + Real.log Z) := by
  simpa only [sq, zeta_mul_zeta, Nat.add_one_sub_one, pow_one] using
    sum_Ioc_zeta_pow_le_mul_one_add_log_pow 2 hZ

end ArithmeticFunction

namespace TauCeti

open Finset

/-- Sending `(c, d)` to `((|c|, |d|), (sign c, sign d))` embeds the integer pairs with `d ∣ c` and
`0 < |c| < Y` into the natural divisor pairs below `Y`, times a choice of two signs. -/
private theorem mapsTo_injOn_setOf_dvd_of_abs_lt (Y : ℝ) :
    Set.MapsTo (fun p : ℤ × ℤ ↦ ((p.1.natAbs, p.2.natAbs), (p.1.sign, p.2.sign)))
        {p : ℤ × ℤ | p.1 ≠ 0 ∧ |(p.1 : ℝ)| < Y ∧ p.2 ∣ p.1}
        ↑(((Ioc 0 ⌊Y⌋₊).biUnion fun a ↦ a.divisors.image fun d ↦ (a, d)) ×ˢ
          (({1, -1} : Finset ℤ) ×ˢ ({1, -1} : Finset ℤ))) ∧
      Set.InjOn (fun p : ℤ × ℤ ↦ ((p.1.natAbs, p.2.natAbs), (p.1.sign, p.2.sign)))
        {p : ℤ × ℤ | p.1 ≠ 0 ∧ |(p.1 : ℝ)| < Y ∧ p.2 ∣ p.1} := by
  have hsign {c : ℤ} (hc : c ≠ 0) : c.sign ∈ ({1, -1} : Finset ℤ) := by
    rcases lt_or_gt_of_ne hc with h | h
    · simp [Int.sign_eq_neg_one_of_neg h]
    · simp [Int.sign_eq_one_of_pos h]
  refine ⟨?_, ?_⟩
  · rintro ⟨c, d⟩ ⟨hc, hcY, hd⟩
    have hd0 : d ≠ 0 := by rintro rfl; exact hc (zero_dvd_iff.mp hd)
    have hcN : c.natAbs ≤ ⌊Y⌋₊ := Nat.le_floor (by rw [Nat.cast_natAbs, Int.cast_abs]; exact hcY.le)
    simp only [coe_product, Set.mem_prod, mem_coe, mem_biUnion, mem_Ioc, mem_image,
      Nat.mem_divisors, Prod.mk.injEq]
    exact ⟨⟨c.natAbs, ⟨Int.natAbs_pos.mpr hc, hcN⟩, d.natAbs,
      ⟨Int.natAbs_dvd_natAbs.mpr hd, Int.natAbs_ne_zero.mpr hc⟩, rfl, rfl⟩, hsign hc, hsign hd0⟩
  · rintro ⟨c, d⟩ - ⟨c', d'⟩ - h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    rw [Prod.mk.injEq, ← Int.sign_mul_natAbs c, ← Int.sign_mul_natAbs c',
      ← Int.sign_mul_natAbs d, ← Int.sign_mul_natAbs d', h1, h2, h3, h4]
    exact ⟨rfl, rfl⟩

/-- There are finitely many integer pairs `(c, d)` with `d ∣ c` and `0 < |c| < Y`. -/
theorem finite_setOf_dvd_of_abs_lt (Y : ℝ) :
    {p : ℤ × ℤ | p.1 ≠ 0 ∧ |(p.1 : ℝ)| < Y ∧ p.2 ∣ p.1}.Finite :=
  Set.Finite.of_injOn (mapsTo_injOn_setOf_dvd_of_abs_lt Y).1
    (mapsTo_injOn_setOf_dvd_of_abs_lt Y).2 (finite_toSet _)

/-- The integer pairs `(c, d)` with `d ∣ c` and `0 < |c| < Y` number at most `4 Y (1 + log Y)`
for `Y ≥ 1`. This is the summatory divisor bound over the integers, both signs of `c` and of
`d` being counted. -/
theorem ncard_setOf_dvd_of_abs_lt_le {Y : ℝ} (hY : 1 ≤ Y) :
    ({p : ℤ × ℤ | p.1 ≠ 0 ∧ |(p.1 : ℝ)| < Y ∧ p.2 ∣ p.1}.ncard : ℝ) ≤
      4 * (Y * (1 + Real.log Y)) := by
  classical
  have hle := Set.ncard_le_ncard_of_injOn _ (mapsTo_injOn_setOf_dvd_of_abs_lt Y).1
    (mapsTo_injOn_setOf_dvd_of_abs_lt Y).2 (finite_toSet _)
  rw [Set.ncard_coe_finset, card_product, card_product] at hle
  have hS : ({1, -1} : Finset ℤ).card = 2 := by decide
  have hR : (((Ioc 0 ⌊Y⌋₊).biUnion fun a ↦ a.divisors.image fun d ↦ (a, d)).card : ℝ) ≤
      ∑ a ∈ Ioc 0 ⌊Y⌋₊, (ArithmeticFunction.sigma 0 a : ℝ) := by
    simp only [ArithmeticFunction.sigma_zero_apply]
    exact_mod_cast card_biUnion_le.trans (sum_le_sum fun a _ ↦ card_image_le)
  rw [hS] at hle
  have := ArithmeticFunction.sum_Ioc_sigma_zero_le_mul_one_add_log hY
  calc ({p : ℤ × ℤ | p.1 ≠ 0 ∧ |(p.1 : ℝ)| < Y ∧ p.2 ∣ p.1}.ncard : ℝ)
      ≤ (((Ioc 0 ⌊Y⌋₊).biUnion fun a ↦ a.divisors.image fun d ↦ (a, d)).card * (2 * 2) : ℕ) := by
        exact_mod_cast hle
    _ ≤ 4 * (Y * (1 + Real.log Y)) := by push_cast; linarith

end TauCeti

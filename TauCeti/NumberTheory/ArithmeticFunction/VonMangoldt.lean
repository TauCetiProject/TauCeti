/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.NumberTheory.PrimeCounting
import TauCeti.Analysis.SpecificLimits.ReciprocalSeries
import TauCeti.NumberTheory.Chebyshev.PrimeTail
import TauCeti.NumberTheory.SumPrimePow

/-!
# The von Mangoldt function at the higher prime powers

The weights `Λ(n) / n` at the non-prime `n` are supported on the prime powers `p ^ k` with
`k ≥ 2`, and their sum `∑ₚ ∑_{k ≥ 2} log p / p ^ k = ∑ₚ log p / (p (p - 1))` is finite and at
most `2 log 4`. This explicit absolute constant bounds the higher-prime-power part of every
twisted von Mangoldt series on `1 ≤ re s` and separates the prime and von Mangoldt forms of
Mertens' first theorem.

The real-exponent regrouping argument adapts Mathlib's
`ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div` and its private
`summable_F''` argument in `Mathlib/NumberTheory/LSeries/PrimesInAP.lean` to `σ > 1/2`.
Summability at exponent one specializes that result. The explicit bound regroups by the prime base
(`Nat.sum_Icc_eq_sum_primesLE_sum_Icc_log`), sums each geometric tail to
`1 / (p (p - 1)) ≤ 2 / p ^ 2`, and applies Chebyshev's reciprocal-square prime tail bound
(`TauCeti.sum_log_div_sq_le_of_prime`).

The higher-prime-power series is summable for every real exponent `σ > 1/2`, with exact
geometric expansion `∑ₚ log p / (p ^ σ * (p ^ σ - 1))`. For `σ ≥ 1`, a finite family of
prime divisors of any level is bounded by the endpoint prime series, uniformly in the level.

## Main results

* `ArithmeticFunction.vonMangoldt.summable_nonprime_div`: `∑ₙ (if n is prime then 0 else Λ(n)) / n`
  converges by specializing the real-exponent result at one.
* `ArithmeticFunction.vonMangoldt.summable_nonprime_div_rpow` and
  `ArithmeticFunction.vonMangoldt.hasSum_prime_log_div_rpow_mul_sub_one`: convergence and the
  exact geometric expansion for `σ > 1/2`.
* `Nat.sum_primeFactors_log_div_rpow_mul_sub_one_le`: the level's
  finite geometric correction is bounded by the endpoint majorant for `σ ≥ 1`.
* `ArithmeticFunction.vonMangoldt.sum_Icc_nonprime_div_le`: for every `N`, the finite sum over
  `1 ≤ n ≤ N` is at most `∑_{p ≤ N} log p / (p (p - 1))`.
* `ArithmeticFunction.vonMangoldt.sum_Icc_nonprime_div_le_two_mul_log_four` and
  `ArithmeticFunction.vonMangoldt.tsum_nonprime_div_le`: the finite and infinite sums are at most
  `2 log 4`.
-/

public section

open ArithmeticFunction Finset

namespace ArithmeticFunction.vonMangoldt

private theorem summable_prime_geometric {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable fun p : Nat.Primes ↦ Real.log p / ((p : ℝ) ^ σ * ((p : ℝ) ^ σ - 1)) := by
  have hσ0 : 0 < σ := by linarith
  have hv : Summable fun n : ℕ ↦ vonMangoldt n / (n : ℝ) ^ (2 * σ) := by
    apply Complex.summable_ofReal.mp
    have h := LSeriesSummable_vonMangoldt (s := ((2 * σ : ℝ) : ℂ))
      (by simpa using (by linarith : 1 < 2 * σ))
    apply h.congr
    intro n
    by_cases hn : n = 0
    · simp [hn, LSeries.term]
    · simp only [LSeries.term_of_ne_zero hn, Complex.ofReal_div,
        Complex.ofReal_cpow n.cast_nonneg, Complex.ofReal_natCast]
  have hpseries : Summable fun p : Nat.Primes ↦ Real.log p / (p : ℝ) ^ (2 * σ) := by
    refine (hv.subtype Nat.Prime).congr fun p ↦ ?_
    simp only [Function.comp_apply, vonMangoldt_apply_prime p.prop]
  have htwo : 1 < (2 : ℝ) ^ σ := Real.one_lt_rpow (by norm_num) hσ0
  have hden : 0 < 1 - ((2 : ℝ) ^ σ)⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ htwo)
  refine (hpseries.div_const (1 - ((2 : ℝ) ^ σ)⁻¹)).of_nonneg_of_le (fun p ↦ ?_) (fun p ↦ ?_)
  · have hp : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
    exact div_nonneg (Real.log_nonneg hp.le)
      (mul_nonneg (Real.rpow_nonneg p.val.cast_nonneg _)
        (sub_nonneg.mpr (Real.one_lt_rpow hp hσ0).le))
  · have hp : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
    have ha : 1 < (p : ℝ) ^ σ := Real.one_lt_rpow hp hσ0
    have hb : (2 : ℝ) ^ σ ≤ (p : ℝ) ^ σ := Real.rpow_le_rpow (by norm_num)
      (by exact_mod_cast p.prop.two_le) hσ0.le
    have hid : Real.log p / ((p : ℝ) ^ σ * ((p : ℝ) ^ σ - 1)) =
        (Real.log p / (p : ℝ) ^ (2 * σ)) / (1 - ((p : ℝ) ^ σ)⁻¹) := by
      rw [mul_comm (2 : ℝ) σ, Real.rpow_mul p.val.cast_nonneg, Real.rpow_two]
      field_simp [ne_of_gt (zero_lt_one.trans ha), sub_ne_zero.mpr ha.ne']
    rw [hid]
    exact div_le_div_of_nonneg_left
      (div_nonneg (Real.log_nonneg hp.le) (Real.rpow_nonneg p.val.cast_nonneg _)) hden
      (sub_le_sub_left ((inv_le_inv₀ (zero_lt_one.trans ha) (zero_lt_one.trans htwo)).mpr hb) 1)

private theorem hasSum_nonprime_prime_pow_div_rpow (p : Nat.Primes) {σ : ℝ} (hσ : 0 < σ) :
    HasSum (fun k : ℕ ↦
      (if ((p : ℕ) ^ (k + 2)).Prime then 0 else vonMangoldt ((p : ℕ) ^ (k + 2))) /
        (((p : ℕ) ^ (k + 2) : ℕ) : ℝ) ^ σ)
      (Real.log p / ((p : ℝ) ^ σ * ((p : ℝ) ^ σ - 1))) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
  have hpow : 1 < (p : ℝ) ^ σ := Real.one_lt_rpow hp hσ
  have hg := ((hasSum_geometric_of_lt_one
    (inv_nonneg.mpr (Real.rpow_nonneg p.val.cast_nonneg σ))
    (inv_lt_one_of_one_lt₀ hpow)).mul_right (((p : ℝ) ^ σ)⁻¹ ^ 2)).mul_left (Real.log p)
  have hv : Real.log p * ((1 - ((p : ℝ) ^ σ)⁻¹)⁻¹ * ((p : ℝ) ^ σ)⁻¹ ^ 2) =
      Real.log p / ((p : ℝ) ^ σ * ((p : ℝ) ^ σ - 1)) := by
    field_simp [ne_of_gt (zero_lt_one.trans hpow), sub_ne_zero.mpr hpow.ne']
  rw [hv] at hg
  refine hg.congr_fun fun k ↦ ?_
  rw [ite_eq_right (fun h ↦ (Nat.Prime.not_prime_pow (by omega : 2 ≤ k + 2) h).elim),
    vonMangoldt_apply_pow (by omega : k + 2 ≠ 0), vonMangoldt_apply_prime p.prop,
    Nat.cast_pow, ← Real.rpow_pow_comm p.val.cast_nonneg σ (k + 2)]
  simp only [div_eq_mul_inv, pow_add, mul_inv, inv_pow]

/-- The nonprime von Mangoldt series is summable for every real exponent greater than one half.
The prime-power regrouping adapts Mathlib's
`ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div` and the private
`summable_F''` argument in `Mathlib/NumberTheory/LSeries/PrimesInAP.lean`. -/
theorem summable_nonprime_div_rpow {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable fun n : ℕ ↦ (if n.Prime then 0 else vonMangoldt n) / (n : ℝ) ^ σ := by
  let f (n : ℕ) : ℝ := (if n.Prime then 0 else vonMangoldt n) / (n : ℝ) ^ σ
  have hσ0 : 0 < σ := by linarith
  have hprod : Summable (fun q : Nat.Primes × ℕ ↦ f (q.1 ^ (q.2 + 2))) := by
    refine (summable_prod_of_nonneg (fun q ↦ ?_)).mpr ⟨?_, ?_⟩
    · exact div_nonneg (ite_nonneg le_rfl vonMangoldt_nonneg)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · exact fun p ↦ (hasSum_nonprime_prime_pow_div_rpow p hσ0).summable
    · have hfiber (p : Nat.Primes) : (∑' k : ℕ, f (p ^ (k + 2))) =
          Real.log p / ((p : ℝ) ^ σ * ((p : ℝ) ^ σ - 1)) :=
        (hasSum_nonprime_prime_pow_div_rpow p hσ0).tsum_eq
      simpa only [hfiber] using summable_prime_geometric hσ
  have hinj : Function.Injective (fun q : Nat.Primes × ℕ ↦ (q.1 : ℕ) ^ (q.2 + 2)) :=
    Subtype.val_injective.comp Nat.Primes.prodNatEquiv.injective |>.comp
      (Function.Injective.prodMap (fun ⦃_ _⦄ ↦ id) (add_left_injective 1))
  apply (hinj.summable_iff (f := f) ?_).mp hprod
  intro n hn
  by_cases hp : n.Prime
  · simp only [f, hp, ↓reduceIte, zero_div]
  by_cases hpp : IsPrimePow n
  · obtain ⟨p, k, hprime, heq⟩ := (isPrimePow_iff_pow_succ n).mp hpp
    cases k with
    | zero =>
        have hnprime : n.Prime := by
          simpa only [← heq, zero_add, pow_one] using (Nat.prime_iff.mpr hprime)
        exact False.elim (hp hnprime)
    | succ k => exact False.elim (hn ⟨(⟨p, Nat.prime_iff.mpr hprime⟩, k), heq⟩)
  · simp only [f, vonMangoldt_eq_zero_iff.mpr hpp, ite_self, zero_div]

/-- The von Mangoldt weights at non-primes divided by `n` are summable, as the exponent-one
case of convergence for every exponent greater than one half. -/
theorem summable_nonprime_div :
    Summable fun n : ℕ ↦ (if n.Prime then 0 else vonMangoldt n) / n := by
  simpa only [Real.rpow_one] using summable_nonprime_div_rpow (σ := 1) (by norm_num)

/-- Regrouping by the prime base evaluates the higher powers as a geometric prime series. -/
theorem hasSum_prime_log_div_rpow_mul_sub_one {σ : ℝ} (hσ : 1 / 2 < σ) :
    HasSum (fun p : Nat.Primes ↦ Real.log p / ((p : ℝ) ^ σ * ((p : ℝ) ^ σ - 1)))
      (∑' n : ℕ, (if n.Prime then 0 else vonMangoldt n) / (n : ℝ) ^ σ) := by
  let f : ℕ → ℝ := fun n ↦ (if n.Prime then 0 else vonMangoldt n) / (n : ℝ) ^ σ
  have hf : Summable f := summable_nonprime_div_rpow hσ
  have hsupp : Function.support f ⊆ {n | IsPrimePow n} := by
    intro n hn
    by_contra h
    exact hn (by simp [f, vonMangoldt_eq_zero_iff.mpr h])
  have hprod : Summable (fun q : Nat.Primes × ℕ ↦ f (q.1 ^ (q.2 + 2))) :=
    hf.comp_injective (Subtype.val_injective.comp Nat.Primes.prodNatEquiv.injective |>.comp
      (Function.Injective.prodMap (fun ⦃_ _⦄ ↦ id) (add_left_injective 1)))
  have hg := hprod.hasSum.prod_fiberwise
    (fun p ↦ hasSum_nonprime_prime_pow_div_rpow p (by linarith : 0 < σ))
  have hzero (p : Nat.Primes) : f p = 0 := by simp [f, p.prop]
  have hsplit : (∑' n, f n) = ∑' (p : Nat.Primes) (k : ℕ), f (p ^ (k + 2)) := by
    simpa only [hzero, tsum_zero, zero_add] using
      tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers hf hsupp
  simpa only [hprod.tsum_prod, ← hsplit] using hg

/-- The finite geometric correction from any level's prime divisors is at most the endpoint
prime-series majorant, uniformly for real exponents at least one. -/
theorem _root_.Nat.sum_primeFactors_log_div_rpow_mul_sub_one_le (N : ℕ) {σ : ℝ} (hσ : 1 ≤ σ) :
    (∑ p ∈ N.primeFactors, Real.log p / ((p : ℝ) ^ σ * ((p : ℝ) ^ σ - 1))) ≤
      ∑' p : Nat.Primes, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hterm (p : Nat.Primes) :
      Real.log p / ((p : ℝ) ^ σ * ((p : ℝ) ^ σ - 1)) ≤
        Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
    have hp : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
    have hpσ : (p : ℝ) ≤ (p : ℝ) ^ σ := by
      simpa using Real.rpow_le_rpow_of_exponent_le hp.le hσ
    exact div_le_div_of_nonneg_left (Real.log_nonneg hp.le)
      (mul_pos (zero_lt_one.trans hp) (sub_pos.mpr hp))
      (mul_le_mul hpσ (sub_le_sub_right hpσ 1) (sub_nonneg.mpr hp.le)
        (Real.rpow_nonneg p.val.cast_nonneg σ))
  have hg := vonMangoldt.hasSum_prime_log_div_rpow_mul_sub_one (σ := 1) (by norm_num)
  simp only [Real.rpow_one] at hg
  have hnonneg (p : Nat.Primes) :
      0 ≤ Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le))
      (mul_nonneg p.val.cast_nonneg (sub_nonneg.mpr
        (by exact_mod_cast p.prop.one_lt.le)))
  calc
    _ ≤ ∑ p ∈ N.primeFactors, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) :=
      Finset.sum_le_sum fun p hp ↦ hterm ⟨p, Nat.prime_of_mem_primeFactors hp⟩
    _ = ∑ p ∈ (N.primeFactors.subtype Nat.Prime : Finset Nat.Primes),
        Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
      exact (Finset.sum_subtype_of_mem
        (fun p : ℕ ↦ Real.log p / ((p : ℝ) * ((p : ℝ) - 1)))
        (fun p hp ↦ Nat.prime_of_mem_primeFactors hp)).symm
    _ ≤ ∑' p : Nat.Primes, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) :=
      sum_le_hasSum (L := SummationFilter.unconditional Nat.Primes)
        (N.primeFactors.subtype Nat.Prime : Finset Nat.Primes)
        (fun p _ ↦ hnonneg p) hg.summable.hasSum

/-- Regrouping by the prime base bounds the non-prime von Mangoldt sum up to `N` by the
prime-indexed geometric majorant `∑_{p ≤ N} log p / (p (p - 1))`. -/
theorem sum_Icc_nonprime_div_le (N : ℕ) :
    ∑ n ∈ Icc 1 N, (if n.Prime then 0 else vonMangoldt n) / n ≤
      ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
  set f : ℕ → ℝ := fun n ↦ (if n.Prime then 0 else vonMangoldt n) / n
  have hf (n : ℕ) (hn : ¬IsPrimePow n) : f n = 0 := by
    simp [f, vonMangoldt_eq_zero_iff.mpr hn]
  rw [Nat.sum_Icc_eq_sum_primesLE_sum_Icc_log hf N]
  refine sum_le_sum fun p hp ↦ ?_
  have hp_prime : p.Prime := Nat.prime_of_mem_primesLE hp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (mod_cast hp_prime.one_lt.le)
  calc ∑ k ∈ Icc 1 (p.log N), f (p ^ k)
      = ∑ k ∈ Icc 2 (p.log N), Real.log p * ((p : ℝ) ^ k)⁻¹ := by
        rcases lt_or_ge (p.log N) 1 with hlt | hge
        · rw [Icc_eq_empty (by omega), Icc_eq_empty (by omega), sum_empty, sum_empty]
        · rw [← insert_Icc_add_one_left_eq_Icc hge, sum_insert (by simp)]
          have hf1 : f (p ^ 1) = 0 := by simp [f, hp_prime]
          rw [hf1, zero_add]
          refine sum_congr rfl fun k hk ↦ ?_
          have hk2 : 2 ≤ k := (mem_Icc.mp hk).1
          have hnot : ¬(p ^ k).Prime := Nat.Prime.not_prime_pow hk2
          simp [f, hnot, vonMangoldt_apply_pow (by omega : k ≠ 0),
            vonMangoldt_apply_prime hp_prime, div_eq_mul_inv]
    _ = Real.log p * ∑ k ∈ Icc 2 (p.log N), ((p : ℝ) ^ k)⁻¹ := (mul_sum _ _ _).symm
    _ ≤ Real.log p * (1 / ((p : ℝ) * ((p : ℝ) - 1))) :=
        mul_le_mul_of_nonneg_left (TauCeti.sum_Icc_inv_pow_le hp_prime.ne_one (p.log N)) hlog
    _ = Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := mul_one_div _ _

/-- For every `N`, the finite sum of `Λ(n) / n` over non-prime `1 ≤ n ≤ N` is at most `2 log 4`. -/
theorem sum_Icc_nonprime_div_le_two_mul_log_four (N : ℕ) :
    ∑ n ∈ Icc 1 N, (if n.Prime then 0 else vonMangoldt n) / n ≤ 2 * Real.log 4 := by
  calc ∑ n ∈ Icc 1 N, (if n.Prime then 0 else vonMangoldt n) / n
      ≤ ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) :=
        sum_Icc_nonprime_div_le N
    _ ≤ ∑ p ∈ Nat.primesLE N, 2 * (Real.log p / (p : ℝ) ^ 2) := by
        refine sum_le_sum fun p hp ↦ ?_
        have hp2 : (2 : ℝ) ≤ p := mod_cast (Nat.prime_of_mem_primesLE hp).two_le
        have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
        rw [mul_div_assoc', le_div_iff₀ (sq_pos_of_pos (by linarith)),
          div_mul_eq_mul_div, div_le_iff₀ (by nlinarith)]
        have hsq : (p : ℝ) ^ 2 ≤ 2 * ((p : ℝ) * ((p : ℝ) - 1)) := by nlinarith
        linarith [mul_le_mul_of_nonneg_left hsq hlog]
    _ = 2 * ∑ p ∈ Nat.primesLE N, Real.log p / (p : ℝ) ^ 2 := (mul_sum _ _ _).symm
    _ ≤ 2 * (2 * Real.log 4 / 2) := by
        gcongr
        exact TauCeti.sum_log_div_sq_le_of_prime zero_lt_two
          (fun p hp ↦ Nat.prime_of_mem_primesLE hp)
          (fun p hp ↦ mod_cast (Nat.prime_of_mem_primesLE hp).two_le)
    _ = 2 * Real.log 4 := by ring

/-- The infinite sum of `Λ(n) / n` over all non-prime `n : ℕ` is at most `2 log 4`. -/
theorem tsum_nonprime_div_le :
    (∑' n : ℕ, (if n.Prime then 0 else vonMangoldt n) / n) ≤ 2 * Real.log 4 := by
  refine summable_nonprime_div.tsum_le_of_sum_le fun s ↦ ?_
  rw [← s.sum_erase (a := 0) (by simp)]
  refine (sum_le_sum_of_subset_of_nonneg (fun n hn ↦ ?_) fun _ _ _ ↦
    div_nonneg (by split_ifs <;> simp [vonMangoldt_nonneg]) (Nat.cast_nonneg _)).trans
      (sum_Icc_nonprime_div_le_two_mul_log_four (s.sup id))
  exact mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (ne_of_mem_erase hn),
    le_sup (f := id) (mem_of_mem_erase hn)⟩

end ArithmeticFunction.vonMangoldt

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.NormCoeff
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.VonMangoldt
public import TauCeti.NumberTheory.NumberField.PrimeIdeal
import Mathlib.RingTheory.RamificationInertia.Basic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting

/-!
# Norm coefficients of the ideal von Mangoldt transform

In the coefficient of index `p ^ k`, a prime ideal over `p` of inertia degree `d` contributes
only if `d ∣ k`, and then its logarithmic weight is `d * log p`. The fundamental identity
`∑ e d = [K : ℚ]` bounds the norm of the coefficient of a bounded twist by `[K : ℚ] * Λ(n)`.
This gives a rational majorant for the coefficients of smoothed prime sums over number fields.

The number-field inputs are Mathlib's `Ideal.pow_inertiaDeg` and
`Ideal.sum_ramification_inertia_eq_finrank`.
-/

public section

open ArithmeticFunction Ideal
open scoped NumberField nonZeroDivisors

namespace TauCeti.IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K]

/-- The coefficients of an ideal von Mangoldt transform vanish off the rational prime powers. -/
@[simp]
theorem normCoeff_vonMangoldtTransform_eq_zero_of_not_isPrimePow
    (f : IdealArithmeticFunction K) {n : ℕ} (hn : ¬ IsPrimePow n) :
    normCoeff K f.vonMangoldtTransform n = 0 := by
  rw [normCoeff_eq_sum_normFiber]
  refine Finset.sum_eq_zero fun A hA ↦ ?_
  rw [f.vonMangoldtTransform_apply, vonMangoldt_eq_zero_of_not_isPrimePow, mul_zero]
  intro hA'
  exact hn ((mem_normFiber K).mp hA ▸ isPrimePow_absNorm ⟨A, hA'⟩)

section PrimesOver

variable {p : ℕ} [hp : Fact p.Prime]

/-- A prime of `𝓞 K` over `p`, as a nonzero ideal. -/
private def primeOverNonZero (P : (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K)) :
    (Ideal (𝓞 K))⁰ :=
  ⟨P.val, NumberField.mem_nonZeroDivisors_of_prime_of_liesOver hp.out P.val⟩

omit hp in
/-- If the inertia degree of a prime over `p` divides `k > 0`, the quotient is positive. -/
private theorem div_inertiaDeg_pos (P : (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K)) {k : ℕ}
    (hk : 0 < k) (hd : P.val.inertiaDeg ℤ ∣ k) : 0 < k / P.val.inertiaDeg ℤ :=
  Nat.div_pos (Nat.le_of_dvd hk hd) (Ideal.inertiaDeg_pos P.val ℤ)

/-- A prime over `p` is a prime element of the ideals of `𝓞 K`. -/
private theorem prime_primeOverNonZero (P : (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K)) :
    Prime P.val :=
  Ideal.prime_of_isPrime (nonZeroDivisors.ne_zero (primeOverNonZero P).prop) inferInstance

/-- A positive power of a prime over `p` is a prime power ideal. -/
private theorem isPrimePow_primeOverNonZero_pow (P : (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K))
    {e : ℕ} (he : 0 < e) : IsPrimePow ((primeOverNonZero P ^ e : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) :=
  ⟨P.val, e, prime_primeOverNonZero P, he, by simp [primeOverNonZero]⟩

end PrimesOver

/-- At `p ^ k`, a prime of inertia degree `d` above `p` contributes the weight of its
`(k / d)`-th power times the logarithm of its own norm, and only when `d ∣ k`. -/
theorem normCoeff_vonMangoldtTransform_prime_pow (f : IdealArithmeticFunction K)
    {p k : ℕ} [hp : Fact p.Prime] (hk : 0 < k) :
    normCoeff K f.vonMangoldtTransform (p ^ k) =
      ∑ P ∈ (Finset.univ : Finset ((span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K))).filter
        (fun P ↦ P.val.inertiaDeg ℤ ∣ k),
        f (⟨P.val, NumberField.mem_nonZeroDivisors_of_prime_of_liesOver hp.out P.val⟩ ^
          (k / P.val.inertiaDeg ℤ)) *
          Real.log (absNorm P.val) := by
  classical
  let P₀ : Ideal ℤ := span {(p : ℤ)}
  rw [normCoeff_eq_sum_normFiber, ← Finset.sum_filter_of_ne (p :=
    fun A : (Ideal (𝓞 K))⁰ ↦ IsPrimePow (A : Ideal (𝓞 K)))
    (fun _ _ hA ↦ ((f.vonMangoldtTransform_ne_zero_iff).mp hA).1)]
  symm
  -- A prime above `p` contributes at most one power, determined by its inertia degree.
  refine Finset.sum_bij (fun P _ ↦ primeOverNonZero P ^ (k / P.val.inertiaDeg ℤ)) ?_ ?_ ?_ ?_
  · intro P hP
    have hd := (Finset.mem_filter.mp hP).2
    refine Finset.mem_filter.mpr ⟨(mem_normFiber K).mpr ?_,
      isPrimePow_primeOverNonZero_pow P (div_inertiaDeg_pos P hk hd)⟩
    simp only [SubmonoidClass.coe_pow, primeOverNonZero, map_pow, ← Ideal.pow_inertiaDeg p P.val,
      ← pow_mul]
    rw [Nat.mul_div_cancel' hd]
  · intro P hP Q _ hPQ
    exact Subtype.ext (eq_of_prime_pow_eq (prime_primeOverNonZero P) (prime_primeOverNonZero Q)
      (div_inertiaDeg_pos P hk (Finset.mem_filter.mp hP).2) (congrArg Subtype.val hPQ))
  · -- A prime over `p` dividing the given prime power must be its base.
    intro A hA
    obtain ⟨hAn, Q, j, hQ, _, hpow⟩ := Finset.mem_filter.mp hA
    have hAnorm := (mem_normFiber K).mp hAn
    obtain ⟨P, hP, hpP, hdiv⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp.out
      (A : Ideal (𝓞 K)) (hAnorm ▸ dvd_pow_self p hk.ne')
    let : P.LiesOver P₀ := ⟨hpP.symm⟩
    let q : P₀.primesOver (𝓞 K) := ⟨P, hP.isPrime, inferInstance⟩
    have hPQ : P = Q := by
      have hPd : Prime P := Ideal.prime_of_isPrime hP.ne_bot_of_isIntegral_int hP.isPrime
      have hdiv' : P ∣ Q := hPd.dvd_of_dvd_pow (hpow ▸ hdiv)
      exact ((Ideal.isPrime_of_prime hQ).isMaximal hQ.ne_zero).eq_of_le hP.ne_top
        (Ideal.le_of_dvd hdiv') |>.symm
    have hdegree : P.inertiaDeg ℤ * j = k := (Nat.pow_right_inj hp.out.one_lt).mp (by
      rw [pow_mul, Ideal.pow_inertiaDeg p P, ← map_pow]
      exact (congrArg absNorm ((congrArg (· ^ j) hPQ).trans hpow)).trans hAnorm)
    have hd : q.val.inertiaDeg ℤ ∣ k := ⟨j, hdegree.symm⟩
    refine ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩, Subtype.ext ?_⟩
    rw [SubmonoidClass.coe_pow, ← hdegree, Nat.mul_div_cancel_left _ (Ideal.inertiaDeg_pos q.val ℤ)]
    exact (congrArg (· ^ j) hPQ).trans hpow
  · intro P hP
    exact (f.vonMangoldtTransform_apply_prime_pow (prime_primeOverNonZero P)
      (div_inertiaDeg_pos P hk (Finset.mem_filter.mp hP).2)).symm

/-- The norm of a twisted von Mangoldt coefficient is at most the field degree times the
rational von Mangoldt coefficient. The twist need only be bounded by one on prime powers. -/
theorem norm_normCoeff_vonMangoldtTransform_le (f : IdealArithmeticFunction K)
    (hf : ∀ A : (Ideal (𝓞 K))⁰, IsPrimePow (A : Ideal (𝓞 K)) → ‖f A‖ ≤ 1) (n : ℕ) :
    ‖normCoeff K f.vonMangoldtTransform n‖ ≤ (Module.finrank ℚ K : ℝ) * Λ n := by
  classical
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
    let : Fact p.Prime := ⟨hp⟩
    let P₀ : Ideal ℤ := span {(p : ℤ)}
    have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
    have hN (P : P₀.primesOver (𝓞 K)) :
        Real.log (absNorm P.val : ℝ) = (P.val.inertiaDeg ℤ : ℝ) * Real.log (p : ℝ) := by
      rw [← Ideal.pow_inertiaDeg p P.val, Nat.cast_pow, Real.log_pow]
    rw [f.normCoeff_vonMangoldtTransform_prime_pow hk, vonMangoldt_apply_pow hk.ne',
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    refine (norm_sum_le _ _).trans (le_trans
      (b := ∑ P ∈ (Finset.univ : Finset (P₀.primesOver (𝓞 K))).filter
        (fun P ↦ P.val.inertiaDeg ℤ ∣ k), (P.val.inertiaDeg ℤ : ℝ) * Real.log (p : ℝ))
      (Finset.sum_le_sum ?_) ?_)
    · intro P hP
      have hpow := isPrimePow_primeOverNonZero_pow P
        (div_inertiaDeg_pos P hk (Finset.mem_filter.mp hP).2)
      have hnon : 0 ≤ (P.val.inertiaDeg ℤ : ℝ) * Real.log (p : ℝ) := by positivity
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hN P, abs_of_nonneg hnon]
      exact mul_le_of_le_one_left hnon (hf _ hpow)
    · -- Add the other primes over `p` and insert their ramification indices.
      calc
        _ ≤ ∑ P : P₀.primesOver (𝓞 K), (P.val.inertiaDeg ℤ : ℝ) * Real.log (p : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun P _ _ ↦ by positivity)
        _ ≤ ∑ P : P₀.primesOver (𝓞 K),
            ((P.val.ramificationIdx ℤ * P.val.inertiaDeg ℤ : ℕ) : ℝ) * Real.log (p : ℝ) := by
          refine Finset.sum_le_sum fun P _ ↦ mul_le_mul_of_nonneg_right ?_ hlog
          exact_mod_cast Nat.le_mul_of_pos_left _ (Ideal.ramificationIdx_pos ℤ P.val)
        _ = _ := by
          rw [← Finset.sum_mul, ← Nat.cast_sum, Ideal.sum_ramification_inertia_eq_finrank,
            NumberField.RingOfIntegers.rank K]
  · rw [f.normCoeff_vonMangoldtTransform_eq_zero_of_not_isPrimePow hn, norm_zero]
    exact mul_nonneg (by positivity) vonMangoldt_nonneg

/-- The partial sums of the regrouped von Mangoldt transform of an ideal weight bounded by one
on prime powers are bounded in norm by the field degree times the rational Chebyshev function. -/
theorem norm_sum_normCoeff_vonMangoldtTransform_le (f : IdealArithmeticFunction K)
    (hf : ∀ A : (Ideal (𝓞 K))⁰, IsPrimePow (A : Ideal (𝓞 K)) → ‖f A‖ ≤ 1) (x : ℝ) :
    ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, normCoeff K f.vonMangoldtTransform n‖ ≤
      (Module.finrank ℚ K : ℝ) * Chebyshev.psi x := by
  rw [Chebyshev.psi, Finset.mul_sum, ← Finset.Icc_add_one_left_eq_Ioc]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ ↦
    f.norm_normCoeff_vonMangoldtTransform_le hf n)

end TauCeti.IdealArithmeticFunction

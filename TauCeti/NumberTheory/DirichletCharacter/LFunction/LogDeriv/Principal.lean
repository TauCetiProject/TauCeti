/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv
public import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.Basic
import Mathlib.Tactic.Linarith
import TauCeti.Analysis.SpecialFunctions.Pow.EulerFactor

/-!
# Exact higher-prime-power remainders for principal characters

Principal characters retain the higher prime powers away from the level's prime divisors.
The complex logarithmic derivative differs from zeta's by the sum of the deleted Euler-factor
logarithmic derivatives throughout `1 ≤ re s`, away from `s = 1`. On the real axis, the
higher-prime-power remainder has a finite correction bounded by one absolute geometric majorant,
independently of the level.
-/

public section

open Complex DirichletCharacter ArithmeticFunction LSeries Filter Topology

namespace TauCeti

/-- Changing the principal character's level adds precisely the logarithmic derivatives of
its finitely many deleted Euler factors on `1 ≤ re s`, away from the pole `s = 1`. -/
theorem logDeriv_LFunctionTrivChar_sub_logDeriv_riemannZeta (N : ℕ) [NeZero N]
    {s : ℂ} (hσ : 1 ≤ s.re) (hs1 : s ≠ 1) :
    logDeriv (LFunctionTrivChar N) s - logDeriv riemannZeta s =
      ∑ p ∈ N.primeFactors, (Real.log p : ℂ) / ((p : ℂ) ^ s - 1) := by
  let f (p : ℕ) (z : ℂ) := 1 - (p : ℂ) ^ (-z)
  let P (z : ℂ) := ∏ p ∈ N.primeFactors, f p z
  have heq : LFunctionTrivChar N =ᶠ[𝓝 s] P * riemannZeta := by
    filter_upwards [eventually_ne_nhds hs1] with z hz
    simpa only [P, f, Pi.mul_apply] using LFunctionTrivChar_eq_mul_riemannZeta (N := N) hz
  have hL : LFunctionTrivChar N s ≠ 0 :=
    LFunction_ne_zero_of_one_le_re 1 (.inr hs1) hσ
  have hPζ : P s * riemannZeta s ≠ 0 := by
    intro hz
    exact hL (heq.eq_of_nhds.trans hz)
  have hP := (mul_ne_zero_iff.mp hPζ).1
  have hζ := (mul_ne_zero_iff.mp hPζ).2
  have hdf (p : ℕ) (hp : p ∈ N.primeFactors) : DifferentiableAt ℂ (f p) s := by
    have : NeZero p := ⟨(Nat.pos_of_mem_primeFactors hp).ne'⟩
    dsimp only [f]
    fun_prop
  have hf0 (p : ℕ) (hp : p ∈ N.primeFactors) : f p s ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hP p hp
  have hd := (logDeriv_congr_nhds heq).eq_of_nhds
  rw [logDeriv_mul _ hP hζ (DifferentiableAt.fun_finsetProd hdf)
    (differentiableAt_riemannZeta hs1), logDeriv_fun_prod hf0 hdf] at hd
  rw [hd, add_sub_cancel_right]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  dsimp only [f]
  rw [Complex.logDeriv_one_sub_cpow_neg]
  congr 1
  exact (Complex.ofReal_log p.cast_nonneg).symm

private theorem re_logDeriv_LFunctionTrivChar_sub (N : ℕ) [NeZero N]
    {σ : ℝ} (hσ : 1 < σ) :
    (logDeriv (LFunctionTrivChar N) (σ : ℂ)).re - (logDeriv riemannZeta (σ : ℂ)).re =
      ∑ p ∈ N.primeFactors, Real.log p / ((p : ℝ) ^ σ - 1) := by
  have h := congrArg Complex.re
    (logDeriv_LFunctionTrivChar_sub_logDeriv_riemannZeta N (s := (σ : ℂ))
      (by simpa only [Complex.ofReal_re] using hσ.le) (by exact_mod_cast hσ.ne'))
  simp only [Complex.sub_re, Complex.re_sum] at h
  rw [h]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_mem_primeFactors hp
  have he := Complex.re_logDeriv_one_sub_ofReal_cpow_neg hp0.le σ
  rw [Complex.logDeriv_one_sub_cpow_neg] at he
  simpa only [Complex.ofReal_natCast, Complex.ofReal_log hp0.le] using he

private theorem tsum_prime_principal_sub (N : ℕ) [NeZero N] {σ : ℝ} (hσ : 1 < σ) :
    (∑' p : Nat.Primes, ((1 : DirichletCharacter ℂ N) p).re * Real.log p / (p : ℝ) ^ σ) -
      (∑' p : Nat.Primes, Real.log p / (p : ℝ) ^ σ) =
        -∑ p ∈ N.primeFactors, Real.log p / (p : ℝ) ^ σ := by
  have hs := (1 : DirichletCharacter ℂ N).summable_prime_re_mul_log_div_rpow hσ
  have ht : Summable fun p : Nat.Primes ↦ Real.log p / (p : ℝ) ^ σ := by
    simpa only [MulChar.one_apply (isUnit_of_subsingleton _), Complex.one_re, one_mul] using
      (1 : DirichletCharacter ℂ 1).summable_prime_re_mul_log_div_rpow hσ
  rw [← hs.tsum_sub ht]
  have hv (p : Nat.Primes) :
      ((1 : DirichletCharacter ℂ N) p).re * Real.log p / (p : ℝ) ^ σ -
        Real.log p / (p : ℝ) ^ σ =
          if (p : ℕ) ∣ N then -(Real.log p / (p : ℝ) ^ σ) else 0 := by
    split_ifs with hp
    · rw [MulChar.map_nonunit 1 ((ZMod.isUnit_prime_iff_not_dvd p.prop).not.mpr
        (not_not.mpr hp))]
      simp
    · rw [MulChar.one_apply (ZMod.isUnit_prime_of_not_dvd p.prop hp)]
      simp
  simp_rw [hv]
  have hfinite : (∑' p : Nat.Primes,
      if (p : ℕ) ∣ N then -(Real.log p / (p : ℝ) ^ σ) else 0) =
        ∑ p ∈ (N.primeFactors.subtype Nat.Prime : Finset Nat.Primes),
          if (p : ℕ) ∣ N then -(Real.log p / (p : ℝ) ^ σ) else 0 := by
    apply tsum_eq_sum
    intro p hp
    have hnd : ¬(p : ℕ) ∣ N := by
      have hp' : (⟨p.val, p.prop⟩ : {n : ℕ // n.Prime}) ∉
          N.primeFactors.subtype Nat.Prime := hp
      intro hd
      exact hp' (Finset.mem_subtype.mpr (Nat.mem_primeFactors.mpr
        ⟨p.prop, hd, NeZero.ne N⟩))
    simp only [hnd, ↓reduceIte]
  rw [hfinite]
  -- Nat.Primes is definitionally the prime subtype. Expose that subtype explicitly so the
  -- finite-sum lemma can infer its natural-number summand across module boundaries.
  change (∑ p ∈ N.primeFactors.subtype Nat.Prime,
    if p.val ∣ N then -(Real.log p.val / (p.val : ℝ) ^ σ) else 0) = _
  rw [Finset.sum_subtype_of_mem
    (fun p : ℕ ↦ if p ∣ N then -(Real.log p / (p : ℝ) ^ σ) else 0)
    (fun p hp ↦ Nat.prime_of_mem_primeFactors hp)]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun p hp ↦ ite_eq_left (Nat.dvd_of_mem_primeFactors hp)

/-- Raising the principal character's level deletes exactly the higher powers of its prime
factors from the logarithmic-derivative remainder. -/
theorem neg_re_logDeriv_LFunctionTrivChar_remainder_sub_eq (N : ℕ) [NeZero N]
    {σ : ℝ} (hσ : 1 < σ) :
    (-(logDeriv (LFunctionTrivChar N) (σ : ℂ)).re -
        ∑' p : Nat.Primes, ((1 : DirichletCharacter ℂ N) p).re * Real.log p / (p : ℝ) ^ σ) -
      (-(logDeriv riemannZeta (σ : ℂ)).re -
        ∑' p : Nat.Primes, Real.log p / (p : ℝ) ^ σ) =
      -∑ p ∈ N.primeFactors, Real.log p / ((p : ℝ) ^ σ * ((p : ℝ) ^ σ - 1)) := by
  have hd := re_logDeriv_LFunctionTrivChar_sub N hσ
  have hp := tsum_prime_principal_sub N hσ
  have hf : (∑ p ∈ N.primeFactors, Real.log p / ((p : ℝ) ^ σ - 1)) -
      (∑ p ∈ N.primeFactors, Real.log p / (p : ℝ) ^ σ) =
      ∑ p ∈ N.primeFactors, Real.log p / ((p : ℝ) ^ σ * ((p : ℝ) ^ σ - 1)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    have hpow : 1 < (p : ℝ) ^ σ := Real.one_lt_rpow
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt) (zero_lt_one.trans hσ)
    field_simp [ne_of_gt (zero_lt_one.trans hpow), sub_ne_zero.mpr hpow.ne']
    ring
  linarith

/-- The finite principal-character correction is at most the endpoint geometric majorant,
independently of the level and of the real argument greater than one. -/
theorem abs_neg_re_logDeriv_LFunctionTrivChar_remainder_sub_le (N : ℕ) [NeZero N]
    {σ : ℝ} (hσ : 1 < σ) :
    |(-(logDeriv (LFunctionTrivChar N) (σ : ℂ)).re -
        ∑' p : Nat.Primes, ((1 : DirichletCharacter ℂ N) p).re * Real.log p / (p : ℝ) ^ σ) -
      (-(logDeriv riemannZeta (σ : ℂ)).re -
        ∑' p : Nat.Primes, Real.log p / (p : ℝ) ^ σ)| ≤
      ∑' p : Nat.Primes, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
  rw [neg_re_logDeriv_LFunctionTrivChar_remainder_sub_eq N hσ, abs_neg, abs_of_nonneg]
  · exact N.sum_primeFactors_log_div_rpow_mul_sub_one_le hσ.le
  · refine Finset.sum_nonneg fun p hp ↦ div_nonneg ?_ ?_
    · exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
    · exact mul_nonneg (Real.rpow_nonneg p.cast_nonneg _) (sub_nonneg.mpr
        (Real.one_le_rpow (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
          (zero_lt_one.trans hσ).le))

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.Analysis.Calculus.LogDeriv
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Basic
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.NearOne
import Mathlib.Tactic.Linarith
import TauCeti.Analysis.SpecialFunctions.Pow.EulerFactor

/-!
# Exact higher-prime-power remainders and pole bounds for principal characters

Principal characters retain the higher prime powers away from the level's prime divisors.
The complex logarithmic derivative differs from zeta's by the sum of the deleted Euler-factor
logarithmic derivatives wherever the principal L-function is nonzero, away from `s = 1`.
On `1 ≤ Re s`, `-Re L'/L(s, χ₀) ≤ -Re ζ'/ζ(s) + log N` away from `s = 1`, and on the real
half-line `(1, 2]` this gives `1 / η + C + log N`.
On the real axis, the higher-prime-power remainder has a finite correction bounded by one
absolute geometric majorant, independently of the level.
-/

public section

open Complex DirichletCharacter ArithmeticFunction LSeries Filter Topology

namespace Nat

/-- Changing the principal character's level adds precisely the logarithmic derivatives of
its finitely many deleted Euler factors wherever it is nonzero, away from the pole `s = 1`. -/
theorem logDeriv_LFunctionTrivChar_sub_logDeriv_riemannZeta (N : ℕ) [NeZero N]
    {s : ℂ} (hL : LFunctionTrivChar N s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv (LFunctionTrivChar N) s - logDeriv riemannZeta s =
      ∑ p ∈ N.primeFactors, (Real.log p : ℂ) / ((p : ℂ) ^ s - 1) := by
  have h := logDeriv_LFunction_changeLevel_sub (1 : DirichletCharacter ℂ 1) N.one_dvd
    (by rwa [changeLevel_one]) (.inr hs1)
  rw [changeLevel_one, LFunction_modOne_eq] at h
  rw [h]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have h1 : (1 : DirichletCharacter ℂ 1) p = 1 := MulChar.one_apply (isUnit_of_subsingleton _)
  simp only [h1, one_mul]
  rw [Complex.logDeriv_one_sub_cpow_neg]
  congr 1
  exact (Complex.ofReal_log p.cast_nonneg).symm

private theorem re_logDeriv_LFunctionTrivChar_sub (N : ℕ) [NeZero N]
    {σ : ℝ} (hσ : 1 < σ) :
    (logDeriv (LFunctionTrivChar N) (σ : ℂ)).re - (logDeriv riemannZeta (σ : ℂ)).re =
      ∑ p ∈ N.primeFactors, Real.log p / ((p : ℝ) ^ σ - 1) := by
  have h := congrArg Complex.re
    (logDeriv_LFunctionTrivChar_sub_logDeriv_riemannZeta N (s := (σ : ℂ))
      (LFunction_ne_zero_of_one_le_re 1 (.inr (by exact_mod_cast hσ.ne'))
        (by simpa only [Complex.ofReal_re] using hσ.le)) (by exact_mod_cast hσ.ne'))
  simp only [Complex.sub_re, Complex.re_sum] at h
  rw [h]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_mem_primeFactors hp
  have he := Complex.re_logDeriv_one_sub_ofReal_cpow_neg hp0.le σ
  rw [Complex.logDeriv_one_sub_cpow_neg] at he
  simpa only [Complex.ofReal_natCast, Complex.ofReal_log hp0.le] using he

/-- For a nonzero level, the principal character deletes exactly the weights at its prime
factors from any summable real prime series. No sign condition on the weights is needed. -/
theorem tsum_prime_re_one_mul_sub_tsum_prime_eq_neg_sum_primeFactors (N : ℕ) [NeZero N]
    (w : ℕ → ℝ)
    (hw : Summable fun p : Nat.Primes ↦ w p) :
    (∑' p : Nat.Primes, ((1 : DirichletCharacter ℂ N) p).re * w p) -
      (∑' p : Nat.Primes, w p) = -∑ p ∈ N.primeFactors, w p := by
  classical
  have hc (p : Nat.Primes) : ((1 : DirichletCharacter ℂ N) p).re =
      if (p : ℕ) ∣ N then 0 else 1 := by
    split_ifs with hp
    · rw [MulChar.map_nonunit 1 ((ZMod.isUnit_prime_iff_not_dvd p.prop).not.mpr
        (not_not.mpr hp))]
      simp
    · rw [MulChar.one_apply (ZMod.isUnit_prime_of_not_dvd p.prop hp)]
      simp
  have hs : Summable fun p : Nat.Primes ↦ ((1 : DirichletCharacter ℂ N) p).re * w p := by
    apply (hw.indicator {p : Nat.Primes | ¬ (p : ℕ) ∣ N}).congr
    exact fun p ↦ by simp [Set.indicator, hc]
  rw [← hs.tsum_sub hw]
  have hv (p : Nat.Primes) :
      ((1 : DirichletCharacter ℂ N) p).re * w p -
        w p =
          if (p : ℕ) ∣ N then -(w p) else 0 := by
    simp only [hc, ite_mul, zero_mul, one_mul]
    split_ifs <;> ring
  simp_rw [hv]
  have hfinite : (∑' p : Nat.Primes,
      if (p : ℕ) ∣ N then -(w p) else 0) =
        ∑ p ∈ (N.primeFactors.subtype Nat.Prime : Finset Nat.Primes),
          if (p : ℕ) ∣ N then -(w p) else 0 := by
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
    if p.val ∣ N then -(w p.val) else 0) = _
  rw [Finset.sum_subtype_of_mem
    (fun p : ℕ ↦ if p ∣ N then -(w p) else 0)
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
  have hw : Summable fun p : Nat.Primes ↦ Real.log p / (p : ℝ) ^ σ := by
    simpa only [MulChar.one_apply (isUnit_of_subsingleton _), Complex.one_re, one_mul] using
      (1 : DirichletCharacter ℂ 1).summable_prime_re_mul_log_div_rpow hσ
  have hp := N.tsum_prime_re_one_mul_sub_tsum_prime_eq_neg_sum_primeFactors
    (fun p ↦ Real.log p / (p : ℝ) ^ σ) hw
  simp only [← mul_div_assoc] at hp
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

end Nat

namespace DirichletCharacter

/-- Away from `s = 1`, on the half-plane `1 ≤ Re s`, raising the principal character's level from
`1` to `N` increases `-Re L'/L(s, χ₀)` by at most `log N`. -/
theorem neg_re_logDeriv_LFunctionTrivChar_le_neg_re_logDeriv_riemannZeta_add (N : ℕ) [NeZero N]
    {s : ℂ} (hs : 1 ≤ s.re) (hs1 : s ≠ 1) :
    -(logDeriv (LFunctionTrivChar N) s).re ≤ -(logDeriv riemannZeta s).re + Real.log N := by
  have hch := norm_logDeriv_LFunction_changeLevel_sub_le (1 : DirichletCharacter ℂ 1) N.one_dvd
    hs (.inr hs1)
  rw [changeLevel_one, LFunction_modOne_eq, norm_sub_rev] at hch
  have hre := (Complex.re_le_norm _).trans hch
  rw [Complex.sub_re] at hre
  dsimp only [LFunctionTrivChar]
  linarith

/-- One positive absolute constant `C` satisfies
`-(logDeriv (LFunctionTrivChar N) (1 + η)).re ≤ 1 / η + C + Real.log N` for every positive level
`N` and every `0 < η ≤ 1`. -/
theorem exists_neg_re_logDeriv_LFunctionTrivChar_one_add_le :
    ∃ C > 0, ∀ (N : ℕ) [NeZero N] {η : ℝ}, 0 < η → η ≤ 1 →
      -(logDeriv (LFunctionTrivChar N) (1 + η)).re ≤ 1 / η + C + Real.log N := by
  obtain ⟨C, hC0, hC⟩ := TauCeti.exists_neg_re_logDeriv_riemannZeta_one_add_le
  refine ⟨C, hC0, fun N _ η hη hη1 ↦ ?_⟩
  have hne1 : (1 : ℂ) + η ≠ 1 := by simpa using hη.ne'
  have hs1 : (1 : ℝ) ≤ ((1 : ℂ) + η).re := by simp [hη.le]
  linarith [neg_re_logDeriv_LFunctionTrivChar_le_neg_re_logDeriv_riemannZeta_add N hs1 hne1,
    hC η hη hη1]

end DirichletCharacter

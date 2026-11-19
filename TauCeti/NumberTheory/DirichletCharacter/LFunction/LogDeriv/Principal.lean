/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv
public import TauCeti.NumberTheory.ArithmeticFunction.VonMangoldt.PrimePowers
import Mathlib.Tactic.Linarith
import TauCeti.Analysis.SpecialFunctions.Pow.EulerFactor

/-!
# Exact higher-prime-power remainders for principal characters

Principal characters retain the higher prime powers away from the level's prime divisors.
Deleting the finitely many ramified factors gives a correction bounded by one absolute
geometric majorant, independently of the level.
-/

public section

open Complex DirichletCharacter ArithmeticFunction LSeries Filter Topology

namespace TauCeti

private theorem re_logDeriv_prime_eulerFactor (p : Nat.Primes) (σ : ℝ) :
    (logDeriv (fun z : ℂ ↦ 1 - (p : ℂ) ^ (-z)) (σ : ℂ)).re =
      Real.log p / ((p : ℝ) ^ σ - 1) := by
  have hd : logDeriv (fun z : ℂ ↦ 1 - (p : ℂ) ^ (-z)) (σ : ℂ) =
      (p : ℂ) ^ (-(σ : ℂ)) * Complex.log p / (1 - (p : ℂ) ^ (-(σ : ℂ))) := by
    simpa only [one_mul] using Complex.logDeriv_one_sub_mul_cpow_neg
      (Nat.cast_ne_zero.mpr p.prop.ne_zero) 1 (σ : ℂ)
  rw [hd]
  rw [← Complex.ofReal_natCast p.val, ← Complex.ofReal_neg,
    ← Complex.ofReal_cpow p.val.cast_nonneg, ← Complex.ofReal_log p.val.cast_nonneg,
    ← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    ← Complex.ofReal_div, Complex.ofReal_re, Real.rpow_neg p.val.cast_nonneg]
  by_cases hpow : (p : ℝ) ^ σ = 1
  · simp only [hpow, inv_one, sub_self, div_zero]
  · have hp0 : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
    have hr0 : (p : ℝ) ^ σ ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hp0 σ)
    field_simp [hr0, sub_ne_zero.mpr hpow]

private theorem re_logDeriv_principal_sub (N : ℕ) [NeZero N] {σ : ℝ} (hσ : 1 < σ) :
    (logDeriv (LFunctionTrivChar N) (σ : ℂ)).re - (logDeriv riemannZeta (σ : ℂ)).re =
      ∑ p ∈ N.primeFactors, Real.log p / ((p : ℝ) ^ σ - 1) := by
  let f (p : ℕ) (z : ℂ) := 1 - (p : ℂ) ^ (-z)
  let P (z : ℂ) := ∏ p ∈ N.primeFactors, f p z
  have hs1 : (σ : ℂ) ≠ 1 := by exact_mod_cast ne_of_gt hσ
  have heq : LFunctionTrivChar N =ᶠ[𝓝 (σ : ℂ)] P * riemannZeta := by
    filter_upwards [eventually_ne_nhds hs1] with z hz
    simpa only [P, f, Pi.mul_apply] using LFunctionTrivChar_eq_mul_riemannZeta (N := N) hz
  have hL : LFunctionTrivChar N (σ : ℂ) ≠ 0 :=
    LFunction_ne_zero_of_one_le_re 1 (.inr hs1) (by simpa using hσ.le)
  have hPζ : P (σ : ℂ) * riemannZeta (σ : ℂ) ≠ 0 := by
    intro hz
    exact hL (heq.eq_of_nhds.trans hz)
  have hP := (mul_ne_zero_iff.mp hPζ).1
  have hζ := (mul_ne_zero_iff.mp hPζ).2
  have hdf (p : ℕ) (hp : p ∈ N.primeFactors) : DifferentiableAt ℂ (f p) (σ : ℂ) := by
    have : NeZero p := ⟨(Nat.pos_of_mem_primeFactors hp).ne'⟩
    dsimp only [f]
    fun_prop
  have hf0 (p : ℕ) (hp : p ∈ N.primeFactors) : f p (σ : ℂ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hP p hp
  have hd := (logDeriv_congr_nhds heq).eq_of_nhds
  rw [logDeriv_mul _ hP hζ (DifferentiableAt.fun_finsetProd hdf)
    (differentiableAt_riemannZeta hs1), logDeriv_fun_prod hf0 hdf] at hd
  have hr := congrArg Complex.re hd
  simp only [Complex.add_re, Complex.re_sum] at hr
  rw [hr, add_sub_cancel_right]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  exact re_logDeriv_prime_eulerFactor ⟨p, Nat.prime_of_mem_primeFactors hp⟩ σ

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

/-- The difference between minus zeta's logarithmic derivative and its prime sum is the
exact geometric higher-prime-power tail. -/
theorem neg_re_logDeriv_riemannZeta_sub_tsum_prime_eq {σ : ℝ} (hσ : 1 < σ) :
    -(logDeriv riemannZeta (σ : ℂ)).re - ∑' p : Nat.Primes, Real.log p / (p : ℝ) ^ σ =
      ∑' p : Nat.Primes, Real.log p / ((p : ℝ) ^ σ * ((p : ℝ) ^ σ - 1)) := by
  have h := (1 : DirichletCharacter ℂ 1).logDeriv_LFunction_add_tsum_prime_eq
    (s := (σ : ℂ)) (by simpa)
  have hχ (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 :=
    MulChar.one_apply (isUnit_of_subsingleton _)
  rw [DirichletCharacter.LFunction_modOne_eq] at h
  simp only [hχ, one_mul] at h
  have hs0 : (σ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (zero_lt_one.trans hσ)
  have hpow (n : ℕ) : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_cpow n.cast_nonneg σ).symm
  simp only [term_of_ne_zero' hs0, Pi.mul_apply, one_mul, hpow, ← Complex.ofReal_div] at h
  have hif (n : ℕ) :
      (if n.Prime then (0 : ℂ) else ((vonMangoldt n / (n : ℝ) ^ σ : ℝ) : ℂ)) =
        (((if n.Prime then 0 else vonMangoldt n) / (n : ℝ) ^ σ : ℝ) : ℂ) := by
    split_ifs <;> simp_all
  simp only [hif, ← Complex.ofReal_tsum] at h
  have hr := congrArg Complex.re h
  simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re] at hr
  linarith [(vonMangoldt.hasSum_prime_log_div_rpow_mul_sub_one hσ.le).tsum_eq]

private theorem sum_primeFactors_geometric_le (N : ℕ) {σ : ℝ} (hσ : 1 ≤ σ) :
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
  have hg := vonMangoldt.hasSum_prime_log_div_rpow_mul_sub_one (σ := 1) le_rfl
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

/-- Raising the principal character's level deletes exactly the higher powers of its prime
factors from the logarithmic-derivative remainder. -/
theorem neg_re_logDeriv_principal_remainder_sub_eq (N : ℕ) [NeZero N]
    {σ : ℝ} (hσ : 1 < σ) :
    (-(logDeriv (LFunctionTrivChar N) (σ : ℂ)).re -
        ∑' p : Nat.Primes, ((1 : DirichletCharacter ℂ N) p).re * Real.log p / (p : ℝ) ^ σ) -
      (-(logDeriv riemannZeta (σ : ℂ)).re -
        ∑' p : Nat.Primes, Real.log p / (p : ℝ) ^ σ) =
      -∑ p ∈ N.primeFactors, Real.log p / ((p : ℝ) ^ σ * ((p : ℝ) ^ σ - 1)) := by
  have hd := re_logDeriv_principal_sub N hσ
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
theorem abs_neg_re_logDeriv_principal_remainder_sub_le (N : ℕ) [NeZero N]
    {σ : ℝ} (hσ : 1 < σ) :
    |(-(logDeriv (LFunctionTrivChar N) (σ : ℂ)).re -
        ∑' p : Nat.Primes, ((1 : DirichletCharacter ℂ N) p).re * Real.log p / (p : ℝ) ^ σ) -
      (-(logDeriv riemannZeta (σ : ℂ)).re -
        ∑' p : Nat.Primes, Real.log p / (p : ℝ) ^ σ)| ≤
      ∑' p : Nat.Primes, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
  rw [neg_re_logDeriv_principal_remainder_sub_eq N hσ, abs_neg, abs_of_nonneg]
  · exact sum_primeFactors_geometric_le N hσ.le
  · refine Finset.sum_nonneg fun p hp ↦ div_nonneg ?_ ?_
    · exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
    · exact mul_nonneg (Real.rpow_nonneg p.cast_nonneg _) (sub_nonneg.mpr
        (Real.one_le_rpow (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
          (zero_lt_one.trans hσ).le))

end TauCeti

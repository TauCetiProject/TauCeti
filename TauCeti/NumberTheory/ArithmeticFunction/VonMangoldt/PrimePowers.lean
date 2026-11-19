/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# Exact geometric sums for the higher prime powers

Regrouping the nonprime von Mangoldt series by its prime base gives a geometric prime sum.
The endpoint exponent one is included and supplies the conductor-independent majorant.
-/

public section

open ArithmeticFunction

namespace ArithmeticFunction.vonMangoldt

/-- The nonprime von Mangoldt series remains summable for every real exponent at least one. -/
theorem summable_nonprime_div_rpow {σ : ℝ} (hσ : 1 ≤ σ) :
    Summable fun n : ℕ ↦ (if n.Prime then 0 else vonMangoldt n) / (n : ℝ) ^ σ := by
  refine summable_nonprime_div.of_nonneg_of_le (fun n ↦ ?_) (fun n ↦ ?_)
  · exact div_nonneg (ite_nonneg le_rfl vonMangoldt_nonneg) (Real.rpow_nonneg n.cast_nonneg _)
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      exact div_le_div_of_nonneg_left (ite_nonneg le_rfl vonMangoldt_nonneg)
        (by exact_mod_cast Nat.pos_of_ne_zero hn)
        (by simpa using Real.rpow_le_rpow_of_exponent_le hn1 hσ)

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

/-- Regrouping by the prime base evaluates the higher powers as a geometric prime series. -/
theorem hasSum_prime_log_div_rpow_mul_sub_one {σ : ℝ} (hσ : 1 ≤ σ) :
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
    (fun p ↦ hasSum_nonprime_prime_pow_div_rpow p (zero_lt_one.trans_le hσ))
  have hzero (p : Nat.Primes) : f p = 0 := by simp [f, p.prop]
  have hsplit : (∑' n, f n) = ∑' (p : Nat.Primes) (k : ℕ), f (p ^ (k + 2)) := by
    simpa only [hzero, tsum_zero, zero_add] using
      tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers hf hsupp
  simpa only [hprod.tsum_prod, ← hsplit] using hg

end ArithmeticFunction.vonMangoldt

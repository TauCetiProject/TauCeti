/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Log
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Prime.Int

/-!
# Finite sums over prime powers

A finite sum `∑ n ∈ Icc 1 N, f n` of a function supported on the prime powers can be regrouped
by the prime base: the prime powers `p ^ k ≤ N` with `k ≥ 1` are exactly the pairs of a prime
`p ≤ N` and an exponent `1 ≤ k ≤ Nat.log p N`. This is the finite cutoff identity used to compare
partial sums of a Dirichlet series supported on prime powers with finite products over primes.

For each prime `p ≤ N`, the first omitted power `p ^ (Nat.log p N + 1)` exceeds `N`. Splitting
the primes `p ≤ N` at `√N` bounds the sum of their reciprocals by `3 / √N`; in particular, it
tends to zero as `N → ∞`, controlling the tails left out by the regrouping.

## Main results

* `Nat.sum_Icc_eq_sum_primesLE_sum_Icc_log`: the regrouping of a finite sum of a function
  supported on the prime powers.
* `Nat.sum_primesLE_inv_pow_log_succ_le`: `∑ p ≤ N, 1 / p ^ (Nat.log p N + 1) ≤ 3 / √N`.
* `Nat.tendsto_sum_primesLE_inv_pow_log_succ`: `∑ p ≤ N, 1 / p ^ (Nat.log p N + 1)` tends to `0`.

## References

The proof adapts the regrouping step of Mathlib's `Chebyshev.psi_eq_sum_mul_log_prime`, which
carries it out for the von Mangoldt function.
-/

public section

open Filter Finset
open scoped Topology

namespace Nat

/-- A finite sum of a function supported on the prime powers, regrouped by the prime base: the
terms `f n` with `1 ≤ n ≤ N` are the terms `f (p ^ k)` with `p ≤ N` prime and
`1 ≤ k ≤ Nat.log p N`. -/
theorem sum_Icc_eq_sum_primesLE_sum_Icc_log {M : Type*} [AddCommMonoid M] {f : ℕ → M}
    (hf : ∀ n, ¬IsPrimePow n → f n = 0) (N : ℕ) :
    ∑ n ∈ Icc 1 N, f n = ∑ p ∈ primesLE N, ∑ k ∈ Icc 1 (p.log N), f (p ^ k) := calc
  _ = ∑ n ∈ (primesLE N).biUnion fun p ↦ image (p ^ ·) (Icc 1 (p.log N)), f n := by
    refine (sum_subset (fun q hq ↦ ?_) fun n hn hn' ↦ hf n ?_).symm
    · simp only [mem_biUnion, mem_primesLE, mem_image, mem_Icc] at hq ⊢
      obtain ⟨p, ⟨-, hp⟩, k, ⟨hk, hkN⟩, rfl⟩ := hq
      exact ⟨one_le_pow _ _ hp.pos, pow_le_of_le_log (by rintro rfl; simp at hkN; lia) hkN⟩
    · rintro ⟨p, k, hp, hk, rfl⟩
      rw [Nat.prime_iff.symm] at hp
      simp only [mem_Icc] at hn
      refine hn' (mem_biUnion.mpr ⟨p, mem_primesLE.mpr ⟨?_, hp⟩, mem_image.mpr ⟨k, ?_, rfl⟩⟩)
      · exact (le_of_dvd (by lia) (dvd_pow_self p hk.ne')).trans hn.2
      · exact mem_Icc.mpr ⟨hk, le_log_of_pow_le hp.one_lt hn.2⟩
  _ = ∑ p ∈ primesLE N, ∑ n ∈ image (p ^ ·) (Icc 1 (p.log N)), f n := by
    rw [sum_biUnion]
    intro p hp q hq hpq
    simp only [Function.onFun, disjoint_left, mem_image, mem_Icc]
    rintro _ ⟨k, ⟨hk, -⟩, rfl⟩ ⟨l, ⟨hl, -⟩, h⟩
    exact hpq ((prime_of_mem_primesLE hq).pow_inj' (prime_of_mem_primesLE hp) (by lia) (by lia)
      h).1.symm
  _ = _ := sum_congr rfl fun p hp ↦
    sum_image fun _ _ _ _ h ↦ Nat.pow_right_injective (two_le_of_mem_primesLE hp) h

private theorem sum_Ioc_inv_sq_le_inv {M N : ℕ} (hM : 1 ≤ M) :
    ∑ k ∈ Ioc M N, ((k : ℝ) ^ 2)⁻¹ ≤ (M : ℝ)⁻¹ := by
  rcases le_or_gt M N with hMN | hNM
  · have himg : Ioc M N = (Ico M N).image (· + 1) := by
      ext k
      simp only [mem_Ioc, mem_image, mem_Ico]
      exact ⟨fun hk ↦ ⟨k - 1, by lia, by lia⟩, fun ⟨i, hi, hk⟩ ↦ by lia⟩
    have hle : ∑ k ∈ Ioc M N, ((k : ℝ) ^ 2)⁻¹ ≤
        ∑ i ∈ Ico M N, (-(((i + 1 : ℕ) : ℝ)⁻¹) - -(i : ℝ)⁻¹) := by
      rw [himg, sum_image fun _ _ _ _ h ↦ Nat.succ.inj h]
      refine sum_le_sum fun i hi ↦ ?_
      have hiM : 1 ≤ i := hM.trans (mem_Ico.mp hi).1
      have hi0 : (0 : ℝ) < i := mod_cast hiM
      have hi1 : (0 : ℝ) < (i + 1 : ℕ) := by positivity
      rw [sub_neg_eq_add, add_comm, ← sub_eq_add_neg, inv_sub_inv hi0.ne' hi1.ne', Nat.cast_add,
        Nat.cast_one, add_sub_cancel_left, one_div]
      exact inv_anti₀ (mul_pos hi0 (by positivity)) (by push_cast; nlinarith)
    rw [sum_Ico_sub (f := fun i : ℕ ↦ -(i : ℝ)⁻¹) hMN] at hle
    linarith [inv_nonneg.mpr (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  · rw [Ioc_eq_empty_of_le hNM.le, sum_empty]
    positivity

/-- **Quantitative bound on the omitted prime-power reciprocals.** Splitting `p ≤ N` at `√N`,
each prime `p ≤ √N` contributes less than `1 / N` (for `1 / √N` in total), while each prime
`p > √N` has `Nat.log p N + 1 ≥ 2` and contributes at most `1 / p ^ 2` (for `2 / √N` in total). -/
theorem sum_primesLE_inv_pow_log_succ_le (N : ℕ) :
    ∑ p ∈ primesLE N, ((p : ℝ) ^ (p.log N + 1))⁻¹ ≤ 3 / √(N : ℝ) := by
  rcases eq_or_ne N 0 with rfl | hN0
  · simp [primesLE]
  have hN1 : 1 ≤ N := Nat.pos_of_ne_zero hN0
  set M := N.sqrt
  have hM1 : 1 ≤ M := Nat.sqrt_pos.mpr hN1
  have hNpos : (0 : ℝ) < N := mod_cast hN1
  have hsN : (0 : ℝ) < √(N : ℝ) := Real.sqrt_pos.mpr hNpos
  -- Primes `p ≤ M` each contribute at most `1 / N`, and there are at most `M ≤ √N` of them.
  have hsmall : ∑ p ∈ primesLE N with p ≤ M, ((p : ℝ) ^ (p.log N + 1))⁻¹ ≤ 1 / √(N : ℝ) := calc
    _ ≤ ∑ p ∈ primesLE N with p ≤ M, (N : ℝ)⁻¹ := sum_le_sum fun p hp ↦
      inv_anti₀ hNpos (mod_cast (lt_pow_succ_log_self (one_lt_of_mem_primesLE
        (mem_filter.mp hp).1) N).le)
    _ ≤ ∑ _p ∈ Icc 1 M, (N : ℝ)⁻¹ := sum_le_sum_of_subset_of_nonneg
      (fun p hp ↦ mem_Icc.mpr ⟨(prime_of_mem_primesLE (mem_filter.mp hp).1).pos,
        (mem_filter.mp hp).2⟩) fun _ _ _ ↦ by positivity
    _ = (M : ℝ) / N := by simp [Nat.card_Icc, div_eq_mul_inv]
    _ ≤ √(N : ℝ) / (√(N : ℝ) * √(N : ℝ)) := by
      rw [Real.mul_self_sqrt hNpos.le]
      exact div_le_div_of_nonneg_right
        (Real.le_sqrt_of_sq_le (by rw [sq]; exact_mod_cast Nat.sqrt_le N)) hNpos.le
    _ = 1 / √(N : ℝ) := by rw [div_mul_cancel_left₀ hsN.ne', one_div]
  -- Primes `p > M` have exponent `≥ 2`, and `∑_{M < k ≤ N} 1 / k ^ 2 ≤ 1 / M ≤ 2 / √N`.
  have hlarge : ∑ p ∈ primesLE N with ¬p ≤ M, ((p : ℝ) ^ (p.log N + 1))⁻¹ ≤ 2 / √(N : ℝ) := calc
    _ ≤ ∑ p ∈ primesLE N with ¬p ≤ M, ((p : ℝ) ^ 2)⁻¹ := sum_le_sum fun p hp ↦ by
      have hp' := (mem_filter.mp hp).1
      have hp1 := one_lt_of_mem_primesLE hp'
      have hlog : 1 ≤ p.log N := log_pos hp1 (le_of_mem_primesLE hp')
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (mod_cast hp1.le) (by lia))
    _ ≤ ∑ k ∈ Ioc M N, ((k : ℝ) ^ 2)⁻¹ := sum_le_sum_of_subset_of_nonneg
      (fun p hp ↦ mem_Ioc.mpr ⟨not_le.mp (mem_filter.mp hp).2,
        le_of_mem_primesLE (mem_filter.mp hp).1⟩) fun _ _ _ ↦ by positivity
    _ ≤ (M : ℝ)⁻¹ := sum_Ioc_inv_sq_le_inv hM1
    _ ≤ 2 / √(N : ℝ) := by
      have hNle : (N : ℝ) ≤ ((M + 1 : ℕ) : ℝ) ^ 2 := by
        rw [sq]
        exact_mod_cast (lt_succ_sqrt N).le
      have h2M : √(N : ℝ) ≤ 2 * (M : ℝ) := Real.sqrt_le_iff.mpr ⟨by positivity,
        hNle.trans (by push_cast; nlinarith [show (1 : ℝ) ≤ M from mod_cast hM1])⟩
      rw [inv_eq_one_div, div_le_div_iff₀ (mod_cast hM1 : (0 : ℝ) < M) hsN]
      linarith
  rw [← sum_filter_add_sum_filter_not (primesLE N) (· ≤ M)]
  calc _ ≤ 1 / √(N : ℝ) + 2 / √(N : ℝ) := _root_.add_le_add hsmall hlarge
    _ = 3 / √(N : ℝ) := by ring

/-- The reciprocals of the first omitted prime powers `p ^ (Nat.log p N + 1)`, summed over the
primes `p ≤ N`, tend to `0`: each is less than `1 / N`, and they are dominated by the summable
`1 / p ^ 2`. -/
theorem tendsto_sum_primesLE_inv_pow_log_succ :
    Tendsto (fun N : ℕ ↦ ∑ p ∈ primesLE N, ((p : ℝ) ^ (p.log N + 1))⁻¹) atTop (𝓝 0) := by
  set e : ℕ → ℕ → ℝ := fun N p ↦ if p ∈ primesLE N then ((p : ℝ) ^ (p.log N + 1))⁻¹ else 0
  have hsum (N : ℕ) : ∑ p ∈ primesLE N, ((p : ℝ) ^ (p.log N + 1))⁻¹ = ∑' p, e N p := by
    rw [tsum_eq_sum (s := primesLE N) fun p hp ↦ by simp [e, hp]]
    exact sum_congr rfl fun p hp ↦ by simp [e, hp]
  simp_rw [hsum]
  have hzero : (0 : ℝ) = ∑' _ : ℕ, (0 : ℝ) := tsum_zero.symm
  rw [hzero]
  refine tendsto_tsum_of_dominated_convergence (bound := fun p : ℕ ↦ ((p : ℝ) ^ 2)⁻¹)
    (Real.summable_nat_pow_inv.mpr one_lt_two) (fun p ↦ ?_) (Eventually.of_forall fun N p ↦ ?_)
  · -- For fixed `p`, the term is eventually at most `1 / N`, since `N < p ^ (Nat.log p N + 1)`.
    refine squeeze_zero' (Eventually.of_forall fun N ↦ ?_) ?_
      tendsto_inv_atTop_nhds_zero_nat
    · simp only [e]
      split_ifs <;> positivity
    · filter_upwards [eventually_gt_atTop 0] with N hN
      simp only [e]
      split_ifs with hp
      · have h := lt_pow_succ_log_self (one_lt_of_mem_primesLE hp) N
        exact inv_anti₀ (mod_cast hN) (mod_cast h.le)
      · positivity
  · -- For `p ≤ N`, the exponent `Nat.log p N + 1` is at least `2`.
    simp only [e]
    split_ifs with hp
    · have hp1 := one_lt_of_mem_primesLE hp
      have hlog : 1 ≤ p.log N := log_pos hp1 (le_of_mem_primesLE hp)
      rw [norm_inv, norm_pow, Real.norm_natCast]
      exact inv_anti₀ (by positivity)
        (pow_le_pow_right₀ (mod_cast hp1.le) (by lia))
    · simp only [norm_zero]
      positivity

end Nat

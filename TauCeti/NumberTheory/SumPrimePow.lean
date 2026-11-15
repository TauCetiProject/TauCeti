/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Data.Nat.Log
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Prime.Int
import TauCeti.Analysis.SpecificLimits.ReciprocalSeries

/-!
# Finite sums over prime powers

A finite sum `∑ n ∈ Icc 1 N, f n` of a function supported on the prime powers can be regrouped
by the prime base: the prime powers `p ^ k ≤ N` with `k ≥ 1` are exactly the pairs of a prime
`p ≤ N` and an exponent `1 ≤ k ≤ Nat.log p N`. This is the finite cutoff identity used to compare
partial sums of a Dirichlet series supported on prime powers with finite products over primes.

For each prime `p ≤ N`, the first omitted power `p ^ (Nat.log p N + 1)` exceeds `N`. The sum of
their reciprocals over the primes `p ≤ N` tends to zero as `N → ∞`, which controls the tails left
out by the regrouping. Meanwhile, the reciprocals of all higher prime powers `p ^ k` (`k ≥ 2`,
`p ≤ N`) are bounded prime-by-prime by `1 / (p (p - 1))`, whose sum over `p ≤ N` is at most `1` by
telescoping `1 / ((n + 1) (n + 2))`.

## Main results

* `Nat.sum_Icc_ite_pow_le_eq_sum_Icc_log`: rewrites `∑ k ∈ Icc 1 N, if p ^ k ≤ N then g k else 0`
  as `∑ k ∈ Icc 1 (p.log N), g k` for `1 < p`.
* `Nat.sum_Icc_eq_sum_primesLE_sum_Icc_log`: the regrouping of a finite sum of a function
  supported on the prime powers.
* `Nat.tendsto_sum_primesLE_inv_pow_log_succ`: `∑ p ≤ N, 1 / p ^ (Nat.log p N + 1)` tends to `0`.
* `Nat.sum_primesLE_inv_mul_sub_one_le_one`, `Nat.sum_primesLE_sum_Icc_two_inv_pow_le_one`:
  `∑ p ≤ N, 1 / (p (p - 1)) ≤ 1` and `∑ p ≤ N, ∑_{2 ≤ k ≤ log_p N} 1 / p ^ k ≤ 1`.

## References

The proof adapts the regrouping step of Mathlib's `Chebyshev.psi_eq_sum_mul_log_prime`, which
carries it out for the von Mangoldt function.
-/

public section

open Filter Finset
open scoped Topology

namespace Nat

/-- For any base `p > 1`, filtering exponents `k ∈ Icc 1 N` by `p ^ k ≤ N` is equivalent to summing
over `Icc 1 (p.log N)`. -/
theorem sum_Icc_ite_pow_le_eq_sum_Icc_log {M : Type*} [AddCommMonoid M] {p : ℕ} (hp : 1 < p)
    (N : ℕ) (g : ℕ → M) :
    ∑ k ∈ Icc 1 N, (if p ^ k ≤ N then g k else 0) = ∑ k ∈ Icc 1 (p.log N), g k := by
  rw [← sum_filter]
  congr 1
  ext k
  simp only [mem_filter, mem_Icc]
  refine ⟨fun ⟨⟨hk1, _⟩, hpk⟩ ↦ ⟨hk1, le_log_of_pow_le hp hpk⟩, fun ⟨hk1, hklog⟩ ↦ ?_⟩
  have hN0 : N ≠ 0 := by rintro rfl; simp at hklog; lia
  exact ⟨⟨hk1, hklog.trans (log_le_self p N)⟩, pow_le_of_le_log hN0 hklog⟩

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

/-- Summing `1 / (p (p - 1))` over primes `p ≤ N` is bounded above by `1`, by comparing with the
telescoping integer series `∑ (1 / (n + 1) - 1 / (n + 2))`. -/
theorem sum_primesLE_inv_mul_sub_one_le_one (N : ℕ) :
    ∑ p ∈ primesLE N, 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := by
  have hsub : primesLE N ⊆ (range N).map ⟨(· + 2), add_left_injective 2⟩ := fun p hp ↦ by
    have hp2 : 2 ≤ p := (prime_of_mem_primesLE hp).two_le
    have hpN : p ≤ N := le_of_mem_primesLE hp
    exact mem_map.mpr ⟨p - 2, mem_range.mpr (by lia), by simp; lia⟩
  calc ∑ p ∈ primesLE N, 1 / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ ∑ p ∈ (range N).map ⟨(· + 2), add_left_injective 2⟩,
          1 / ((p : ℝ) * ((p : ℝ) - 1)) :=
        sum_le_sum_of_subset_of_nonneg hsub fun m hm _ ↦ by
          obtain ⟨k, -, rfl⟩ := mem_map.mp hm
          simp only [Function.Embedding.coeFn_mk]
          have hk2 : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := mod_cast Nat.le_add_left 2 k
          exact div_nonneg zero_le_one (mul_nonneg (by linarith) (by linarith))
    _ = ∑ n ∈ range N, (((n : ℝ) + 1)⁻¹ - ((n : ℝ) + 2)⁻¹) := by
        rw [sum_map]
        refine sum_congr rfl fun n _ ↦ ?_
        simp only [Function.Embedding.coeFn_mk, ← one_div]
        push_cast
        rw [show (n : ℝ) + 2 - 1 = (n : ℝ) + 1 by ring]
        have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
        have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
        field_simp
        ring
    _ = 1 - ((N : ℝ) + 1)⁻¹ := by
        simpa [Nat.cast_add, add_assoc, one_add_one_eq_two] using
          sum_range_sub' (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) N
    _ ≤ 1 := sub_le_self 1 (by positivity)

/-- The higher-prime-power reciprocals `1 / p ^ k` (`k ≥ 2`, `p ≤ N`) sum to at most `1`. -/
theorem sum_primesLE_sum_Icc_two_inv_pow_le_one (N : ℕ) :
    ∑ p ∈ primesLE N, ∑ k ∈ Icc 2 (p.log N), ((p : ℝ) ^ k)⁻¹ ≤ 1 :=
  (sum_le_sum fun p hp ↦ TauCeti.sum_Icc_inv_pow_le (prime_of_mem_primesLE hp).ne_one
    (p.log N)).trans (sum_primesLE_inv_mul_sub_one_le_one N)

end Nat

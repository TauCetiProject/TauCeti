/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.NumberTheory.Chebyshev

/-!
# Power tails over primes

Chebyshev's bound gives `π(x) ≪ x / log x` for every `x ≥ 2`, and
`∑_{p ≥ a} p⁻ˢ ≪ₛ a^(1-s) / log a` for `s > 1` and `a > 1`.
The finite-set estimate includes a prime at the lower endpoint, so it also bounds
prime sums over arbitrary bounded intervals. Summability is established before bounding
the infinite tail, independently of the totalized value of `tsum`.

The proof integrates the finite logarithmic prime sum against `s * t^(-s-1)` and
uses `θ(t) ≤ (log 4) * t`. Removing `log p` costs at most `1 / log a`.
These estimates supply the logarithmic saving in the small-prime geometric sieve.

## References

* M. Bhargava, *The geometric sieve and the density of squarefree values of invariant
  polynomials*, arXiv:1402.0031, proof of Theorem 3.3, display (16).
-/

public section

open Finset MeasureTheory Set

namespace TauCeti

/-- An all-range Chebyshev upper bound, with an absolute constant. -/
theorem primeCounting_floor_le {x : ℝ} (hx : 1 < x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (2 * Real.log 4 + 2) * x / Real.log x := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hs : Real.sqrt x * Real.log x ≤ 2 * x := by
    have h := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    nlinarith [Real.sq_sqrt hx0.le, Real.sqrt_nonneg x]
  calc
    _ ≤ Real.log 4 * x / Real.log (Real.sqrt x) + Real.sqrt x :=
      Chebyshev.pi_le_log4_mul_div (by linarith)
    _ ≤ (2 * Real.log 4 + 2) * x / Real.log x := by
      rw [Real.log_sqrt hx0.le]
      apply (le_div_iff₀ hl).2
      field_simp
      nlinarith

-- Pointwise domination of the truncated prime kernel before integration.
private theorem sum_prime_power_kernel_le {P : Finset ℕ} {s t : ℝ}
    (hs : 0 ≤ s) (ht0 : 0 < t) (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, (Ioi (p : ℝ)).indicator
      (fun t : ℝ ↦ s * Real.log p * t ^ (-s - 1)) t) ≤
        s * Real.log 4 * t ^ (-s) := by
  classical
  have hsubset : P.filter (fun p : ℕ ↦ (p : ℝ) < t) ⊆ Nat.primesLE ⌊t⌋₊ := by
    intro p hp
    obtain ⟨hpP, hpt⟩ := mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨Nat.le_floor hpt.le, hP p hpP⟩
  have htheta : ∑ p ∈ P.filter (fun p : ℕ ↦ (p : ℝ) < t), Real.log p ≤
      Real.log 4 * t := by
    refine (sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ ↦
      Real.log_natCast_nonneg _)).trans ?_
    rw [← Chebyshev.theta_eq_sum_primesLE]
    exact Chebyshev.theta_le_log4_mul_x ht0.le
  have heq : (∑ p ∈ P, (Ioi (p : ℝ)).indicator
      (fun t : ℝ ↦ s * Real.log p * t ^ (-s - 1)) t) =
      s * t ^ (-s - 1) * ∑ p ∈ P.filter (fun p : ℕ ↦ (p : ℝ) < t), Real.log p := by
    rw [mul_sum, sum_filter]
    apply sum_congr rfl
    intro p _
    simp only [indicator_apply, Set.mem_Ioi]
    split_ifs <;> ring
  rw [heq]
  calc
    _ ≤ s * t ^ (-s - 1) * (Real.log 4 * t) := by gcongr
    _ = s * Real.log 4 * t ^ (-s) := by
      rw [mul_mul_mul_comm, ← Real.rpow_add_one ht0.ne']
      congr 2
      ring

/-- For any finite set of primes at least `a > 0`, the logarithmic power sum is
at most `(s log 4 / (s-1)) a^(1-s)`, uniformly in the set. -/
theorem sum_prime_log_mul_rpow_le {P : Finset ℕ} {a s : ℝ} (ha : 0 < a) (hs : 1 < s)
    (hP : ∀ p ∈ P, p.Prime) (haP : ∀ p ∈ P, a ≤ (p : ℝ)) :
    ∑ p ∈ P, Real.log p * (p : ℝ) ^ (-s) ≤
      s * Real.log 4 / (s - 1) * a ^ (1 - s) := by
  classical
  have hk : IntegrableOn (fun t : ℝ ↦ t ^ (-s - 1)) (Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) ha
  have hi (p : ℕ) : IntegrableOn ((Ioi (p : ℝ)).indicator
      (fun t : ℝ ↦ s * Real.log p * t ^ (-s - 1))) (Ioi a) :=
    (hk.const_mul _).indicator measurableSet_Ioi
  calc
    _ = ∫ t in Ioi a, ∑ p ∈ P, (Ioi (p : ℝ)).indicator
        (fun t : ℝ ↦ s * Real.log p * t ^ (-s - 1)) t := by
      rw [integral_finsetSum _ (fun p _ ↦ hi p)]
      apply sum_congr rfl
      intro p hp
      have hap := haP p hp
      have hp0 : 0 < (p : ℝ) := ha.trans_le hap
      rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right hap,
        integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hp0, sub_add_cancel]
      field_simp
    _ ≤ ∫ t in Ioi a, s * Real.log 4 * t ^ (-s) := by
      refine setIntegral_mono_on (integrable_finsetSum _ (fun p _ ↦ hi p))
        ((integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) ha).const_mul _)
        measurableSet_Ioi ?_
      intro t ht
      have ht0 : 0 < t := ha.trans ht
      exact sum_prime_power_kernel_le (by linarith) ht0 hP
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) ha, neg_add_eq_sub]
      field_simp [sub_ne_zero.2 hs.ne]
      ring

/-- The logarithmically improved power-tail bound over any finite set of primes,
including a prime at the lower endpoint. -/
theorem sum_prime_rpow_neg_le {P : Finset ℕ} {a s : ℝ} (ha : 1 < a) (hs : 1 < s)
    (hP : ∀ p ∈ P, p.Prime) (haP : ∀ p ∈ P, a ≤ (p : ℝ)) :
    ∑ p ∈ P, (p : ℝ) ^ (-s) ≤
      (s * Real.log 4 / (s - 1)) * a ^ (1 - s) / Real.log a := by
  have hl : 0 < Real.log a := Real.log_pos ha
  apply (le_div_iff₀ hl).2
  calc
    _ = ∑ p ∈ P, Real.log a * (p : ℝ) ^ (-s) := by
      rw [sum_mul]
      exact sum_congr rfl fun _ _ ↦ mul_comm _ _
    _ ≤ ∑ p ∈ P, Real.log p * (p : ℝ) ^ (-s) := by
      apply sum_le_sum
      intro p hp
      gcongr
      exact haP p hp
    _ ≤ _ := sum_prime_log_mul_rpow_le (by linarith) hs hP haP

/-- The strict prime tail has the bound `Cₛ a^(1-s) / log a` for every real `s > 1`
and `a > 1`, with `Cₛ = s log 4 / (s-1)`. -/
theorem tsum_prime_rpow_neg_gt_le {a s : ℝ} (ha : 1 < a) (hs : 1 < s) :
    (∑' p : ℕ, if p.Prime ∧ a < (p : ℝ) then (p : ℝ) ^ (-s) else 0) ≤
      (s * Real.log 4 / (s - 1)) * a ^ (1 - s) / Real.log a := by
  classical
  have hsum : Summable (fun p : ℕ ↦
      if p.Prime ∧ a < (p : ℝ) then (p : ℝ) ^ (-s) else 0) := by
    exact ((Real.summable_nat_rpow.mpr (by linarith : -s < -1)).indicator
      {p : ℕ | p.Prime ∧ a < (p : ℝ)}).congr (fun p ↦ by simp [Set.indicator_apply])
  apply hsum.tsum_le_of_sum_le
  intro P
  rw [← sum_filter]
  exact sum_prime_rpow_neg_le ha hs
    (fun p hp ↦ (mem_filter.mp hp).2.1) (fun p hp ↦ (mem_filter.mp hp).2.2.le)

/-- The weighted finite prime sum used in the small-prime geometric sieve.
The constant depends on `k` alone, independently of both endpoints and the dimension `n`. -/
theorem sum_primesLE_filter_gt_div_pow_le {M r : ℝ} (hM : 1 < M) (hr : 0 ≤ r)
    {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    ∑ p ∈ (Nat.primesLE ⌊r⌋₊).filter (fun p : ℕ ↦ M < (p : ℝ)),
      r ^ n / (p : ℝ) ^ k ≤
        ((k : ℝ) * Real.log 4 / (k - 1)) * r ^ n / (M ^ (k - 1) * Real.log M) := by
  have hs : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  have hbound := sum_prime_rpow_neg_le hM hs
    (P := (Nat.primesLE ⌊r⌋₊).filter (fun p : ℕ ↦ M < (p : ℝ)))
    (fun p hp ↦ (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2)
    (fun p hp ↦ (mem_filter.mp hp).2.le)
  simp only [Real.rpow_neg_natCast, zpow_neg, zpow_natCast] at hbound
  have hk1 : 1 - (k : ℝ) = -((k - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    push_cast
    ring
  have hexp : M ^ (1 - (k : ℝ)) = (M ^ (k - 1))⁻¹ := by
    rw [hk1, Real.rpow_neg (by linarith : 0 ≤ M), Real.rpow_natCast]
  rw [hexp] at hbound
  calc
    _ = r ^ n * ∑ p ∈ (Nat.primesLE ⌊r⌋₊).filter (fun p : ℕ ↦ M < (p : ℝ)),
        ((p : ℝ) ^ k)⁻¹ := by simp_rw [div_eq_mul_inv, mul_sum]
    _ ≤ r ^ n * ((k : ℝ) * Real.log 4 / (k - 1) *
        (M ^ (k - 1))⁻¹ / Real.log M) := mul_le_mul_of_nonneg_left hbound (pow_nonneg hr n)
    _ = _ := by ring

end TauCeti

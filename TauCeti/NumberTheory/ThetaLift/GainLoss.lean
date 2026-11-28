/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import TauCeti.NumberTheory.Chebyshev.Mertens
public import TauCeti.NumberTheory.Chebyshev.PrimeTail
public import TauCeti.NumberTheory.Chebyshev.RoundedLog

/-!
# Summing local losses in theta-lift chains

The local gain estimates charge a rounded logarithm at every eligible prime and a separate
quadratic rounding cost for the sandwich exponents. Below the intermediate cutoff there
are additional losses, with different formulas below and above the depth threshold. The
bounds here sum all three types of losses with weight `log p`, over any eligible subset
of the primes.

The decomposition into losses follows L. Alpöge's `PrimeSumNumericFacts` in
`Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/SecondConstantNonneg.lean`.
-/

public section

open Finset Real

namespace TauCeti

/-- The total loss from a uniform local cost `C * (Sc + k + ϑ)` multiplied by
`1 + ⌊log_p(2*a)⌋` is at most `3*C*b`, when `X*(Sc+k+ϑ)*log(2*a) ≤ b`.
Here `L` stands for `Sc + k + ϑ`. -/
theorem sum_log_mul_theta_gain_rounding_le {s : Finset ℕ} {a X C L b : ℝ}
    (ha : 1 ≤ a) (hX : 0 ≤ X) (hs : s ⊆ Nat.primesLE ⌊X⌋₊)
    (hCL : 0 ≤ C * L) (hC : 0 ≤ C) (hb : X * L * log (2 * a) ≤ b) :
    ∑ p ∈ s, log p * (C * L * ((⌊logb p (2 * a)⌋₊ : ℝ) + 1)) ≤ 3 * C * b := by
  have h₂ : log 2 ≤ log (2 * a) := log_le_log (by norm_num) (by linarith)
  have h := Chebyshev.sum_log_mul_floor_logb_add_one_le (A := 2 * a) (by linarith) hX hs
  simp_rw [mul_left_comm (log (_ : ℝ)) (C * L), ← mul_sum]
  calc
    _ ≤ C * L * (X * (log (2 * a) + log 4)) := mul_le_mul_of_nonneg_left h hCL
    _ ≤ C * L * (X * (3 * log (2 * a))) := by
      rw [log_four_eq]
      gcongr
      linarith
    _ = 3 * C * (X * L * log (2 * a)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)

/-- Sum the sandwich and rounding loss over the served primes. The coefficient `F` includes
both the uniform local constant and the number of places; `N` bounds the lattice ranks.
The estimate does not require `X ≤ 2*a`. -/
theorem sum_log_mul_theta_gain_floor_le {s : Finset ℕ} {a X F N : ℝ}
    (ha : 1 ≤ a) (hX : 0 ≤ X) (hs : s ⊆ Nat.primesLE ⌊X⌋₊) (hF : 0 ≤ F) :
    ∑ p ∈ s, log p * (F * (N ^ 2 * ((⌊logb p (2 * a)⌋₊ : ℝ) + 1) +
      ((⌊logb p (2 * a)⌋₊ : ℝ) + 1) ^ 2)) ≤
      9 * F * X * (N ^ 2 * log (2 * a) + log (2 * a) ^ 2) := by
  let A : ℝ := 2 * a
  let r (p : ℕ) : ℝ := (⌊logb p A⌋₊ : ℝ) + 1
  have h₂ : log 2 ≤ log A := log_le_log (by norm_num) (by dsimp [A]; linarith)
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have hAlog := log_nonneg hA
  have hlog : log A + log 4 ≤ 3 * log A := by rw [log_four_eq]; linarith
  have hr : logb 2 A + 1 ≤ 3 * log A := by
    rw [← log_div_log, ← le_sub_iff_add_le, div_le_iff₀ (log_pos one_lt_two)]
    have hc : 0 ≤ 3 * log 2 - 2 := by linarith [log_two_gt_d9]
    nlinarith [mul_nonneg hc hAlog]
  have h₁ : ∑ p ∈ s, log p * r p ≤ 3 * X * log A := calc
    _ ≤ X * (log A + log 4) := Chebyshev.sum_log_mul_floor_logb_add_one_le hA hX hs
    _ ≤ _ := by rw [mul_comm 3 X, mul_assoc]; gcongr
  have h₂' : ∑ p ∈ s, log p * r p ^ 2 ≤ 9 * X * log A ^ 2 := calc
    _ ≤ (logb 2 A + 1) * (X * (log A + log 4)) :=
      Chebyshev.sum_log_mul_floor_logb_add_one_sq_le hA hX hs
    _ ≤ (3 * log A) * (X * (3 * log A)) := by gcongr
    _ = _ := by ring
  calc
    _ = ∑ p ∈ s, F * (N ^ 2 * (log p * r p) + log p * r p ^ 2) := by
      apply sum_congr rfl
      intro p _
      dsimp [r, A]
      ring
    _ = F * (N ^ 2 * (∑ p ∈ s, log p * r p) + ∑ p ∈ s, log p * r p ^ 2) := by
      rw [mul_sum, ← sum_add_distrib, mul_sum]
    _ ≤ F * (N ^ 2 * (3 * X * log A) + 9 * X * log A ^ 2) := by gcongr
    _ ≤ F * (N ^ 2 * (9 * X * log A) + 9 * X * log A ^ 2) := by
      gcongr
      norm_num
    _ = _ := by dsimp [A]; ring

/-- The small-prime depth remainder: the rounded exponent makes each denominator at
least `D`. The constant cost and this remainder both sum against Chebyshev's `θ`. -/
private theorem sum_log_mul_small_gain_loss_le {s : Finset ℕ} {P S H D : ℝ}
    (hP : 0 ≤ P) (hs : s ⊆ Nat.primesLE ⌊P⌋₊) (hH : 0 ≤ H) (hD : 0 < D)
    (hcost : 0 ≤ S + H / D) :
    ∑ p ∈ s, log p * (S + H / (p : ℝ) ^ (⌈logb p D⌉₊ + 1 : ℕ)) ≤
      log 4 * P * (S + H / D) := by
  have hθ : ∑ p ∈ s, log (p : ℝ) ≤ log 4 * P := by
    apply le_trans _ (Chebyshev.theta_le_log4_mul_x hP)
    rw [Chebyshev.theta_eq_sum_primesLE]
    exact sum_le_sum_of_subset_of_nonneg hs fun p _ _ ↦ log_natCast_nonneg p
  calc
    _ ≤ ∑ p ∈ s, log p * (S + H / D) := by
      apply sum_le_sum
      intro p hp
      have hp' : 1 < (p : ℝ) := by exact_mod_cast Nat.one_lt_of_mem_primesLE (hs hp)
      have hpow : D ≤ (p : ℝ) ^ (⌈logb p D⌉₊ + 1 : ℕ) := by
        rw [← rpow_natCast, ← logb_le_iff_le_rpow hp' hD]
        simpa only [Nat.cast_add, Nat.cast_one] using
          (Nat.le_ceil (logb p D)).trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
      exact mul_le_mul_of_nonneg_left (by gcongr) (log_natCast_nonneg p)
    _ ≤ _ := by
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right hθ hcost

/-- The finite prime-sum bound for the losses below the intermediate cutoff `X`.
Here `P` is the depth threshold, `S` and `M` are the constant costs on either side of `P`,
`B/p` is the common reciprocal-prime cost, and `H` scales the depth remainders. The small-prime
exponent is chosen from `D` (equal to `k² Y_II³` in the gain estimate). In particular one can
include the cost `C * b' / x` in `M`: when `X * b' = x * b`, its contribution to
`log 4 * X * M` is `C * log 4 * b`. -/
theorem sum_log_mul_theta_gain_loss_le {s : Finset ℕ} {P X S M H D B : ℝ}
    (hP : 0 < P) (hX : 1 ≤ X) (hs : s ⊆ Nat.primesLE ⌊X⌋₊)
    (hS : 0 ≤ S + H / D) (hM : 0 ≤ M) (hH : 0 ≤ H) (hD : 0 < D) (hB : 0 ≤ B) :
    ∑ p ∈ s, log p * (B / p + if (p : ℝ) < P then
      S + H / (p : ℝ) ^ (⌈logb p D⌉₊ + 1 : ℕ) else M + H / (p : ℝ) ^ 2) ≤
      B * (log X + (log 4 + 4)) + log 4 * P * (S + H / D) +
        log 4 * X * M + 2 * log 4 * H / P := by
  classical
  let small := s.filter fun p : ℕ ↦ (p : ℝ) < P
  let medium := s.filter fun p : ℕ ↦ ¬ (p : ℝ) < P
  have hsmall : small ⊆ Nat.primesLE ⌊P⌋₊ := fun p hp ↦
    Nat.mem_primesLE.mpr ⟨Nat.le_floor (mem_filter.mp hp).2.le,
      Nat.prime_of_mem_primesLE (hs (mem_filter.mp hp).1)⟩
  have hm : medium ⊆ Nat.primesLE ⌊X⌋₊ := fun p hp ↦ hs (mem_filter.mp hp).1
  have hθ : ∑ p ∈ medium, log (p : ℝ) ≤ log 4 * X := by
    apply le_trans _ (Chebyshev.theta_le_log4_mul_x (by linarith))
    rw [Chebyshev.theta_eq_sum_primesLE]
    exact sum_le_sum_of_subset_of_nonneg hm fun p _ _ ↦ log_natCast_nonneg p
  have htail := sum_log_div_sq_le_of_prime hP
    (fun p hp ↦ Nat.prime_of_mem_primesLE (hm hp)) (fun p hp ↦ le_of_not_gt (mem_filter.mp hp).2)
  have hmertens : ∑ p ∈ s, log p / (p : ℝ) ≤ log X + (log 4 + 4) := by
    refine le_trans ?_ (Chebyshev.sum_primesLE_log_div_le hX)
    exact sum_le_sum_of_subset_of_nonneg hs (fun p _ _ ↦ by positivity)
  have hsplit : (∑ p ∈ s, log p * (if (p : ℝ) < P then
      S + H / (p : ℝ) ^ (⌈logb p D⌉₊ + 1 : ℕ) else M + H / (p : ℝ) ^ 2)) =
      (∑ p ∈ small, log p * (S + H / (p : ℝ) ^ (⌈logb p D⌉₊ + 1 : ℕ))) +
      ∑ p ∈ medium, log p * (M + H / (p : ℝ) ^ 2) := by
    rw [← sum_filter_add_sum_filter_not (s := s) (p := fun p : ℕ ↦ (p : ℝ) < P)]
    congr 1 <;> apply sum_congr rfl <;> intro p hp <;> simp [(mem_filter.mp hp).2]
  have hcommon : ∑ p ∈ s, log p * (B / (p : ℝ)) ≤ B * (log X + (log 4 + 4)) := by
    simp_rw [← mul_div_assoc, mul_comm (log (_ : ℝ)) B, mul_div_assoc, ← mul_sum]
    exact mul_le_mul_of_nonneg_left hmertens hB
  have hmedium : ∑ p ∈ medium, log p * (M + H / (p : ℝ) ^ 2) ≤
      log 4 * X * M + 2 * log 4 * H / P := by
    simp_rw [mul_add (log (_ : ℝ)), sum_add_distrib, ← sum_mul (f := fun p : ℕ ↦ log p),
      ← mul_div_assoc, mul_comm (log (_ : ℝ)) H, mul_div_assoc, ← mul_sum]
    exact add_le_add (mul_le_mul_of_nonneg_right hθ hM) (by
      convert mul_le_mul_of_nonneg_left htail hH using 1
      ring)
  simp_rw [mul_add (log (_ : ℝ)) (B / (_ : ℝ)), sum_add_distrib, hsplit]
  linarith only [sum_log_mul_small_gain_loss_le hP.le hsmall hH hD hS, hcommon, hmedium]

end TauCeti

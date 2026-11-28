/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.PrimeCounting
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.NumberTheory.ArithmeticFunction.VonMangoldt.RampTail
import TauCeti.NumberTheory.SumPrimePow

/-!
# Large-prime tails of Frobenius Riesz sums

At primes exceeding the divisibility cutoff, the entire odd-power contribution must be
charged to the error. A lower bound on the caps makes this contribution vanish at the nominal
scale; the excess at a perturbed scale is bounded by a short interval of prime powers.

The application is the large-prime term in L. Alpöge's
`Formalism.RankGapBounds.WeightedMeanData.Data.LoP` in
`Formalism/RankGapBounds/MeanBoundSecondForm.lean`
(<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open ArithmeticFunction Filter Finset
open scoped BigOperators

namespace TauCeti

/-- Bound the odd-power contribution of any selected primes beyond `X`, with caps at least `w`.
The prime-power cutoff `M` is arbitrary. The factor `2` is the off-kernel weight at an
unramified prime inert in the quadratic subfield. -/
theorem sum_prime_power_ramp_tail_le (S : Finset ℕ) (M : ℕ) (cap : ℕ → ℕ → ℝ)
    {X w a θ : ℝ} (hw : 0 ≤ w) (hθ : 0 ≤ θ) (ha : a ≤ w * (X * (1 + θ)))
    (hc : ∀ p ∈ Nat.primesLE M, p ∈ S → X < (p : ℝ) →
      ∀ k ∈ Icc 1 (p.log M), Odd k → w ≤ cap p k) :
    ∑ p ∈ Nat.primesLE M with p ∈ S ∧ X < (p : ℝ),
        (2 * Real.log p) * ∑ k ∈ Icc 1 (p.log M) with Odd k,
          max (a / ((p ^ k : ℕ) : ℝ) - cap p k) 0 ≤
      2 * Real.log (max 1 (X * (1 + θ))) * (w * X * θ ^ 2 + w * θ) := by
  classical
  let c (n : ℕ) := cap n.minFac (n.minFac.log n)
  let P (n : ℕ) := n.minFac ∈ S ∧ X < (n.minFac : ℝ) ∧ Odd (n.minFac.log n)
  let s := (Icc 1 M).filter P
  have hsum : ∑ n ∈ s, Λ n * max (a / (n : ℝ) - c n) 0 =
      ∑ p ∈ Nat.primesLE M with p ∈ S ∧ X < (p : ℝ), Real.log p *
        ∑ k ∈ Icc 1 (p.log M) with Odd k, max (a / ((p ^ k : ℕ) : ℝ) - cap p k) 0 := by
    rw [sum_filter, Nat.sum_Icc_eq_sum_primesLE_sum_Icc_log (fun n hn ↦ by
      simp [vonMangoldt_eq_zero_iff.mpr hn]), sum_filter]
    refine sum_congr rfl fun p hp ↦ ?_
    have hprime := Nat.prime_of_mem_primesLE hp
    rw [sum_filter, mul_sum]
    split_ifs with hS
    · refine sum_congr rfl fun k hk ↦ ?_
      have hk₀ := Nat.ne_of_gt (mem_Icc.mp hk).1
      simp [c, hprime.pow_minFac hk₀, Nat.log_pow hprime.one_lt,
        vonMangoldt_apply_pow hk₀, vonMangoldt_apply_prime hprime, hS.1, hS.2, mul_ite]
    · refine sum_eq_zero fun k hk ↦ ?_
      have hk₀ := Nat.ne_of_gt (mem_Icc.mp hk).1
      simp only [hprime.pow_minFac hk₀]
      exact ite_eq_right (fun h ↦ hS ⟨h.1, h.2.1⟩)
  have hx (n : ℕ) (hn : n ∈ s) : X < (n : ℝ) := by
    obtain ⟨hnI, hnP⟩ := mem_filter.mp hn
    exact hnP.2.1.trans_le (Nat.cast_le.mpr (Nat.minFac_le (mem_Icc.mp hnI).1))
  have hcap (n : ℕ) (hn : n ∈ s) : w ≤ c n := by
    obtain ⟨hnI, hnP⟩ := mem_filter.mp hn
    obtain ⟨hn₁, hnM⟩ := mem_Icc.mp hnI
    have hn₂ : n ≠ 1 := by
      intro h
      subst n
      simp [P] at hnP
    have hp := Nat.minFac_prime hn₂
    have hp_le := Nat.minFac_le hn₁
    exact hc _ (Nat.mem_primesLE.mpr ⟨hp_le.trans hnM, hp⟩) hnP.1 hnP.2.1 _
      (mem_Icc.mpr ⟨Nat.le_log_of_pow_le hp.one_lt (by simpa using hp_le),
        Nat.log_mono_right hnM⟩) hnP.2.2
  convert mul_le_mul_of_nonneg_left (sum_vonMangoldt_mul_ramp_tail_le s c hw hθ ha hx hcap)
    (zero_le_two : (0 : ℝ) ≤ 2) using 1
  · rw [hsum, mul_sum]
    exact sum_congr rfl fun p _ ↦ by rw [mul_assoc]
  · rw [mul_assoc]

open scoped Topology in
/-- The large-prime contribution is `o(b)` uniformly in the selected primes, cutoff and caps.
The nominal scale is `x * b`, the caps are at least `x * b / X`, and the relative excess of the
actual scale is at most `1 / x`. The logarithmic budget allows the cutoff `X` to grow with `x`. -/
theorem eventually_sum_prime_power_ramp_tail_le (C : ℝ) {δ η : ℝ} (hδ : δ < 1) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ (S : Finset ℕ) (M : ℕ) (cap : ℕ → ℕ → ℝ) {X b a : ℝ},
      x ≤ X → Real.log (2 * X) ≤ C * x ^ δ → 0 ≤ b → a ≤ x * b * (1 + 1 / x) →
      (∀ p ∈ Nat.primesLE M, p ∈ S → X < (p : ℝ) →
        ∀ k ∈ Icc 1 (p.log M), Odd k → x * b / X ≤ cap p k) →
      ∑ p ∈ Nat.primesLE M with p ∈ S ∧ X < (p : ℝ),
        (2 * Real.log p) * ∑ k ∈ Icc 1 (p.log M) with Odd k,
          max (a / ((p ^ k : ℕ) : ℝ) - cap p k) 0 ≤ η * b := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_const_mul_rpow_le_rpow hδ (4 * C / η)] with x hx hsmall
    S M cap X b a hX hlog hb ha hc
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hX₀ : 0 < X := hx₀.trans_le hX
  let w := x * b / X
  have hw : 0 ≤ w := by positivity
  have hscale : w * X = x * b := div_mul_cancel₀ _ hX₀.ne'
  have hw_le : w ≤ b := (div_le_iff₀ hX₀).mpr (by
    rw [mul_comm b X]
    exact mul_le_mul_of_nonneg_right hX hb)
  have hθ : 1 / x ≤ 1 := (div_le_iff₀ hx₀).mpr (by simpa using hx)
  have hcut : max 1 (X * (1 + 1 / x)) ≤ 2 * X := by
    refine max_le (by linarith) ?_
    calc
      X * (1 + 1 / x) ≤ X * (1 + 1) := by gcongr
      _ = 2 * X := by ring
  have hcost : w * X * (1 / x) ^ 2 + w * (1 / x) ≤ 2 * b / x := calc
    _ ≤ x * b * (1 / x) ^ 2 + b * (1 / x) := by
      rw [hscale]
      gcongr
    _ = _ := by field_simp; ring
  have hsmall' : 4 * C * x ^ δ ≤ η * x := by
    rw [Real.rpow_one] at hsmall
    rwa [div_mul_eq_mul_div, div_le_iff₀ hη, mul_comm x η] at hsmall
  calc
    _ ≤ 2 * Real.log (max 1 (X * (1 + 1 / x))) *
        (w * X * (1 / x) ^ 2 + w * (1 / x)) :=
      sum_prime_power_ramp_tail_le S M cap hw (by positivity) (by rwa [← mul_assoc, hscale]) hc
    _ ≤ 2 * (C * x ^ δ) * (2 * b / x) := by
      refine mul_le_mul ?_ hcost (by positivity) ?_
      · exact mul_le_mul_of_nonneg_left
          ((Real.log_le_log (zero_lt_one.trans_le (le_max_left ..)) hcut).trans hlog) zero_le_two
      · exact mul_nonneg zero_le_two ((Real.log_nonneg (by linarith)).trans hlog)
    _ = (4 * C * x ^ δ / x) * b := by ring
    _ ≤ η * b := mul_le_mul_of_nonneg_right ((div_le_iff₀ hx₀).mpr hsmall') hb

end TauCeti

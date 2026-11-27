/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import TauCeti.NumberTheory.ModularForms.ThetaLift.Level
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# The level window for integral two-cutoff weights

The logarithmic lower endpoint for the level prime depends on the mean log weight and on the
product of the two auxiliary primes. The separated cutoffs give the mean-weight bound even
when the smaller weight is formed by natural-number division. The auxiliary-prime bounds
then give the required size of the product without a separate assumption on it.

The endpoint and its bounds are those of `New.Parameters.logLevelMin_mem_Icc` in
`grh/src/New/Reduction/Data/AdmissibleData.lean` in lsernau/grh-lean (revision `72fead1`).
-/

public section

open Real Set
open scoped BigOperators

namespace TauCeti.OneSidedBound

/-- If the cutoffs satisfy `x ≤ x₁` and each auxiliary prime lies in `[b^10, b^11]`, then the
logarithmic lower endpoint with integral weights `b` and `x * b / x₁` lies in
`[m * log b, 24 * m * log b]` for `m ≥ 2`, `b ≥ 2π` and root discriminant in `[1,b]`.
Only the sizes of the auxiliary primes are used. An empty set of places gives mean log weight
zero. -/
theorem logLevelMin_twoCutoff_weights_mem_Icc {ι : Type*} (s t : Finset ι) [DecidableEq ι]
    {x x₁ b m : ℕ} {p₀ p₁ D : ℝ} (hm : 2 ≤ m) (hx₁ : x ≤ x₁)
    (hb : 2 * π ≤ (b : ℝ)) (hD : D ∈ Icc 1 (b : ℝ))
    (hp₀ : p₀ ∈ Icc ((b : ℝ) ^ 10) ((b : ℝ) ^ 11))
    (hp₁ : p₁ ∈ Icc ((b : ℝ) ^ 10) ((b : ℝ) ^ 11)) :
    ThetaLift.logLevelMin m
      (𝔼 i ∈ s, log ((if i ∈ t then b else x * b / x₁ : ℕ) : ℝ))
      (p₀ * p₁) D (log b) ∈ Icc (m * log b) (24 * m * log b) := by
  have hb₁ : 1 ≤ (b : ℝ) := hD.1.trans hD.2
  have hbR : 0 < (b : ℝ) := zero_lt_one.trans_le hb₁
  have hlog (i : ι) : log ((if i ∈ t then b else x * b / x₁ : ℕ) : ℝ) ∈ Icc 0 (log b) := by
    split_ifs
    · exact ⟨log_nonneg hb₁, le_rfl⟩
    · have hle : x * b / x₁ ≤ b := Nat.div_le_of_le_mul (Nat.mul_le_mul_right b hx₁)
      rcases Nat.eq_zero_or_pos (x * b / x₁) with h₀ | hpos
      · simpa [h₀] using log_nonneg hb₁
      · exact ⟨log_nonneg (by exact_mod_cast hpos),
          log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)⟩
  have hw : (𝔼 i ∈ s, log ((if i ∈ t then b else x * b / x₁ : ℕ) : ℝ)) ∈ Icc 0 (log b) := by
    refine ⟨Finset.expect_nonneg (fun i _ ↦ (hlog i).1), ?_⟩
    obtain rfl | hs := s.eq_empty_or_nonempty
    · simpa using log_nonneg hb₁
    · exact Finset.expect_le hs (fun i _ ↦ (hlog i).2)
  have hp : p₀ * p₁ ∈ Icc ((b : ℝ) ^ 20) ((b : ℝ) ^ 22) := by
    have h₀ : 0 ≤ p₀ := (by positivity : 0 ≤ (b : ℝ) ^ 10).trans hp₀.1
    have h₁ : 0 ≤ p₁ := (by positivity : 0 ≤ (b : ℝ) ^ 10).trans hp₁.1
    exact ⟨by simpa only [← pow_add] using mul_le_mul hp₀.1 hp₁.1 (by positivity) h₀,
      by simpa only [← pow_add] using mul_le_mul hp₀.2 hp₁.2 h₁ (by positivity)⟩
  have hexp (n : ℕ) : exp ((n : ℝ) * log b) = (b : ℝ) ^ n := by
    rw [← log_pow, exp_log (pow_pos hbR _)]
  have hp' : p₀ * p₁ ∈ Icc (exp (20 * log b)) (exp (22 * log b)) := by
    have h₂₀ : exp (20 * log b) = (b : ℝ) ^ 20 := hexp 20
    have h₂₂ : exp (22 * log b) = (b : ℝ) ^ 22 := hexp 22
    rwa [h₂₀, h₂₂]
  exact ThetaLift.logLevelMin_mem_Icc hm (log_le_log (by positivity) hb) hw hp'
    (by rwa [exp_log hbR])

end TauCeti.OneSidedBound

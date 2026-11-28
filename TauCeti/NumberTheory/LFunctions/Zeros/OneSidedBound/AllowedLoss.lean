/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
import TauCeti.NumberTheory.Harmonic.Basic
import TauCeti.NumberTheory.Harmonic.Progressions

/-!
# The total divisibility-loss budget for a chain of theta lifts

The loss at a small nonsplit prime is amplified on the two classes `±1` modulo the chain
length. The total logarithmic cost of both classes is controlled by harmonic sums after
reindexing by `(p ± 1) / m`. The level prime has a separate cost. The combined bound permits
using the same losses in local divisibility estimates and in the global normalization.

The normalization and target inequality are those of `New.Data.loss`, `New.Data.allowedLoss`
and `New.Data.sum_allowedLoss_mul_log_le` in lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open Finset

namespace TauCeti.OneSidedBound

/-- The reciprocal weight in the local loss, amplified on the two residue classes. -/
private noncomputable def primeLossWeight (m p : ℕ) : ℝ :=
  (if m ∣ p - 1 ∨ m ∣ p + 1 then (m : ℝ) else 1) / p

/-- The local loss `fa(log b)²/p`, multiplied by the chain length `m` on the classes `±1`
modulo `m`. The divisibility tests implement these classes for primes `p`. -/
noncomputable def primeLoss (m f a b p : ℕ) : ℝ :=
  (f : ℝ) * a * Real.log b ^ 2 * primeLossWeight m p

/-- The defining formula for the local loss. -/
theorem primeLoss_def (m f a b p : ℕ) :
    primeLoss m f a b p =
      (f : ℝ) * a * Real.log b ^ 2 * ((if m ∣ p - 1 ∨ m ∣ p + 1 then (m : ℝ) else 1) / p) := (rfl)

/-- The local loss has the factor `m / p` when `m` divides `p - 1` or `p + 1`. -/
@[simp] theorem primeLoss_of_dvd {m p : ℕ} (f a b : ℕ) (h : m ∣ p - 1 ∨ m ∣ p + 1) :
    primeLoss m f a b p = (f : ℝ) * a * Real.log b ^ 2 * ((m : ℝ) / p) := by
  simp [primeLoss_def, h]

/-- The local loss is unamplified when `m` divides neither `p - 1` nor `p + 1`. -/
@[simp] theorem primeLoss_of_not_dvd {m p : ℕ} (f a b : ℕ) (h : ¬(m ∣ p - 1 ∨ m ∣ p + 1)) :
    primeLoss m f a b p = (f : ℝ) * a * Real.log b ^ 2 / p := by
  simp only [primeLoss_def, ite_eq_right h, mul_one_div]

/-- The local loss is nonnegative. -/
theorem primeLoss_nonneg (m f a b p : ℕ) : 0 ≤ primeLoss m f a b p := by
  rw [primeLoss_def]
  split_ifs <;> positivity

/-- The allowed loss is twice the local loss on small nonsplit primes, and `2mfb` at the
level prime `N` (which in the application is outside the small-prime range). It is zero
elsewhere, including at every nonprime. -/
noncomputable def allowedLoss (d : ℕ) [Fact d.Prime] (x₁ m N f a b p : ℕ) : ℝ :=
  if p.Prime ∧ p < x₁ ∧ legendreSym d p ≠ 1 then 2 * primeLoss m f a b p
  else if p = N ∧ p.Prime then 2 * (m : ℝ) * f * b else 0

/-- The small-prime, level-prime, and zero cases of the allowed loss. -/
theorem allowedLoss_def (d : ℕ) [Fact d.Prime] (x₁ m N f a b p : ℕ) :
    allowedLoss d x₁ m N f a b p =
      if p.Prime ∧ p < x₁ ∧ legendreSym d p ≠ 1 then 2 * primeLoss m f a b p
      else if p = N ∧ p.Prime then 2 * (m : ℝ) * f * b else 0 := (rfl)

/-- The loss charged at a small nonsplit prime. -/
@[simp] theorem allowedLoss_of_prime_of_lt_of_legendreSym_ne_one (d : ℕ) [Fact d.Prime]
    {x₁ p : ℕ} (m N f a b : ℕ) (hp : p.Prime) (hlt : p < x₁) (hχ : legendreSym d p ≠ 1) :
    allowedLoss d x₁ m N f a b p = 2 * primeLoss m f a b p := by
  simp [allowedLoss, hp, hlt, hχ]

/-- The loss charged at the level prime when the small nonsplit branch does not apply. -/
@[simp] theorem allowedLoss_levelPrime (d : ℕ) [Fact d.Prime] {x₁ N : ℕ} (m f a b : ℕ)
    (hN : N.Prime) (h : legendreSym d N = 1 ∨ x₁ ≤ N) :
    allowedLoss d x₁ m N f a b N = 2 * (m : ℝ) * f * b := by
  rcases h with h | h
  · simp [allowedLoss, hN, h]
  · simp [allowedLoss, hN, not_lt.mpr h]

/-- No loss is charged at nonprimes. -/
@[simp] theorem allowedLoss_of_not_prime (d : ℕ) [Fact d.Prime] (x₁ m N f a b : ℕ)
    {p : ℕ} (hp : ¬p.Prime) : allowedLoss d x₁ m N f a b p = 0 := by
  simp [allowedLoss, hp]

/-- Outside the level prime and the small nonsplit primes, the loss vanishes. -/
theorem allowedLoss_eq_zero (d : ℕ) [Fact d.Prime] {x₁ N p : ℕ} (m f a b : ℕ)
    (hne : p ≠ N) (hp : legendreSym d p = 1 ∨ x₁ ≤ p) : allowedLoss d x₁ m N f a b p = 0 := by
  rcases hp with h | h <;> simp [allowedLoss, hne, h, not_lt.mpr]

/-- The allowed loss is nonnegative at all indices. -/
theorem allowedLoss_nonneg (d : ℕ) [Fact d.Prime] (x₁ m N f a b p : ℕ) :
    0 ≤ allowedLoss d x₁ m N f a b p := by
  unfold allowedLoss
  split_ifs
  · exact mul_nonneg zero_le_two (primeLoss_nonneg _ _ _ _ _)
  · positivity
  · exact le_rfl

/-- The local loss below a cutoff costs at most five logarithmically weighted harmonic sums:
one for the unweighted primes and two for each amplified residue class. -/
private theorem sum_primeLoss_mul_log_le (U : Finset ℕ) (x₁ m f a b : ℕ) :
    ∑ p ∈ U with 2 ≤ p ∧ p < x₁, primeLoss m f a b p * Real.log p ≤
      5 * f * a * Real.log b ^ 2 * Real.log x₁ * (1 + Real.log x₁) := by
  let S := U.filter fun p ↦ 2 ≤ p ∧ p < x₁
  have hS : ∀ p ∈ S, 2 ≤ p ∧ p < x₁ := fun _ hp ↦ (mem_filter.mp hp).2
  have hw (p : ℕ) : 0 ≤ primeLossWeight m p := by
    unfold primeLossWeight
    split_ifs <;> positivity
  have hminus := sum_natCast_div_le_two_mul_harmonic_of_dvd_add (m := m) (B := x₁)
    (S := S.filter fun p ↦ m ∣ p - 1) (δ := -1) (by norm_num) fun p hp ↦ by
      obtain ⟨hp, hd⟩ := mem_filter.mp hp
      obtain ⟨h₂, hlt⟩ := hS p hp
      refine ⟨h₂, hlt, ?_⟩
      simpa [Int.natCast_sub (by omega : 1 ≤ p), sub_eq_add_neg] using
        (Int.natCast_dvd_natCast.mpr hd)
  have hplus := sum_natCast_div_le_two_mul_harmonic_of_dvd_add (m := m) (B := x₁)
    (S := S.filter fun p ↦ m ∣ p + 1) (δ := 1) (by norm_num) fun p hp ↦ by
      obtain ⟨hp, hd⟩ := mem_filter.mp hp
      exact ⟨(hS p hp).1, (hS p hp).2, by exact_mod_cast hd⟩
  have hbase : ∑ p ∈ S, (p : ℝ)⁻¹ ≤ (harmonic x₁ : ℝ) := by
    rw [cast_harmonic_eq_sum_Ioc]
    exact sum_le_sum_of_subset_of_nonneg (fun p hp ↦ mem_Ioc.mpr
      ⟨zero_lt_two.trans_le (hS p hp).1, (hS p hp).2.le⟩) (by intros; positivity)
  have hsum : ∑ p ∈ S, primeLossWeight m p ≤ 5 * (1 + Real.log x₁) := by
    calc
      _ ≤ (∑ p ∈ S, (p : ℝ)⁻¹) +
          (∑ p ∈ S with m ∣ p - 1, (m : ℝ) / p) +
          (∑ p ∈ S with m ∣ p + 1, (m : ℝ) / p) := by
        simp only [sum_filter, ← sum_add_distrib]
        refine sum_le_sum fun p _ ↦ ?_
        have hm₀ : 0 ≤ (m : ℝ) / p := by positivity
        have hp₀ : 0 ≤ (p : ℝ)⁻¹ := by positivity
        by_cases hm : m ∣ p - 1 <;> by_cases hp : m ∣ p + 1
        · simp only [primeLossWeight, hm, hp, true_or, ite_true]
          linarith only [hm₀, hp₀]
        all_goals simp [primeLossWeight, hm, hp, one_div]
      _ ≤ _ := by linarith [harmonic_le_one_add_log x₁]
  let C : ℝ := (f : ℝ) * a * Real.log b ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hfactor (p : ℕ) : primeLoss m f a b p = C * primeLossWeight m p := by
    simp only [primeLoss, C]
  calc
    _ ≤ ∑ p ∈ S, C * (Real.log x₁ * primeLossWeight m p) := by
      refine sum_le_sum fun p hp ↦ ?_
      rw [hfactor, mul_assoc, mul_comm (primeLossWeight m p)]
      have hp₀ : 0 < (p : ℝ) := by exact_mod_cast (zero_lt_two.trans_le (hS p hp).1)
      have hp₁ : (p : ℝ) ≤ x₁ := by exact_mod_cast (hS p hp).2.le
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (Real.log_le_log hp₀ hp₁) (hw p)) hC
    _ = C * (Real.log x₁ * ∑ p ∈ S, primeLossWeight m p) := by rw [mul_sum, mul_sum]
    _ ≤ C * (Real.log x₁ * (5 * (1 + Real.log x₁))) := by gcongr
    _ = _ := by dsimp [C]; ring

/-- Separate the contributions of the small nonsplit primes and the level prime in the
logarithmic loss budget. This bound does not need scale separation. -/
private theorem sum_allowedLoss_mul_log_le_harmonic (d : ℕ) [Fact d.Prime]
    (U : Finset ℕ) (x₁ m N f a b : ℕ) :
    ∑ p ∈ U, allowedLoss d x₁ m N f a b p * Real.log p ≤
      10 * f * a * Real.log b ^ 2 * Real.log x₁ * (1 + Real.log x₁) +
        2 * m * f * b * Real.log N := by
  let S := U.filter fun p ↦ p.Prime ∧ p < x₁ ∧ legendreSym d p ≠ 1
  have hS : ∀ p ∈ S, 2 ≤ p ∧ p < x₁ := fun p hp ↦
    let h := (mem_filter.mp hp).2
    ⟨h.1.two_le, h.2.1⟩
  calc
    _ ≤ ∑ p ∈ U, ((if p.Prime ∧ p < x₁ ∧ legendreSym d p ≠ 1 then
        2 * (primeLoss m f a b p * Real.log p) else 0) +
        if p = N then 2 * (m : ℝ) * f * b * Real.log p else 0) := by
      refine sum_le_sum fun p _ ↦ ?_
      have hlevel : 0 ≤ (if p = N then 2 * (m : ℝ) * f * b * Real.log p else 0) :=
        ite_nonneg (by positivity) le_rfl
      rw [allowedLoss_def]
      by_cases hsmall : p.Prime ∧ p < x₁ ∧ legendreSym d p ≠ 1
      · simp only [ite_eq_left hsmall, mul_assoc (2 : ℝ) (primeLoss m f a b p)]
        exact le_add_of_nonneg_right hlevel
      · simp only [ite_eq_right hsmall, zero_add]
        split
        · rename_i hprime
          simp only [ite_eq_left hprime.1, le_refl]
        · simpa only [zero_mul] using hlevel
    _ = 2 * (∑ p ∈ S, primeLoss m f a b p * Real.log p) +
        (if N ∈ U then 2 * (m : ℝ) * f * b * Real.log N else 0) := by
      rw [sum_add_distrib, sum_ite_eq', ← sum_filter]
      simp only [S, mul_sum]
    _ ≤ _ := by
      have h₁ := sum_primeLoss_mul_log_le S x₁ m f a b
      rw [filter_eq_self.mpr hS] at h₁
      have h₂ : (if N ∈ U then 2 * (m : ℝ) * f * b * Real.log N else 0) ≤
          2 * (m : ℝ) * f * b * Real.log N := by
        split_ifs <;> first | rfl | positivity
      linarith

/-- The numerical absorption for the two terms of the loss budget. -/
private theorem lossBudget_le (x₁ : ℕ) {L : ℝ} (hL : 64 ≤ L)
    (hscale : Real.log x₁ ^ 6 ≤ L) : 10 * Real.log x₁ * (1 + Real.log x₁) + 240 / L ≤ L := by
  have hl := Real.log_natCast_nonneg x₁
  generalize Real.log (x₁ : ℝ) = l at hl hscale ⊢
  have hdiv : 240 / L ≤ (15 / 4 : ℝ) := by
    rw [div_le_iff₀ (by positivity : 0 < L)]
    linarith
  by_cases h : l ≤ 2
  · have hmul := mul_le_mul h (show 1 + l ≤ 3 by linarith) (by positivity) (by norm_num)
    linarith
  · have hlt : 2 < l := lt_of_not_ge h
    have h₄ : (16 : ℝ) ≤ l ^ 4 := calc
      (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ l ^ 4 := pow_le_pow_left₀ (by norm_num) hlt.le 4
    have h₆ : 16 * l ^ 2 ≤ l ^ 6 := by
      nlinarith [mul_le_mul_of_nonneg_right h₄ (sq_nonneg l)]
    nlinarith [mul_nonneg hl (sub_nonneg.mpr hlt.le), sq_nonneg (l - 2)]

/-- At separated cutoffs, the primewise allowed losses have total logarithmic cost at most
`f · a · (log b)³`, where `a = xb`. The only level and chain-size inputs are `log N ≤ 30 m log b`
and `m² ≤ 4x`. -/
theorem sum_allowedLoss_mul_log_le (d : ℕ) [Fact d.Prime] (U : Finset ℕ)
    {x₁ m N f x b : ℕ} (hb : 64 ≤ Real.log b) (hscale : Real.log x₁ ^ 6 ≤ Real.log b)
    (hm : m ^ 2 ≤ 4 * x) (hN : Real.log N ≤ 30 * m * Real.log b) :
    ∑ p ∈ U, allowedLoss d x₁ m N f (x * b) b p * Real.log p ≤
      (f : ℝ) * (x * b : ℕ) * Real.log b ^ 3 := by
  have hL : 0 < Real.log (b : ℝ) := by linarith
  let A : ℝ := (f : ℝ) * (x * b : ℕ)
  have hbudget := lossBudget_le x₁ hb hscale
  have hlevel : 2 * (m : ℝ) * f * b * Real.log N ≤ 240 * A * Real.log b := by
    have hm' : (m : ℝ) ^ 2 ≤ 4 * x := by exact_mod_cast hm
    calc
      _ ≤ 2 * (m : ℝ) * f * b * (30 * m * Real.log b) := by gcongr
      _ = (60 * f * b * Real.log b) * (m : ℝ) ^ 2 := by ring
      _ ≤ (60 * f * b * Real.log b) * (4 * x) := by gcongr
      _ = _ := by dsimp [A]; push_cast; ring
  have hmul := mul_le_mul_of_nonneg_left hbudget
    (show 0 ≤ A * Real.log b ^ 2 by dsimp [A]; positivity)
  have hcancel : Real.log (b : ℝ) ^ 2 * (240 / Real.log b) = 240 * Real.log b := by
    field_simp [hL.ne']
  rw [mul_add, mul_assoc A (Real.log (b : ℝ) ^ 2) (240 / Real.log b), hcancel] at hmul
  exact (sum_allowedLoss_mul_log_le_harmonic d U x₁ m N f (x * b) b).trans (by linarith)

end TauCeti.OneSidedBound

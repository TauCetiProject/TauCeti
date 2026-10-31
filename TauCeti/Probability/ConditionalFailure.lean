/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.Probability.Amplification
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Amplification with a conditional success bound

The trials may depend on their history. The event that all earlier trials
failed must be measurable in the current history, and the conditional
probability of success must have the stated almost-everywhere lower bound.
No independence assumption is used.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

@[expose] public section

namespace TauCeti.ConditionalFailure

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

theorem failure_step {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {previous success : Set Ω} (hprevious : MeasurableSet[m] previous)
    (hsuccess : MeasurableSet[m₀] success) {q : ℝ}
    (hconditional : ∀ᵐ ω ∂μ, q ≤ μ[success.indicator (fun _ => (1 : ℝ)) | m] ω) :
    μ.real (previous \ success) ≤ (1 - q) * μ.real previous := by
  have hsuccessInt : Integrable (success.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hsuccess
  have hbound : q * μ.real previous ≤ μ.real (previous ∩ success) := by
    calc
      q * μ.real previous = ∫ ω in previous, q ∂μ := by
        simp [mul_comm]
      _ ≤ ∫ ω in previous,
          μ[success.indicator (fun _ => (1 : ℝ)) | m] ω ∂μ :=
        setIntegral_mono_ae (integrable_const q) integrable_condExp.integrableOn hconditional
      _ = ∫ ω in previous, success.indicator (fun _ => (1 : ℝ)) ω ∂μ :=
        setIntegral_condExp hm hsuccessInt hprevious
      _ = μ.real (previous ∩ success) := by
        rw [setIntegral_indicator hsuccess]
        simp
  have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := previous) hsuccess
  nlinarith

/-- The event that all trials before the given index failed. -/
def failures (success : ℕ → Set Ω) : ℕ → Set Ω
  | 0 => Set.univ
  | i + 1 => failures success i \ success i

theorem measurableSet_failures (success : ℕ → Set Ω)
    (hsuccess : ∀ i, MeasurableSet (success i)) (i : ℕ) :
    MeasurableSet (failures success i) := by
  induction i with
  | zero => exact MeasurableSet.univ
  | succ i ih => exact ih.diff (hsuccess i)

theorem mem_failures_iff (success : ℕ → Set Ω) (r : ℕ) (ω : Ω) :
    ω ∈ failures success r ↔ ∀ i < r, ω ∉ success i := by
  induction r with
  | zero => simp [failures]
  | succ r ih =>
      simp only [failures, Set.mem_sdiff, ih]
      constructor
      · rintro ⟨hprevious, hcurrent⟩ i hi
        by_cases hir : i = r
        · simpa [hir] using hcurrent
        · exact hprevious i (by omega)
      · intro h
        exact ⟨fun i hi => h i (by omega), h r (by omega)⟩

theorem all_fail_le_pow (success : ℕ → Set Ω)
    (history : ℕ → MeasurableSpace Ω) (hhistory : ∀ i, history i ≤ m₀)
    (hsuccess : ∀ i, MeasurableSet (success i))
    (hprevious : ∀ i, MeasurableSet[history i] (failures success i))
    {q : ℝ} (hq : q ≤ 1)
    (hconditional : ∀ i, ∀ᵐ ω ∂μ,
      q ≤ μ[(success i).indicator (fun _ => (1 : ℝ)) | history i] ω) (r : ℕ) :
    μ.real (failures success r) ≤ (1 - q) ^ r := by
  induction r with
  | zero => simp [failures]
  | succ r ih =>
      calc
        μ.real (failures success (r + 1)) ≤ (1 - q) * μ.real (failures success r) :=
          failure_step (hhistory r) (hprevious r) (hsuccess r) (hconditional r)
        _ ≤ (1 - q) * (1 - q) ^ r := mul_le_mul_of_nonneg_left ih (by linarith)
        _ = (1 - q) ^ (r + 1) := by rw [pow_succ, mul_comm]

theorem all_fail_le_half_pow (success : ℕ → Set Ω)
    (history : ℕ → MeasurableSpace Ω) (hhistory : ∀ i, history i ≤ m₀)
    (hsuccess : ∀ i, MeasurableSet (success i))
    (hprevious : ∀ i, MeasurableSet[history i] (failures success i))
    {q : ℝ} (hq1 : q ≤ 1)
    (hconditional : ∀ i, ∀ᵐ ω ∂μ,
      q ≤ μ[(success i).indicator (fun _ => (1 : ℝ)) | history i] ω)
    (R k : ℕ) (hR : 0 < R) (hq : 1 / (R : ℝ) ≤ q) :
    μ.real (failures success (k * R)) ≤ (1 / 2 : ℝ) ^ k :=
  (all_fail_le_pow success history hhistory hsuccess hprevious hq1 hconditional (k * R)).trans
    (TauCeti.failure_pow_mul_le_half_pow hq1 R k hR hq)


end TauCeti.ConditionalFailure

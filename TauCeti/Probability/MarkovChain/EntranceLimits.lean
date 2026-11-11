/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.Visits
public import TauCeti.Probability.Process.Occupation
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Transferring occupation limits through first entrance

An almost-sure occupation limit for the chain started at `y` determines the almost-sure limit from
every initial measure: it is the same on paths that enter `y`, and zero on paths that never
enter `y`. Bounded convergence gives the corresponding expected-frequency limit from every finite
initial measure.

These transfer theorems do not require recurrence, irreducibility or a finite mean return time.
The candidate frequency is an arbitrary real number; identifying it from return cycles is a
separate question. Entrance includes time zero, whereas the conclusion counts visits at times
one through `n`. No convention for a stopped path on nonentrance affects the statements.

The argument is the first-entrance reduction in J. R. Norris, *Markov Chains*, Cambridge
University Press, 1997, §1.10, using the strong Markov property (Theorem 1.4.2).
-/

public section

open Filter ProbabilityTheory TauCeti TauCeti.Probability
open scoped Topology

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  (ν : Measure α) [IsFiniteMeasure ν] (κ : Kernel α α) [IsMarkovKernel κ]

omit [IsFiniteMeasure ν] in
/-- A point-started occupation limit extends to any initial measure, multiplied pathwise
by the indicator of ever entering the visited state. Both premise and conclusion count positive
times only. -/
theorem ae_tendsto_visitCount_div_of_ae_tendsto_dirac {y : α} {r : ℝ}
    (hy : ∀ᵐ x ∂markovChainLaw (dirac y) κ,
      Tendsto (fun n => (visitCount (shift α x) y n : ℝ) / n) atTop (𝓝 r)) :
    ∀ᵐ x ∂markovChainLaw ν κ,
      Tendsto (fun n => (visitCount (shift α x) y n : ℝ) / n) atTop
        (𝓝 (if hittingAfter (fun n x => x n) {y} 0 x ≠ ⊤ then r else 0)) := by
  classical
  let σ := successiveVisit (fun n (x : ℕ → α) => x n) y 0
  have hσ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => α)) σ :=
    Filtration.adapted_piLE.isStoppingTime_successiveVisit (measurableSet_singleton y) 0
  have hθ : Measurable (stoppedValue (fun n => (shift α)^[n]) σ) :=
    measurable_stoppedValue_of_countable (fun n => measurable_shift_iterate n) hσ.measurable'
  have hB : MeasurableSet {x : ℕ → α |
      Tendsto (fun n => (visitCount x y n : ℝ) / n) atTop (𝓝 r)} :=
    measurableSet_tendsto (𝓝 r) fun n =>
      (Measurable.of_discrete.comp
        (measurable_visitCount y n (measurableSet_singleton y))).div_const _
  -- On entrance, the stopped future has a point-started law, scaled by the entrance mass.
  have hlaw := markovChainLaw_restrict_map_successiveVisit_eq_smul ν κ y 0
  have hy' : ∀ᵐ x ∂markovChainLaw (dirac y) κ,
      Tendsto (fun n => (visitCount x y n : ℝ) / n) atTop (𝓝 r) :=
    hy.mono fun x hx => (tendsto_visitCount_shift_iterate_div_iff x y 1 r).1 hx
  have hfuture : ∀ᵐ x ∂(markovChainLaw ν κ).restrict {x | σ x ≠ ⊤},
      Tendsto (fun n => (visitCount (stoppedValue (fun n => (shift α)^[n]) σ x) y n : ℝ) / n)
        atTop (𝓝 r) := by
    apply (ae_map_iff hθ.aemeasurable hB).1
    rw [hlaw]
    exact ae_smul_measure hy' _
  have hS : MeasurableSet {x | σ x ≠ ⊤} :=
    measurableSet_setOf_successiveVisit_ne_top (fun n => measurable_pi_apply n)
      (measurableSet_singleton y) 0
  filter_upwards [(ae_restrict_iff' hS).1 hfuture] with x hx
  by_cases hhit : hittingAfter (fun n x => x n) {y} 0 x ≠ ⊤
  · rw [ite_eq_left hhit]
    have hfin : σ x ≠ ⊤ := by simpa only [σ, successiveVisit_zero] using hhit
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfin
    have htail := hx hfin
    simp only [stoppedValue, ← hn, WithTop.untopD_coe] at htail
    exact (tendsto_visitCount_shift_iterate_div_iff x y 1 r).2
      ((tendsto_visitCount_shift_iterate_div_iff x y n r).1 htail)
  · -- A path that never enters `y` has every occupation count equal to zero.
    rw [ite_eq_right hhit]
    have hnever : ∀ n, x n ≠ y := by
      simpa only [not_not, hittingAfter_eq_top_iff, zero_le, forall_const,
        Set.mem_singleton_iff] using hhit
    have hzero (n : ℕ) : visitCount (shift α x) y n = 0 :=
      visitCount_eq_zero_of_forall_ne fun i _ => hnever (i + 1)
    simpa only [hzero, Nat.cast_zero, zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- Expected occupation fractions converge to the measure of paths entering `y` times its
point-started limiting frequency. No probability normalization of the initial measure is needed. -/
theorem tendsto_integral_visitCount_div_of_ae_tendsto_dirac {y : α} {r : ℝ}
    (hy : ∀ᵐ x ∂markovChainLaw (dirac y) κ,
      Tendsto (fun n => (visitCount (shift α x) y n : ℝ) / n) atTop (𝓝 r)) :
    Tendsto (fun n => ∫ x, (visitCount (shift α x) y n : ℝ) / n ∂markovChainLaw ν κ)
      atTop (𝓝 ((markovChainLaw ν κ).real
        {x | hittingAfter (fun n x => x n) {y} 0 x ≠ ⊤} * r)) := by
  classical
  have hm (n : ℕ) : Measurable (fun x : ℕ → α => (visitCount (shift α x) y n : ℝ) / n) :=
    (Measurable.of_discrete.comp ((measurable_visitCount y n (measurableSet_singleton y)).comp
      measurable_shift)).div_const _
  have h := tendsto_integral_filter_of_norm_le_const
    (Filter.Eventually.of_forall fun n => (hm n).aestronglyMeasurable)
    (⟨1, Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun x => ?_⟩)
    (ae_tendsto_visitCount_div_of_ae_tendsto_dirac ν κ hy)
  · have hS : MeasurableSet {x : ℕ → α |
        hittingAfter (fun n x => x n) {y} 0 x ≠ ⊤} := by
      simpa only [successiveVisit_zero] using
        measurableSet_setOf_successiveVisit_ne_top (fun n => measurable_pi_apply n)
          (measurableSet_singleton y) 0
    have he : (fun x : ℕ → α =>
        if hittingAfter (fun n x => x n) {y} 0 x ≠ ⊤ then r else 0) =
        {x | hittingAfter (fun n x => x n) {y} 0 x ≠ ⊤}.indicator (fun _ => r) := by
      funext x
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    simpa only [he, integral_indicator_const _ hS, smul_eq_mul] using h
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    by_cases hn : n = 0
    · simp [hn]
    · exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)).2
        (by exact_mod_cast visitCount_le (shift α x) y n)

end MeasureTheory.Measure

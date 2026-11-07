/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.LocalProperty
public import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Uniformly integrable localizations of martingales

A strongly adapted process whose native stopped stages are martingales is a true
martingale if, at each deterministic time, those stages are uniformly integrable in
`Lᵖ`, for `1 ≤ p < ∞`. Its values then belong to `Lᵖ` as well. The criterion is useful
when moment estimates for localized stochastic integrals or stochastic exponentials
must be passed to the unstopped process.

The stopped stages retain Mathlib's indicator of the event that the stopping time
is positive. No path regularity or usual filtration conditions are needed, and the
stopping times need only tend to infinity almost surely, not be monotone. Strong
adaptation of the original process remains an explicit hypothesis: almost-sure
limits alone do not imply literal adaptation on a raw filtration.

Uniform integrability is required separately at every fixed time, not uniformly
over the entire time axis. The conclusion does not assert class D or a terminal
value at infinite time.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second
  edition, Chapter 1, §5 (local martingales).
-/

public section

open Filter ProbabilityTheory Set
open scoped ENNReal Topology

namespace MeasureTheory.StronglyAdapted

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
  [TopologicalSpace ι] [OrderTopology ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {ℱ : Filtration ι mΩ} {X : ι → Ω → E} {τ : ℕ → Ω → WithTop ι} {p : ℝ≥0∞}

/-- Uniform `Lᵖ` integrability of the native stopped martingale stages at every fixed
 time upgrades a strongly adapted local process to a martingale with `Lᵖ` values.
 The stages include the positive-stopping-time indicator, so no initial-value
 integrability assumption is hidden in the localization convention. -/
theorem martingale_and_memLp_of_uniformIntegrable_stoppedProcess
    (hX : StronglyAdapted ℱ X) (hτ : IsPreLocalizingSequence ℱ τ P)
    (hM : ∀ n, Martingale
      (MeasureTheory.stoppedProcess (fun t ↦ {ω | ⊥ < τ n ω}.indicator (X t)) (τ n)) ℱ P)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (hUI : ∀ t, UniformIntegrable
      (fun n ↦ MeasureTheory.stoppedProcess
        (fun s ↦ {ω | ⊥ < τ n ω}.indicator (X s)) (τ n) t) p P) :
    Martingale X ℱ P ∧ ∀ t, MemLp (X t) p P := by
  let Y := fun n ↦ MeasureTheory.stoppedProcess
    (fun t ↦ {ω | ⊥ < τ n ω}.indicator (X t)) (τ n)
  -- Beyond a fixed time, the stopping and the initial-time indicator both disappear.
  have hlim (t : ι) : ∀ᵐ ω ∂P, Tendsto (fun n ↦ Y n t ω) atTop (𝓝 (X t ω)) := by
    filter_upwards [hτ.tendsto_top] with ω hω
    have ht := hω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top t))
    refine tendsto_const_nhds.congr' (ht.mono fun n hn ↦ ?_)
    have hpos : ω ∈ {ω | ⊥ < τ n ω} := lt_of_le_of_lt bot_le hn
    simp only [Y, stoppedProcess_eq_of_le hn.le, indicator_of_mem hpos]
  have hLp (t : ι) : MemLp (X t) p P := (hUI t).memLp_of_ae_tendsto (hlim t)
  have hconv (t : ι) :
      Tendsto (fun n ↦ eLpNorm (Y n t - X t) p P) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendsto_ae hp hp_top (fun n ↦ (hUI t).aestronglyMeasurable n)
      (hLp t) (hUI t).unifIntegrable (hlim t)
  -- On a finite measure space, Lᵖ convergence with p ≥ 1 implies L¹ convergence.
  have hconv₁ (t : ι) :
      Tendsto (fun n ↦ eLpNorm (Y n t - X t) 1 P) atTop (𝓝 0) := by
    have hC : P univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) ≠ ∞ := by
      apply ENNReal.rpow_ne_top_of_nonneg
      · simp only [ENNReal.toReal_one, div_one]
        have hp_real : (1 : ℝ) ≤ p.toReal := by
          simpa using ENNReal.toReal_mono hp_top hp
        exact sub_nonneg.mpr (by simpa using
          one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp_real)
      · exact measure_ne_top P univ
    have hbound := ENNReal.Tendsto.mul_const (hconv t) (Or.inr hC)
    rw [zero_mul] at hbound
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
      (Eventually.of_forall fun _ ↦ bot_le) (Eventually.of_forall fun n ↦
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp
          (((hM n).integrable t).aestronglyMeasurable.sub (hLp t).aestronglyMeasurable))
  refine ⟨⟨hX, fun s t hst ↦ ?_⟩, hLp⟩
  -- Test the conditional identity on each measurable event, then pass to L¹ limits.
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s)
    ((hLp t).integrable hp) (fun _ _ _ ↦ ((hLp s).integrable hp).integrableOn)
    ?_ (hX s).aestronglyMeasurable).symm
  intro A hA _
  exact tendsto_nhds_unique
    (tendsto_setIntegral_of_L1' (X s) (Eventually.of_forall fun n ↦ (hM n).integrable s)
      (hconv₁ s) A)
    ((tendsto_setIntegral_of_L1' (X t) (Eventually.of_forall fun n ↦ (hM n).integrable t)
      (hconv₁ t) A).congr fun n ↦ ((hM n).setIntegral_eq hst hA).symm)

end MeasureTheory.StronglyAdapted

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.LocalProperty
public import Mathlib.MeasureTheory.Function.UniformIntegrable
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.Probability.Martingale.LpLimit

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

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
  [TopologicalSpace ι] [OrderTopology ι]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ι mΩ} {X : ι → Ω → E} {τ : ℕ → Ω → WithTop ι} {p : ℝ≥0∞}

namespace ProbabilityTheory.IsPreLocalizingSequence

/-- The native stopped stages of a pre-localizing sequence converge almost surely at each
fixed time. Eventually both the stopping and the positive-stopping-time indicator disappear. -/
theorem ae_tendsto_stoppedProcess [Zero E] [TopologicalSpace E]
    (hτ : IsPreLocalizingSequence ℱ τ P) (X : ι → Ω → E) (t : ι) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ MeasureTheory.stoppedProcess
      (fun s ↦ {ω | ⊥ < τ n ω}.indicator (X s)) (τ n) t ω) atTop (𝓝 (X t ω)) := by
  filter_upwards [hτ.tendsto_top] with ω hω
  have ht := hω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top t))
  refine tendsto_const_nhds.congr' (ht.mono fun n hn ↦ ?_)
  have hpos : ω ∈ {ω | ⊥ < τ n ω} := lt_of_le_of_lt bot_le hn
  simp only [stoppedProcess_eq_of_le hn.le, indicator_of_mem hpos]

/-- Uniform `Lᵖ` integrability of native stopped stages at a fixed time gives an `Lᵖ` value
of the original process. No adaptation, martingale, or exponent restriction is required. -/
theorem memLp_of_uniformIntegrable_stoppedProcess [NormedAddCommGroup E]
    (hτ : IsPreLocalizingSequence ℱ τ P) {t : ι}
    (hUI : UniformIntegrable (fun n ↦ MeasureTheory.stoppedProcess
      (fun s ↦ {ω | ⊥ < τ n ω}.indicator (X s)) (τ n) t) p P) :
    MemLp (X t) p P :=
  hUI.memLp_of_ae_tendsto (hτ.ae_tendsto_stoppedProcess X t)

end ProbabilityTheory.IsPreLocalizingSequence

namespace MeasureTheory.StronglyAdapted

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [IsFiniteMeasure P]

/-- Uniform `Lᵖ` integrability of the native stopped martingale stages at every fixed
 time upgrades a strongly adapted local process to a martingale.
 The stages include the positive-stopping-time indicator, so no initial-value
 integrability assumption is hidden in the localization convention. -/
theorem martingale_of_uniformIntegrable_stoppedProcess
    (hX : StronglyAdapted ℱ X) (hτ : IsPreLocalizingSequence ℱ τ P)
    (hM : ∀ n, Martingale
      (MeasureTheory.stoppedProcess (fun t ↦ {ω | ⊥ < τ n ω}.indicator (X t)) (τ n)) ℱ P)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (hUI : ∀ t, UniformIntegrable
      (fun n ↦ MeasureTheory.stoppedProcess
        (fun s ↦ {ω | ⊥ < τ n ω}.indicator (X s)) (τ n) t) p P) :
    Martingale X ℱ P := by
  let Y := fun n ↦ MeasureTheory.stoppedProcess
    (fun t ↦ {ω | ⊥ < τ n ω}.indicator (X t)) (τ n)
  have hLp (t : ι) : MemLp (X t) p P :=
    hτ.memLp_of_uniformIntegrable_stoppedProcess (hUI t)
  have hconv (t : ι) :
      Tendsto (fun n ↦ eLpNorm (Y n t - X t) p P) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendsto_ae hp hp_top (fun n ↦ (hUI t).aestronglyMeasurable n)
      (hLp t) (hUI t).unifIntegrable (hτ.ae_tendsto_stoppedProcess X t)
  -- On a finite measure space, Lᵖ convergence with p ≥ 1 implies L¹ convergence.
  have hconv₁ (t : ι) :
      Tendsto (fun n ↦ eLpNorm (Y n t - X t) 1 P) atTop (𝓝 0) :=
    TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm hp (hconv t)
  exact martingale_of_tendsto_eLpNorm_one hM hX hconv₁

end MeasureTheory.StronglyAdapted

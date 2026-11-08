/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.Basic
public import TauCeti.MeasureTheory.Function.ConditionalExpectation.UniformIntegrable
import Mathlib.Topology.Sequences

/-!
# Lᵖ continuity of martingales

On a finite horizon, a martingale with an Lᵖ terminal value has uniformly Lᵖ integrable
values, for finite p ≥ 1. Almost surely continuous paths therefore give a continuous map
into Lᵖ, by Vitali's theorem. In particular a continuous square-integrable stochastic integral
is continuous in mean square, not only at almost every sample point.

The filtration may be raw: neither completeness nor right continuity is needed. Continuity
is assumed only outside one common null set, and only on the declared time domain.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 1, §3.
-/

public section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {Ω ι E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsFiniteMeasure μ] [Preorder ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ℱ : Filtration ι mΩ} {M : ι → Ω → E} {p : ℝ≥0∞} {T : ι}

/-- A martingale with an Lᵖ value at T has uniformly Lᵖ integrable values at all times
up to T, for finite p ≥ 1. -/
theorem Martingale.uniformIntegrable_Iic (hM : Martingale M ℱ μ)
    (hp : 1 ≤ p) (hp_top : p ≠ ∞) (hT : MemLp (M T) p μ) :
    UniformIntegrable (fun t : Iic T => M t) p μ :=
  (hT.uniformIntegrable_condExp hp hp_top (fun t : Iic T => ℱ.le t)).ae_eq
    (fun t => hM.condExp_ae_eq t.property)

/-- Almost surely continuous martingale paths give Lᵖ continuity on a finite horizon,
provided the terminal value belongs to Lᵖ and 1 ≤ p < ∞. The map takes each time to the
native Lᵖ class of its value; no everywhere-continuous representative is required. -/
theorem Martingale.continuous_toLp [TopologicalSpace ι] [FirstCountableTopology ι]
    [Fact (1 ≤ p)] (hM : Martingale M ℱ μ) (hp_top : p ≠ ∞) (hT : MemLp (M T) p μ)
    (hcont : ∀ᵐ ω ∂μ, Continuous (fun t : Iic T => M t ω)) :
    Continuous (fun t : Iic T =>
      ((hM.uniformIntegrable_Iic (Fact.out : 1 ≤ p) hp_top hT).memLp t).toLp (M t)) := by
  have hui := hM.uniformIntegrable_Iic (Fact.out : 1 ≤ p) hp_top hT
  rw [continuous_iff_seqContinuous]
  intro u t hu
  rw [tendsto_iff_edist_tendsto_0]
  simp only [Function.comp_apply, Lp.edist_toLp_toLp]
  exact tendsto_Lp_finite_of_tendsto_ae (Fact.out : 1 ≤ p) hp_top
    (fun n => hui.aestronglyMeasurable (u n))
    (hui.memLp t) (hui.1.comp u) (hcont.mono fun ω hω => (hω.tendsto t).comp hu)

end MeasureTheory

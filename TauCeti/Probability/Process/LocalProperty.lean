/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.LocalProperty

/-!
# Convergence of localizing stopped stages

For any native local property, the stopped stages converge almost surely at each fixed time
to the original process. This uses only eventual equality, not path regularity.
-/

public section

open Filter MeasureTheory
open scoped Topology

namespace ProbabilityTheory.Locally

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
  [TopologicalSpace ι] [OrderTopology ι] [Zero E] [TopologicalSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ι mΩ}
  {X : ι → Ω → E} {p : (ι → Ω → E) → Prop}

/-- At each fixed time, the native stopped stages of any local property converge almost surely
to the original process, including the indicator of a strictly positive localizing time. -/
theorem ae_tendsto_stoppedProcess_localSeq (hX : Locally p ℱ X P) (t : ι) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ stoppedProcess
      (fun u ↦ {ω | ⊥ < hX.localSeq n ω}.indicator (X u)) (hX.localSeq n) t ω)
      atTop (𝓝 (X t ω)) := by
  filter_upwards [hX.isLocalizingSequence_localSeq.tendsto_top] with ω hω
  have ht := hω.eventually (eventually_gt_nhds (WithTop.coe_lt_top t))
  apply tendsto_const_nhds.congr'
  filter_upwards [ht] with n hn
  rw [stoppedProcess_eq_of_le hn.le, Set.indicator_of_mem]
  exact lt_of_le_of_lt (WithTop.coe_le_coe.mpr bot_le) hn

end ProbabilityTheory.Locally

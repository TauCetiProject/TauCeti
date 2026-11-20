/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Topology.Algebra.Order.Field
import TauCeti.Probability.BrownianMotion.Regularity

/-!
# Time inversion of real Brownian motion

If `B` is a standard real Brownian motion, then so is its time inversion
`X t = t * B (1 / t)`, with `X 0 = 0`. Mathlib proves that `X` has the pre-Brownian
finite-dimensional laws (`ProbabilityTheory.IsPreBrownianReal.inv`); the content here is that
almost every path of `X` is continuous, including at time `0`, where continuity is not inherited
from `B`.

Evaluating the inverted motion at `1 / t` gives the strong law of large numbers for Brownian
motion: `B t / t → 0` almost surely as `t → ∞`.

## Main results

* `ProbabilityTheory.IsBrownianReal.inv`: time inversion preserves real Brownian motion.
* `ProbabilityTheory.IsBrownianReal.tendsto_div_atTop`: almost surely `B t / t → 0` as `t → ∞`.

## Implementation notes

Continuity at `0` is obtained by comparing `X` with a continuous modification `W` of it, given
by the Kolmogorov–Chentsov theorem
(`ProbabilityTheory.IsPreBrownianReal.exists_continuous_modification`). The two processes
agree almost surely on a countable dense set of times and at time `0`; both are continuous on
`(0, ∞)`, so they agree at every time, and `X` inherits the continuity of `W`.

## References

* P. Mörters, Y. Peres, *Brownian Motion*, Cambridge University Press, 2010, Theorem 1.9 and
  Corollary 1.11.
-/

public section

open MeasureTheory Filter Set Topology
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {_ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Time inversion of Brownian motion.** If `B` is a real Brownian motion, then so is
`t ↦ t * B (1 / t)`; in particular almost every inverted path is continuous at `0`. -/
theorem IsBrownianReal.inv (hB : IsBrownianReal B P) :
    IsBrownianReal (fun t ω ↦ t * B (1 / t) ω) P where
  toIsPreBrownianReal := hB.toIsPreBrownianReal.inv
  cont := by
    obtain ⟨W, -, hW_cont, -, hW_ae⟩ := hB.toIsPreBrownianReal.inv.exists_continuous_modification
    obtain ⟨D, hD_count, hD_dense⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
    filter_upwards [hB.cont, hW_ae 0, (ae_ball_iff hD_count).2 fun t _ ↦ hW_ae t]
      with ω hBω hW0 hWD
    -- The inverted path is continuous away from `0`, where it agrees with `W` on a dense set.
    have hX : ContinuousOn (fun t : ℝ≥0 ↦ (t : ℝ) * B (1 / t) ω) (Ioi 0) := fun t ht ↦
      (NNReal.continuous_coe.continuousAt.mul <| hBω.continuousAt.comp <|
        continuousAt_const.div continuousAt_id (mem_Ioi.mp ht).ne').continuousWithinAt
    have hpos : EqOn (W · ω) (fun t : ℝ≥0 ↦ (t : ℝ) * B (1 / t) ω) (Ioi 0) :=
      EqOn.of_subset_closure (s := Ioi 0 ∩ D) (fun t ht ↦ hWD t ht.2)
        (hW_cont ω).continuousOn hX inter_subset_left
        (hD_dense.open_subset_closure_inter isOpen_Ioi)
    have hW : (W · ω) = fun t : ℝ≥0 ↦ (t : ℝ) * B (1 / t) ω := by
      funext t
      rcases eq_zero_or_pos t with rfl | ht
      · simpa using hW0
      · exact hpos ht
    exact hW ▸ hW_cont ω

/-- **Strong law of large numbers for Brownian motion.** Almost surely `B t / t → 0` as
`t → ∞`. -/
theorem IsBrownianReal.tendsto_div_atTop (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ B t ω / t) atTop (𝓝 0) := by
  filter_upwards [hB.inv.tendsto_nhds_zero] with ω hω
  refine (hω.comp (tendsto_inv_atTop_zero (𝕜 := ℝ≥0))).congr fun t ↦ ?_
  simp [div_eq_inv_mul]

end ProbabilityTheory

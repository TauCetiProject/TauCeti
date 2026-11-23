/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic

import TauCeti.Probability.BrownianMotion.Regularity
import TauCeti.Probability.Process.Indistinguishable

/-!
# Time inversion and the law of large numbers for Brownian motion

Time inversion preserves standard real Brownian motion: `t ↦ t * B (1 / t)` is Brownian,
including continuity at zero. Consequently, almost surely `B t / t → 0` as `t → ∞`.

The proof reuses Mathlib's finite-dimensional time inversion `IsPreBrownianReal.inv`,
the continuous modification supplied by `IsPreBrownianReal.exists_continuous_modification`,
and indistinguishability of continuous modifications on the strictly positive times.
Continuity of that modification at zero then supplies continuity of the inverted paths there.

## References

* Peter Mörters and Yuval Peres, *Brownian Motion*, Cambridge University Press, 2010,
  Theorem 1.9 and Corollary 1.11.
-/

public section

open Filter MeasureTheory Set
open scoped Topology NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {_ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Brownian time inversion.** If `B` is standard real Brownian motion, then so is
`t ↦ t * B (1 / t)`, with value zero at time zero. -/
theorem IsBrownianReal.inv (hB : IsBrownianReal B P) :
    IsBrownianReal (fun t ω ↦ t * B (1 / t) ω) P := by
  have hInv := hB.toIsPreBrownianReal.inv
  obtain ⟨W, _, hWcont, _, hWB⟩ := hInv.exists_continuous_modification
  have hpos : (fun t : Ioi (0 : ℝ≥0) ↦ W t) ≡ᵐ[P]
      (fun (t : Ioi (0 : ℝ≥0)) ω ↦ (t : ℝ≥0) * B (1 / (t : ℝ≥0)) ω) := by
    apply TauCeti.indist_of_ae_continuous
      (ae_of_all _ fun ω ↦ (hWcont ω).comp continuous_subtypeVal)
    · filter_upwards [hB.cont] with ω hω
      refine (NNReal.continuous_coe.comp continuous_subtypeVal).mul (hω.comp ?_)
      simpa only [one_div, Pi.inv_def] using
        continuous_subtypeVal.inv₀ (fun t : Ioi (0 : ℝ≥0) ↦ ne_of_gt t.property)
    · exact fun t ↦ hWB t
  refine ⟨hInv, ?_⟩
  filter_upwards [hpos, hWB 0] with ω hω hzero
  have heq : (W · ω) = (fun t : ℝ≥0 ↦ (t : ℝ) * B (1 / t) ω) := by
    funext t
    obtain rfl | ht := eq_or_ne t 0
    · exact hzero
    · exact hω ⟨t, pos_of_ne_zero (α := ℝ≥0) ht⟩
  exact heq ▸ hWcont ω

/-- **Brownian law of large numbers.** Almost every standard real Brownian path grows
sublinearly as time tends to infinity. -/
theorem IsBrownianReal.tendsto_div_atTop (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ B t ω / (t : ℝ)) atTop (𝓝 0) := by
  filter_upwards [hB.inv.tendsto_nhds_zero] with ω hω
  simpa only [Function.comp_def, one_div, inv_inv, mul_one, NNReal.coe_inv,
    div_eq_mul_inv, mul_comm]
    using hω.comp (tendsto_inv_atTop_zero (𝕜 := ℝ≥0))

end ProbabilityTheory

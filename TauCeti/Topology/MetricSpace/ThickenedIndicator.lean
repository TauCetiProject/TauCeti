/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.ThickenedIndicator
public import Mathlib.Analysis.Normed.MulAction

/-!
# Rescaled thickened indicators

Multiplying a thickened indicator by its radius gives a `1`-Lipschitz real function whose norm
is bounded by that radius. These functions let bounded Lipschitz test functions determine finite
Borel measures by approximation of closed-set indicators.
-/

public section

namespace TauCeti

variable {X : Type*} [PseudoEMetricSpace X] {δ : ℝ}

/-- A thickened indicator multiplied by its radius is `1`-Lipschitz as a real function. -/
theorem lipschitzWith_one_mul_thickenedIndicator (hδ : 0 < δ) (F : Set X) :
    LipschitzWith 1 fun x ↦ δ * (thickenedIndicator hδ F x : ℝ) := by
  have h := (lipschitzWith_smul (β := ℝ) δ).comp
    (NNReal.isometry_coe.lipschitzWith.comp (lipschitzWith_thickenedIndicator hδ F))
  have hnorm : ‖δ‖₊ = δ.toNNReal := by
    apply NNReal.coe_injective
    simp [Real.norm_of_nonneg hδ.le, hδ.le]
  refine h.weaken (le_of_eq ?_)
  simp only [hnorm, one_mul, mul_inv_cancel₀ (Real.toNNReal_pos.mpr hδ).ne']

/-- The norm of a thickened indicator multiplied by its radius is bounded by that radius. -/
theorem norm_mul_thickenedIndicator_le (hδ : 0 < δ) (F : Set X) (x : X) :
    ‖δ * (thickenedIndicator hδ F x : ℝ)‖ ≤ δ := by
  rw [norm_mul, Real.norm_of_nonneg hδ.le, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
  exact mul_le_of_le_one_right hδ.le (by exact_mod_cast thickenedIndicator_le_one hδ F x)

end TauCeti

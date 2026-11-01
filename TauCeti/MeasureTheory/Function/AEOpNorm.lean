/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Topology.Bases

/-!
# Almost everywhere operator-norm bounds from directional bounds

Let `τ` be a field of continuous linear maps on a separable normed space `F`, indexed by a
measure space. If `‖τ x v‖ ≤ C ‖v‖` at almost every `x` for each direction `v` separately, then
`‖τ x‖ ≤ C` at almost every `x` (`TauCeti.ae_norm_le_of_forall_ae_norm_apply_le`): the
exceptional sets of a countable dense sequence of directions form a null set, outside which the
bound extends to every direction by continuity.

## Main results

* `TauCeti.ae_norm_le_of_forall_ae_norm_apply_le`: directional almost everywhere bounds give an
  almost everywhere operator-norm bound.
-/

public section

open MeasureTheory TopologicalSpace

namespace TauCeti

variable {𝕜 F G X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeparableSpace F] [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] [MeasurableSpace X]
  {μ : Measure X}

/-- A field of continuous linear maps on a separable space that is bounded by `C` in each
direction, almost everywhere, is bounded by `C` in operator norm almost everywhere. -/
theorem ae_norm_le_of_forall_ae_norm_apply_le {τ : X → F →L[𝕜] G} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v, ∀ᵐ x ∂μ, ‖τ x v‖ ≤ C * ‖v‖) : ∀ᵐ x ∂μ, ‖τ x‖ ≤ C := by
  filter_upwards [ae_all_iff.2 fun n => h (denseSeq F n)] with x hx
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun v => ?_
  exact (denseRange_denseSeq F).induction_on v
    (isClosed_le (τ x).continuous.norm (continuous_const.mul continuous_norm)) hx

end TauCeti

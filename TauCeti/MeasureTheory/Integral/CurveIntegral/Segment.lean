/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Curve integrals of continuous `1`-forms along segments

A continuous field `ω : E → E →L[𝕜] F` of continuous linear maps is curve integrable along every
segment `Path.segment a b`. Reading a `1`-form `α : E [⋀^Fin 1]→L[𝕜] F` as the continuous linear
map `v ↦ α ![v]` through `ContinuousAlternatingMap.ofSubsingletonLIE`, curve integration along the
segment from `a` to `b` is therefore a continuous linear functional on bounded continuous
`1`-form fields, of norm at most the length `‖b - a‖` of the segment.

## Main declarations

* `Continuous.curveIntegrable_segment`: a continuous field is curve integrable along segments.
* `BoundedContinuousFunction.curveIntegralSegmentCLM a b`: curve integration along the segment
  from `a` to `b`, as a continuous linear functional on bounded continuous `1`-form fields.
* `BoundedContinuousFunction.norm_curveIntegralSegmentCLM_le`: its norm is at most `‖b - a‖`.
-/

public section

noncomputable section

open AffineMap ContinuousAlternatingMap
open scoped BoundedContinuousFunction

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A continuous field of continuous linear maps is curve integrable along every segment. -/
theorem Continuous.curveIntegrable_segment {ω : E → E →L[𝕜] F} (hω : Continuous ω) (a b : E) :
    CurveIntegrable ω (.segment a b) :=
  _root_.curveIntegrable_segment.2 <|
    ((hω.clm_apply continuous_const).comp lineMap_continuous).intervalIntegrable 0 1

namespace BoundedContinuousFunction

/-- Curve integration of bounded continuous `1`-form fields along the segment from `a` to `b`,
a `1`-form `α` being read as the continuous linear map `v ↦ α ![v]`. It is a continuous linear
functional of norm at most `‖b - a‖` (`BoundedContinuousFunction.norm_curveIntegralSegmentCLM_le`).
-/
def curveIntegralSegmentCLM (a b : E) : (E →ᵇ E [⋀^Fin 1]→L[𝕜] F) →L[𝕜] F :=
  LinearMap.mkContinuous
    { toFun ω := ∫ᶜ x in .segment a b, (ofSubsingletonLIE (0 : Fin 1)).symm (ω x)
      map_add' ω η := by
        simp only [FunLike.coe_add, Pi.add_apply, map_add]
        exact curveIntegral_fun_add
          (((ofSubsingletonLIE 0).symm.continuous.comp ω.continuous).curveIntegrable_segment a b)
          (((ofSubsingletonLIE 0).symm.continuous.comp η.continuous).curveIntegrable_segment a b)
      map_smul' c ω := by
        simp only [FunLike.coe_smul, Pi.smul_apply, map_smul, RingHom.id_apply]
        exact curveIntegral_fun_smul }
    ‖b - a‖ fun ω => (norm_curveIntegral_segment_le fun z _ =>
      ((ofSubsingletonLIE 0).symm.norm_map (ω z)).trans_le (ω.norm_coe_le_norm z)).trans_eq
        (mul_comm _ _)

/-- `BoundedContinuousFunction.curveIntegralSegmentCLM a b ω` is the curve integral of `ω` along
`Path.segment a b`, with `ω x` read as the continuous linear map `v ↦ ω x ![v]`. -/
@[simp]
theorem curveIntegralSegmentCLM_apply (a b : E) (ω : E →ᵇ E [⋀^Fin 1]→L[𝕜] F) :
    curveIntegralSegmentCLM a b ω =
      ∫ᶜ x in .segment a b, (ofSubsingleton 𝕜 E F (0 : Fin 1)).symm (ω x) := by
  simp [curveIntegralSegmentCLM]

/-- Curve integration along the segment from `a` to `b` has norm at most `‖b - a‖`. -/
theorem norm_curveIntegralSegmentCLM_le (a b : E) :
    ‖(curveIntegralSegmentCLM a b : (E →ᵇ E [⋀^Fin 1]→L[𝕜] F) →L[𝕜] F)‖ ≤ ‖b - a‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

end BoundedContinuousFunction

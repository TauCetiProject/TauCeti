/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Star
public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Curve integrals of continuous `1`-forms along segments

A continuous field `ω : E → E →L[𝕜] F` of continuous linear maps is curve integrable along every
segment `Path.segment a b`. Reading a `1`-form `α : E [⋀^Fin 1]→L[𝕜] F` as the continuous linear
map `v ↦ α ![v]` through `ContinuousAlternatingMap.ofSubsingletonLIE`, curve integration along the
segment from `a` to `b` is therefore a continuous linear functional on bounded continuous
`1`-form fields, of norm at most the length `‖b - a‖` of the segment.

For a complex function `F` with continuous derivative `f` on the segment, the curve integral of
the exact form `f(z) dz` along the segment from `a` to `b` is `F b - F a`
(`TauCeti.curveIntegral_segment_toSpanSingleton_eq_sub`). Consequently, if `F` is a primitive of
`f` on a set `S` star-convex at `c`, the curve integral of `f(z) dz` along the polygonal path from
`a ∈ S` through `c` to `b ∈ S` is `F b - F a`
(`TauCeti.curveIntegral_segment_add_segment_toSpanSingleton_eq_sub`).

## Main declarations

* `Continuous.curveIntegrable_segment`: a continuous field is curve integrable along segments.
* `BoundedContinuousFunction.curveIntegralSegmentCLM a b`: curve integration along the segment
  from `a` to `b`, as a continuous linear functional on bounded continuous `1`-form fields.
* `BoundedContinuousFunction.norm_curveIntegralSegmentCLM_le`: its norm is at most `‖b - a‖`.
* `TauCeti.curveIntegral_segment_toSpanSingleton_eq_sub`: the fundamental theorem of calculus
  along a segment in `ℂ`.
* `TauCeti.curveIntegral_segment_add_segment_toSpanSingleton_eq_sub`: the same along a two-segment
  path through the center of a star-convex domain of a primitive.
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

namespace TauCeti

open Set

/-- **Fundamental theorem of calculus along a segment.** If `F` has complex derivative `f` at every
point of the segment `[a, b]` and `f` is continuous there, the curve integral of `f(z) dz` along
`Path.segment a b` is `F b - F a`. -/
theorem curveIntegral_segment_toSpanSingleton_eq_sub {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {F f : ℂ → E} {a b : ℂ}
    (hF : ∀ z ∈ segment ℝ a b, HasDerivAt F (f z) z) (hf : ContinuousOn f (segment ℝ a b)) :
    ∫ᶜ z in Path.segment a b, ContinuousLinearMap.toSpanSingleton ℂ (f z) = F b - F a := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  have hmem : ∀ t ∈ uIcc (0 : ℝ) 1, AffineMap.lineMap a b t ∈ segment ℝ a b := fun t ht =>
    lineMap_mem_segment ℝ a b (by rwa [uIcc_of_le zero_le_one] at ht)
  rw [curveIntegral_segment]
  simp only [ContinuousLinearMap.toSpanSingleton_apply]
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => F (AffineMap.lineMap a b t))
        ((b - a) • f (AffineMap.lineMap a b t)) t := fun t ht =>
    (hF _ (hmem t ht)).scomp t (AffineMap.hasDerivAt_lineMap (a := a) (b := b) (x := t))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv, AffineMap.lineMap_apply_one,
    AffineMap.lineMap_apply_zero]
  refine ContinuousOn.intervalIntegrable ?_
  refine continuousOn_const.smul (hf.comp ?_ hmem)
  exact (AffineMap.lineMap_continuous (R := ℝ)).continuousOn

/-- **Fundamental theorem of calculus along a path through a star center.** If `F` has complex
derivative `f` on a set `S` that is star-convex at `c`, and `f` is continuous on `S`, then for
`a b ∈ S` the curve integrals of `f(z) dz` along `Path.segment a c` and `Path.segment c b` add up
to `F b - F a`. -/
theorem curveIntegral_segment_add_segment_toSpanSingleton_eq_sub {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {F f : ℂ → E} {S : Set ℂ}
    {a b c : ℂ} (hS : StarConvex ℝ c S) (ha : a ∈ S) (hb : b ∈ S)
    (hF : ∀ z ∈ S, HasDerivAt F (f z) z) (hf : ContinuousOn f S) :
    (∫ᶜ z in Path.segment a c, ContinuousLinearMap.toSpanSingleton ℂ (f z)) +
        ∫ᶜ z in Path.segment c b, ContinuousLinearMap.toSpanSingleton ℂ (f z) =
      F b - F a := by
  have h₁ : segment ℝ a c ⊆ S := by
    rw [segment_symm]
    exact hS.segment_subset ha
  have h₂ : segment ℝ c b ⊆ S := hS.segment_subset hb
  rw [curveIntegral_segment_toSpanSingleton_eq_sub (fun z hz => hF z (h₁ hz)) (hf.mono h₁),
    curveIntegral_segment_toSpanSingleton_eq_sub (fun z hz => hF z (h₂ hz)) (hf.mono h₂)]
  abel

end TauCeti

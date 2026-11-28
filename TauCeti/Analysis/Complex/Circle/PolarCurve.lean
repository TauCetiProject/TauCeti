/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.Complex.Circle.Basic

/-!
# Polar curves

The **polar curve** `r = ρ(θ)` of a radius `ρ : ℝ → ℝ` is the curve `θ ↦ ρ(θ) e^(iθ)` in `ℂ`
(`TauCeti.polarCurve`). This file records its basic analysis: continuity and smoothness, its
velocity `(ρ'(θ) + i ρ(θ)) e^(iθ)`, and the facts that the polar curve of a continuous, strictly
increasing, positive radius is a topological embedding, and that the polar curve of a radius
increasing from `0` to `∞` is closed in `ℂ ∖ {0}`.

## Main definitions

* `TauCeti.polarCurve`: the polar curve `θ ↦ ρ(θ) e^(iθ)`.

## Main results

* `TauCeti.hasDerivAt_polarCurve`, `TauCeti.fderiv_polarCurve_apply`: the velocity of a polar
  curve.
* `TauCeti.differentiableAt_polarCurve_iff`: a polar curve is differentiable exactly where its
  radius is.
* `TauCeti.isEmbedding_polarCurve`, `TauCeti.closure_range_polarCurve`: the polar curve of an
  increasing radius from `0` to `∞` is a closed embedded curve in `ℂ ∖ {0}`.
-/

public section

noncomputable section

open Complex Filter Function Set Topology

namespace TauCeti

/-- The **polar curve** `r = ρ(θ)`: the curve `θ ↦ ρ(θ) e^(iθ)` in `ℂ`. -/
def polarCurve (ρ : ℝ → ℝ) (θ : ℝ) : ℂ :=
  circleMap 0 (ρ θ) θ

@[simp]
theorem polarCurve_apply (ρ : ℝ → ℝ) (θ : ℝ) : polarCurve ρ θ = circleMap 0 (ρ θ) θ :=
  (rfl)

variable {ρ : ℝ → ℝ}

private theorem polarCurve_eq_mul : polarCurve ρ = fun θ ↦ (ρ θ : ℂ) * exp ((θ : ℂ) * I) := by
  funext θ
  rw [polarCurve_apply, circleMap_zero]

/-- The polar curve of a continuous radius is continuous. -/
theorem continuous_polarCurve (h : Continuous ρ) : Continuous (polarCurve ρ) := by
  rw [polarCurve_eq_mul]
  fun_prop

/-- The polar curve of a `Cⁿ` radius is `Cⁿ`. -/
theorem contDiff_polarCurve {n : WithTop ℕ∞} (h : ContDiff ℝ n ρ) :
    ContDiff ℝ n (polarCurve ρ) := by
  rw [polarCurve_eq_mul]
  exact (ofRealCLM.contDiff.comp h).mul ((ofRealCLM.contDiff.mul contDiff_const).cexp)

/-- The velocity of the polar curve `r = ρ(θ)` is `(ρ'(θ) + i ρ(θ)) e^(iθ)`. -/
theorem hasDerivAt_polarCurve {ρ' θ : ℝ} (h : HasDerivAt ρ ρ' θ) :
    HasDerivAt (polarCurve ρ) ((ρ' + ρ θ * I) * exp ((θ : ℂ) * I)) θ := by
  rw [hasDerivAt_iff_hasFDerivAt]
  convert hasFDerivAt_circleExp_mul_ofReal (hasFDerivAt_id θ) h.hasFDerivAt using 1
  · funext t
    simp [Circle.coe_exp, circleMap_zero, mul_comm]
  · ext
    simp [Circle.coe_exp]
    ring

/-- A polar curve is differentiable exactly where its radius is: one direction is
`TauCeti.hasDerivAt_polarCurve`, the other recovers the radius as `ρ(θ) = Re (γ(θ) e^(-iθ))`. -/
theorem differentiableAt_polarCurve_iff {θ : ℝ} :
    DifferentiableAt ℝ (polarCurve ρ) θ ↔ DifferentiableAt ℝ ρ θ := by
  refine ⟨fun h ↦ ?_, fun h ↦ (hasDerivAt_polarCurve h.hasDerivAt).differentiableAt⟩
  have hρ : ρ = fun t : ℝ ↦ (polarCurve ρ t * exp (-((t : ℂ) * I))).re := by
    funext t
    rw [polarCurve_eq_mul]
    simp [mul_assoc, ← Complex.exp_add]
  rw [hρ]
  exact reCLM.differentiableAt.comp θ
    (h.mul ((ofRealCLM.differentiableAt.mul_const I).neg.cexp))

/-- The differential of the polar curve sends `v` to `v (ρ'(θ) + i ρ(θ)) e^(iθ)`. -/
theorem fderiv_polarCurve_apply {θ : ℝ} (h : DifferentiableAt ℝ ρ θ) (v : ℝ) :
    fderiv ℝ (polarCurve ρ) θ v =
      v • ((((deriv ρ θ : ℝ) : ℂ) + ((ρ θ : ℝ) : ℂ) * I) * exp ((θ : ℂ) * I)) := by
  rw [(hasDerivAt_polarCurve h.hasDerivAt).hasFDerivAt.fderiv]
  simp

/-- **A polar curve with increasing positive radius is an embedding.** Its norm is the radius,
which is a topological embedding of `ℝ` since it is continuous and strictly increasing. -/
theorem isEmbedding_polarCurve (hc : Continuous ρ) (hm : StrictMono ρ) (hpos : ∀ θ, 0 < ρ θ) :
    IsEmbedding (polarCurve ρ) := by
  have hnorm : (fun z : ℂ ↦ ‖z‖) ∘ polarCurve ρ = ρ := by
    funext θ
    simp [abs_of_pos (hpos θ)]
  have hρ : IsEmbedding ρ := hm.isEmbedding_of_ordConnected (isPreconnected_range hc).ordConnected
  refine ⟨IsInducing.of_comp (continuous_polarCurve hc) continuous_norm
    (by rw [hnorm]; exact hρ.isInducing), fun a b h ↦ hm.injective ?_⟩
  simpa [abs_of_pos (hpos a), abs_of_pos (hpos b)] using congrArg (fun z : ℂ ↦ ‖z‖) h

/-- **A polar curve from the origin to infinity is closed in `ℂ ∖ {0}`.** If the radius `ρ` is
continuous and monotone, tends to `0` at `-∞` and to `∞` at `∞`, then the closure of the polar
curve `r = ρ(θ)` adds only the origin to it. -/
theorem closure_range_polarCurve (hc : Continuous ρ) (hm : Monotone ρ)
    (h0 : Tendsto ρ atBot (𝓝 0)) (htop : Tendsto ρ atTop atTop) :
    closure (range (polarCurve ρ)) = insert 0 (range (polarCurve ρ)) := by
  have hcont := continuous_polarCurve hc
  have hnorm (θ : ℝ) : ‖polarCurve ρ θ‖ = ρ θ := by
    simp [abs_of_nonneg (hm.le_of_tendsto h0 θ)]
  refine Subset.antisymm (fun z hz ↦ ?_) (insert_subset_iff.2 ⟨?_, subset_closure⟩)
  · rcases eq_or_ne z 0 with rfl | hz0
    · exact mem_insert _ _
    refine mem_insert_of_mem _ ?_
    -- The part of the curve in the closed ball `B` of radius `r = ‖z‖ / 2` about `z` is compact,
    -- since its parameters lie in an interval `[a, b]` on which `r ≤ ρ ≤ 3 r` can hold.
    set r := ‖z‖ / 2 with hr
    have hr0 : 0 < r := by positivity
    obtain ⟨a, ha⟩ : ∃ a, ρ a < r := (h0.eventually (gt_mem_nhds hr0)).exists
    obtain ⟨b, hb⟩ : ∃ b, 3 * r < ρ b := (htop.eventually_gt_atTop _).exists
    have hsub : polarCurve ρ ⁻¹' Metric.closedBall z r ⊆ Icc a b := by
      intro θ hθ
      rw [mem_preimage, Metric.mem_closedBall, dist_eq_norm] at hθ
      have hd : |ρ θ - ‖z‖| ≤ r := by
        rw [← hnorm]
        exact (abs_norm_sub_norm_le _ _).trans hθ
      rw [abs_le] at hd
      exact ⟨le_of_not_gt fun h ↦ by linarith [hm h.le],
        le_of_not_gt fun h ↦ by linarith [hm h.le]⟩
    have hK : IsCompact (polarCurve ρ ⁻¹' Metric.closedBall z r) :=
      isCompact_Icc.of_isClosed_subset (Metric.isClosed_closedBall.preimage hcont) hsub
    have hz' : z ∈ closure (polarCurve ρ '' (polarCurve ρ ⁻¹' Metric.closedBall z r)) := by
      rw [image_preimage_eq_range_inter, mem_closure_iff_nhds]
      intro U hU
      obtain ⟨w, hwU, hw⟩ := mem_closure_iff_nhds.1 hz (U ∩ Metric.closedBall z r)
        (inter_mem hU (Metric.closedBall_mem_nhds z hr0))
      exact ⟨w, hwU.1, hw, hwU.2⟩
    obtain ⟨θ, -, rfl⟩ := (hK.image hcont).isClosed.closure_subset hz'
    exact mem_range_self θ
  · -- The curve tends to the origin as `θ → -∞`.
    have ht : Tendsto (polarCurve ρ) atBot (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simpa only [hnorm] using h0
    exact mem_closure_of_tendsto ht (Eventually.of_forall mem_range_self)


end TauCeti

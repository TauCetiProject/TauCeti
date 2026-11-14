/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.TangentCone.Graph
public import TauCeti.Geometry.MeasureTheory.Rectifiable.TangentialFDeriv
public import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-!
# Approximate tangency and tangential Jacobians of differentiable normal graphs

At every differentiability point of a normal graph, the classical tangent plane satisfies the
measure-theoretic cone condition: the normalized Hausdorff measure of the graph outside any cone
about that plane, divided by the volume of a parameter ball, tends to zero. In fact the part
outside the cone is empty in a sufficiently small ball, so this cone comparison holds in arbitrary
real normed spaces without surface-measure finiteness or measurability of the parameter set.

When the parameter space `E` is a finite-dimensional real inner product space, the inverse-Lipschitz
property of `TauCeti.normalGraphEmbedding` upgrades the cone condition at any Lebesgue density-one
point `x ∈ s` to **uniqueness of the approximate tangent plane**, identifying
`TauCeti.approximateTangentPlane` with `LinearMap.range A.normalGraphL.toLinearMap` and, on
parameter neighborhoods `s ∈ 𝓝 x`, with the span of the classical tangent cone `tangentConeAt`. It
also yields the classical surface-area factor `√(1 + ‖A‖²)` in the tangential Jacobian formula
along the graph, and in particular `(√(1 + ‖A‖²))⁻¹` for the tangential coordinate projection
`WithLp.snd`.

All surface measures here use the normalized convention `μHE[k]`.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11 (approximate tangent planes).
* H. Federer, *Geometric Measure Theory*, 3.2.16 and 3.2.19.
-/

public section

open Filter Metric MeasureTheory Measure Module Set TauCeti
open scoped ENNReal NNReal Topology

namespace HasFDerivWithinAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {φ : E → ℝ} {A : E →L[ℝ] ℝ} {x : E}

/-- Differentiability within a parameter set makes the normal graph satisfy the cone condition
about the range of the derivative's linear graph. No surface-measure finiteness, measurability,
or membership of the base point in the parameter set is needed. This includes dimension zero. -/
theorem tendsto_euclideanHausdorffMeasure_normalGraphEmbedding_outside_cone_div
    {s : Set E} (hφ : HasFDerivWithinAt φ A s x) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun r =>
      μHE[Module.finrank ℝ E]
        {z ∈ TauCeti.normalGraphEmbedding φ '' s ∩
            closedBall (TauCeti.normalGraphEmbedding φ x) r |
          ε * dist z (TauCeti.normalGraphEmbedding φ x) <
            infDist (z - TauCeti.normalGraphEmbedding φ x)
              (LinearMap.range A.normalGraphL.toLinearMap : Set (WithLp 2 (ℝ × E)))} /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) r))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨δ, hδ, hcone⟩ := hφ.exists_pos_forall_infDist_range_normalGraphL_le hε
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ)] with r hr
  have hempty :
      {z ∈ TauCeti.normalGraphEmbedding φ '' s ∩
          closedBall (TauCeti.normalGraphEmbedding φ x) r |
        ε * dist z (TauCeti.normalGraphEmbedding φ x) <
          infDist (z - TauCeti.normalGraphEmbedding φ x)
            (LinearMap.range A.normalGraphL.toLinearMap : Set (WithLp 2 (ℝ × E)))} = ∅ := by
    apply eq_empty_of_forall_notMem
    intro z hz
    exact (not_lt_of_ge (hcone z hz.1.1
      ((mem_closedBall.mp hz.1.2).trans_lt hr))) hz.2
  rw [hempty, measure_empty, ENNReal.zero_div]

end HasFDerivWithinAt

/-- The classical tangent plane of a differentiable normal graph satisfies the approximate
tangent-plane cone condition. The parameter set is arbitrary, with no surface-measure
finiteness or measurability hypothesis. This includes dimension zero. -/
theorem HasFDerivAt.tendsto_euclideanHausdorffMeasure_normalGraphEmbedding_outside_cone_div
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {φ : E → ℝ} {A : E →L[ℝ] ℝ} {x : E}
    (hφ : HasFDerivAt φ A x) (s : Set E) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun r =>
      μHE[Module.finrank ℝ E]
        {z ∈ TauCeti.normalGraphEmbedding φ '' s ∩
            closedBall (TauCeti.normalGraphEmbedding φ x) r |
          ε * dist z (TauCeti.normalGraphEmbedding φ x) <
            infDist (z - TauCeti.normalGraphEmbedding φ x)
              (LinearMap.range A.normalGraphL.toLinearMap : Set (WithLp 2 (ℝ × E)))} /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) r))
      (𝓝[>] 0) (𝓝 0) :=
  hφ.hasFDerivWithinAt.tendsto_euclideanHausdorffMeasure_normalGraphEmbedding_outside_cone_div hε

section InnerProductParameter

variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {φ : E → ℝ} {A : E →L[ℝ] ℝ} {s : Set E} {x : E}

/-- Every neighborhood `s ∈ 𝓝 x` in a finite-dimensional real inner product space has Lebesgue
density `1` at `x`. -/
private lemma tendsto_volume_inter_closedBall_div_of_mem_nhds (hs : s ∈ 𝓝 x) :
    Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall (0 : E) r))
      (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hs
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with r ⟨hr0, hrδ⟩
  have hinter : s ∩ closedBall x r = closedBall x r :=
    inter_eq_self_of_subset_right fun y hy =>
      hball (mem_ball.mpr ((mem_closedBall.mp hy).trans_lt hrδ))
  have hpos : 0 < volume (closedBall (0 : E) r) := measure_closedBall_pos volume 0 hr0
  have htop : volume (closedBall (0 : E) r) ≠ ∞ := measure_closedBall_lt_top.ne
  rw [hinter, addHaar_closedBall_center, ENNReal.div_self hpos.ne' htop]

namespace HasFDerivWithinAt

/-- At a Lebesgue density-one point `x ∈ s` of a relatively differentiable normal graph, a subspace
`Q` of `WithLp 2 (ℝ × E)` is an approximate tangent `(dim E)`-plane to the graph iff `Q` is the
linear graph of `A`. -/
theorem isApproximateTangentPlane_normalGraphEmbedding_image_iff
    (hφ : HasFDerivWithinAt φ A s x) (hx : x ∈ s)
    (hdens : Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall (0 : E) r))
      (𝓝[>] 0) (𝓝 1))
    {Q : Submodule ℝ (WithLp 2 (ℝ × E))} :
    IsApproximateTangentPlane (finrank ℝ E) (TauCeti.normalGraphEmbedding φ '' s)
        (TauCeti.normalGraphEmbedding φ x) Q ↔
      Q = LinearMap.range A.normalGraphL.toLinearMap :=
  hφ.normalGraphEmbedding.isApproximateTangentPlane_image_iff A.injective_normalGraphL
    ((antilipschitzWith_normalGraphEmbedding φ).domRestrict s) hx hdens

/-- At a Lebesgue density-one point `x ∈ s`, the canonical approximate tangent `(dim E)`-plane to
`TauCeti.normalGraphEmbedding φ '' s` at `TauCeti.normalGraphEmbedding φ x` is the linear graph of
`A`. -/
theorem approximateTangentPlane_normalGraphEmbedding_image_eq
    (hφ : HasFDerivWithinAt φ A s x) (hx : x ∈ s)
    (hdens : Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall (0 : E) r))
      (𝓝[>] 0) (𝓝 1)) :
    approximateTangentPlane (finrank ℝ E) (TauCeti.normalGraphEmbedding φ '' s)
        (TauCeti.normalGraphEmbedding φ x) =
      LinearMap.range A.normalGraphL.toLinearMap :=
  hφ.normalGraphEmbedding.approximateTangentPlane_image_eq_range A.injective_normalGraphL
    ((antilipschitzWith_normalGraphEmbedding φ).domRestrict s) hx hdens

/-- **Tangential Jacobian along a relatively differentiable normal graph.** At a Lebesgue
density-one point `x ∈ s`, if `φ` has derivative `A` within `s` at `x` and
`ψ ∘ TauCeti.normalGraphEmbedding φ` has derivative `B` within `s` at `x`, then the tangential
Jacobian of `ψ` along `TauCeti.normalGraphEmbedding φ '' s` multiplied by `√(1 + ‖A‖²)` equals
`B.normDet`. -/
theorem tangentialJacobian_normalGraphEmbedding_mul_sqrt
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {ψ : WithLp 2 (ℝ × E) → W} {B : E →L[ℝ] W}
    (hφ : HasFDerivWithinAt φ A s x) (hx : x ∈ s)
    (hdens : Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall (0 : E) r))
      (𝓝[>] 0) (𝓝 1))
    (hψ : HasFDerivWithinAt (ψ ∘ TauCeti.normalGraphEmbedding φ) B s x) :
    tangentialJacobian (finrank ℝ E) (TauCeti.normalGraphEmbedding φ '' s) ψ
        (TauCeti.normalGraphEmbedding φ x) * Real.sqrt (1 + ‖A‖ ^ 2) =
      B.toLinearMap.normDet := by
  have hdiff : Tendsto (fun r =>
      μHE[finrank ℝ E]
        (((TauCeti.normalGraphEmbedding φ '' s) \ TauCeti.normalGraphEmbedding φ '' s) ∩
          closedBall (TauCeti.normalGraphEmbedding φ x) r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) r))
      (𝓝[>] 0) (𝓝 0) := by
    simp
  rw [← A.normDet_normalGraphL]
  exact hφ.normalGraphEmbedding.tangentialJacobian_mul_normDet A.injective_normalGraphL
    ((antilipschitzWith_normalGraphEmbedding φ).domRestrict s) hx Subset.rfl hdens hdiff hψ

/-- Along a relatively differentiable normal graph at a Lebesgue density-one point `x ∈ s`, the
tangential coordinate projection `WithLp.snd : WithLp 2 (ℝ × E) → E` has tangential Jacobian
`(√(1 + ‖A‖²))⁻¹`. -/
theorem tangentialJacobian_snd_normalGraphEmbedding
    (hφ : HasFDerivWithinAt φ A s x) (hx : x ∈ s)
    (hdens : Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall (0 : E) r))
      (𝓝[>] 0) (𝓝 1)) :
    tangentialJacobian (finrank ℝ E) (TauCeti.normalGraphEmbedding φ '' s) WithLp.snd
        (TauCeti.normalGraphEmbedding φ x) =
      (Real.sqrt (1 + ‖A‖ ^ 2))⁻¹ := by
  have hid : HasFDerivWithinAt (WithLp.snd ∘ TauCeti.normalGraphEmbedding φ)
      (ContinuousLinearMap.id ℝ E) s x :=
    (hasFDerivWithinAt_id x s).congr (fun y _ => normalGraphEmbedding_snd φ y)
      (normalGraphEmbedding_snd φ x)
  have hmul := hφ.tangentialJacobian_normalGraphEmbedding_mul_sqrt hx hdens hid
  rw [ContinuousLinearMap.coe_id, LinearMap.normDet_id] at hmul
  exact eq_inv_of_mul_eq_one_left hmul

end HasFDerivWithinAt

namespace HasFDerivAt

/-- Over a parameter neighborhood `s ∈ 𝓝 x`, a subspace `Q` is an approximate tangent
`(dim E)`-plane to `TauCeti.normalGraphEmbedding φ '' s` at `TauCeti.normalGraphEmbedding φ x` iff
`Q` is the linear graph of `A`. -/
theorem isApproximateTangentPlane_normalGraphEmbedding_image_iff
    (hφ : HasFDerivAt φ A x) (hs : s ∈ 𝓝 x) {Q : Submodule ℝ (WithLp 2 (ℝ × E))} :
    IsApproximateTangentPlane (finrank ℝ E) (TauCeti.normalGraphEmbedding φ '' s)
        (TauCeti.normalGraphEmbedding φ x) Q ↔
      Q = LinearMap.range A.normalGraphL.toLinearMap :=
  hφ.hasFDerivWithinAt.isApproximateTangentPlane_normalGraphEmbedding_image_iff
    (mem_of_mem_nhds hs) (tendsto_volume_inter_closedBall_div_of_mem_nhds hs)

/-- Over a parameter neighborhood `s ∈ 𝓝 x`, the canonical approximate tangent `(dim E)`-plane to
`TauCeti.normalGraphEmbedding φ '' s` at `TauCeti.normalGraphEmbedding φ x` is the linear graph of
`A`. -/
theorem approximateTangentPlane_normalGraphEmbedding_image_eq
    (hφ : HasFDerivAt φ A x) (hs : s ∈ 𝓝 x) :
    approximateTangentPlane (finrank ℝ E) (TauCeti.normalGraphEmbedding φ '' s)
        (TauCeti.normalGraphEmbedding φ x) =
      LinearMap.range A.normalGraphL.toLinearMap :=
  hφ.hasFDerivWithinAt.approximateTangentPlane_normalGraphEmbedding_image_eq
    (mem_of_mem_nhds hs) (tendsto_volume_inter_closedBall_div_of_mem_nhds hs)

/-- **Agreement of approximate and classical tangent spaces on differentiable normal graphs.** Over
a parameter neighborhood `s ∈ 𝓝 x`, the canonical approximate tangent `(dim E)`-plane equals the
span of the classical tangent cone `tangentConeAt`. -/
theorem approximateTangentPlane_normalGraphEmbedding_image_eq_span_tangentConeAt
    (hφ : HasFDerivAt φ A x) (hs : s ∈ 𝓝 x) :
    approximateTangentPlane (finrank ℝ E) (TauCeti.normalGraphEmbedding φ '' s)
        (TauCeti.normalGraphEmbedding φ x) =
      Submodule.span ℝ
        (tangentConeAt ℝ (TauCeti.normalGraphEmbedding φ '' s)
          (TauCeti.normalGraphEmbedding φ x)) :=
  (hφ.approximateTangentPlane_normalGraphEmbedding_image_eq hs).trans
    (hφ.span_tangentConeAt_normalGraphEmbedding_image hs).symm

/-- On the full normal graph `range (TauCeti.normalGraphEmbedding φ)`, a subspace `Q` is an
approximate tangent `(dim E)`-plane at `TauCeti.normalGraphEmbedding φ x` iff `Q` is the linear
graph of `A`. -/
theorem isApproximateTangentPlane_range_normalGraphEmbedding_iff
    (hφ : HasFDerivAt φ A x) {Q : Submodule ℝ (WithLp 2 (ℝ × E))} :
    IsApproximateTangentPlane (finrank ℝ E) (range (TauCeti.normalGraphEmbedding φ))
        (TauCeti.normalGraphEmbedding φ x) Q ↔
      Q = LinearMap.range A.normalGraphL.toLinearMap := by
  rw [← image_univ]
  exact hφ.isApproximateTangentPlane_normalGraphEmbedding_image_iff univ_mem

/-- On the full normal graph `range (TauCeti.normalGraphEmbedding φ)`, the canonical approximate
tangent `(dim E)`-plane at `TauCeti.normalGraphEmbedding φ x` is the linear graph of `A`. -/
theorem approximateTangentPlane_range_normalGraphEmbedding_eq
    (hφ : HasFDerivAt φ A x) :
    approximateTangentPlane (finrank ℝ E) (range (TauCeti.normalGraphEmbedding φ))
        (TauCeti.normalGraphEmbedding φ x) =
      LinearMap.range A.normalGraphL.toLinearMap := by
  rw [← image_univ]
  exact hφ.approximateTangentPlane_normalGraphEmbedding_image_eq univ_mem

/-- On the full normal graph `range (TauCeti.normalGraphEmbedding φ)`, the canonical approximate
tangent `(dim E)`-plane equals the span of the classical tangent cone `tangentConeAt`. -/
theorem approximateTangentPlane_range_normalGraphEmbedding_eq_span_tangentConeAt
    (hφ : HasFDerivAt φ A x) :
    approximateTangentPlane (finrank ℝ E) (range (TauCeti.normalGraphEmbedding φ))
        (TauCeti.normalGraphEmbedding φ x) =
      Submodule.span ℝ
        (tangentConeAt ℝ (range (TauCeti.normalGraphEmbedding φ))
          (TauCeti.normalGraphEmbedding φ x)) := by
  rw [← image_univ]
  exact hφ.approximateTangentPlane_normalGraphEmbedding_image_eq_span_tangentConeAt univ_mem

/-- On the full normal graph `range (TauCeti.normalGraphEmbedding φ)`, the tangential coordinate
projection `WithLp.snd` has tangential Jacobian `(√(1 + ‖A‖²))⁻¹` at
`TauCeti.normalGraphEmbedding φ x`. -/
theorem tangentialJacobian_snd_range_normalGraphEmbedding
    (hφ : HasFDerivAt φ A x) :
    tangentialJacobian (finrank ℝ E) (range (TauCeti.normalGraphEmbedding φ)) WithLp.snd
        (TauCeti.normalGraphEmbedding φ x) =
      (Real.sqrt (1 + ‖A‖ ^ 2))⁻¹ := by
  rw [← image_univ]
  exact (hφ.hasFDerivWithinAt (s := univ)).tangentialJacobian_snd_normalGraphEmbedding
    (mem_univ x) (tendsto_volume_inter_closedBall_div_of_mem_nhds univ_mem)

end HasFDerivAt

end InnerProductParameter

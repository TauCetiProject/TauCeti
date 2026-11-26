/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.TangentCone.Graph
public import TauCeti.Geometry.MeasureTheory.Rectifiable.TangentialFDeriv
public import Mathlib.Geometry.Euclidean.Volume.Measure
import TauCeti.Geometry.Euclidean.Volume.Density

/-!
# Approximate tangency and tangential calculus on differentiable normal graphs

At every differentiability point of a normal graph, the classical tangent plane also satisfies
the measure-theoretic cone condition: the normalized Hausdorff measure of the graph outside
any cone about that plane, divided by the volume of a parameter ball, tends to zero.

In fact the part outside the cone is empty in a sufficiently small ball. Consequently this
comparison does not need local finiteness of surface measure or measurability of the parameter
set. The plane is explicitly the range of `A.normalGraphL`, where `A` is the derivative of the
graphing function. `HasFDerivAt.tangentConeAt_normalGraphEmbedding_image` identifies it with
the classical tangent cone over a neighborhood of the parameter. When `E` is a finite-dimensional
real inner product space, inverse-Lipschitzness upgrades this at Lebesgue density-one points to
uniqueness of `TauCeti.approximateTangentPlane` (agreeing directly as sets with `tangentConeAt`
over neighborhoods `s ∈ 𝓝 x`), identifies `TauCeti.tangentialFDeriv` with both
`D ∘L (range A.normalGraphL).starProjection` and `B ∘L A.normalGraphL.gramLeftInverse`, and yields
the surface-area factor `√(1 + ‖A‖²)`.

All surface measures here use the normalized convention `μHE[k]`.

## References
* L. Simon, *Lectures on Geometric Measure Theory*, §11 (approximate tangent planes).
* H. Federer, *Geometric Measure Theory*, 3.2.16 and 3.2.19.
-/

public section

open Filter Metric MeasureTheory Module Set
open scoped ENNReal Topology

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
            (LinearMap.range A.normalGraphL.toLinearMap : Set (WithLp 2 (ℝ × E)))} = ∅ :=
    eq_empty_of_forall_notMem fun z hz =>
      (not_lt_of_ge (hcone z hz.1.1 ((mem_closedBall.mp hz.1.2).trans_lt hr))) hz.2
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
open Measure Module TauCeti
open scoped NNReal
variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {φ : E → ℝ} {A : E →L[ℝ] ℝ} {s : Set E} {x : E}
local notation "Gφ" => TauCeti.normalGraphEmbedding φ
local notation "kE" => finrank ℝ E
local notation "R[" A "]" =>
  LinearMap.range (ContinuousLinearMap.toLinearMap (ContinuousLinearMap.normalGraphL A))

namespace HasFDerivWithinAt
variable (hφ : HasFDerivWithinAt φ A s x) (hx : x ∈ s) (hdens : Tendsto (fun r => volume (s ∩
    closedBall x r) / volume (closedBall (0 : E) r)) (𝓝[>] 0) (𝓝 1))
include hφ hx hdens

/-- Uniqueness of the approximate tangent `(dim E)`-plane to `normalGraphEmbedding φ '' s`. -/
theorem isApproximateTangentPlane_normalGraphEmbedding_image_iff {Q : Submodule ℝ (WithLp 2 (ℝ ×
    E))} : IsApproximateTangentPlane kE (Gφ '' s) (Gφ x) Q ↔ Q = R[A] :=
  hφ.normalGraphEmbedding.isApproximateTangentPlane_image_iff
    ((antilipschitzWith_normalGraphEmbedding φ).domRestrict s) hx hdens

/-- Canonical approximate tangent `(dim E)`-plane to `normalGraphEmbedding φ '' s`. -/
theorem approximateTangentPlane_normalGraphEmbedding_image_eq :
    approximateTangentPlane kE (Gφ '' s) (Gφ x) = R[A] :=
  hφ.normalGraphEmbedding.approximateTangentPlane_image_eq_range
    ((antilipschitzWith_normalGraphEmbedding φ).domRestrict s) hx hdens

/-- Agreement of `tangentialFDeriv` with `D ∘L (range A.normalGraphL).starProjection` along a
normal graph at a Lebesgue density-one point `x ∈ s`. -/
theorem tangentialFDeriv_normalGraphEmbedding_image_eq_of_hasFDerivWithinAt
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {ψ : WithLp 2 (ℝ × E) → W} {D : WithLp 2 (ℝ × E) →L[ℝ] W}
    (hψ : HasFDerivWithinAt ψ D (Gφ '' s) (Gφ x)) :
    tangentialFDeriv kE (Gφ '' s) ψ (Gφ x) = D ∘L (R[A]).starProjection := by
  have hiff := fun Q =>
    hφ.isApproximateTangentPlane_normalGraphEmbedding_image_iff hx hdens (Q := Q)
  have hu : ∃! Q, IsApproximateTangentPlane kE (Gφ '' s) (Gφ x) Q :=
    ⟨R[A], (hiff _).mpr rfl, fun Q hQ => (hiff Q).mp hQ⟩
  rw [(HasTangentialFDerivAt.of_hasFDerivWithinAt hu hψ).tangentialFDeriv_eq,
    approximateTangentProjection_eq,
    hφ.approximateTangentPlane_normalGraphEmbedding_image_eq hx hdens]

/-- Explicit Gram-inverse formula for `tangentialFDeriv` along a relatively differentiable normal
graph at a Lebesgue density-one point `x ∈ s`. -/
theorem tangentialFDeriv_normalGraphEmbedding_image_eq
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {ψ : WithLp 2 (ℝ × E) → W} {B : E →L[ℝ] W} (hψ : HasFDerivWithinAt (ψ ∘ Gφ) B s x) :
    tangentialFDeriv kE (Gφ '' s) ψ (Gφ x) = B ∘L A.normalGraphL.gramLeftInverse :=
  (hφ.normalGraphEmbedding.hasTangentialFDerivAt_of_comp
    ((antilipschitzWith_normalGraphEmbedding φ).domRestrict s) hx Subset.rfl hdens (by simp)
    hψ).tangentialFDeriv_eq

/-- Tangential Jacobian formula along a relatively differentiable normal graph. -/
theorem tangentialJacobian_normalGraphEmbedding_mul_sqrt [NormedAddCommGroup W] [InnerProductSpace ℝ
    W] {ψ : WithLp 2 (ℝ × E) → W} {B : E →L[ℝ] W} (hψ : HasFDerivWithinAt (ψ ∘ Gφ) B s x) :
    tangentialJacobian kE (Gφ '' s) ψ (Gφ x) * Real.sqrt (1 + ‖A‖ ^ 2) = B.toLinearMap.normDet :=
  A.normDet_normalGraphL ▸ hφ.normalGraphEmbedding.tangentialJacobian_mul_normDet
    ((antilipschitzWith_normalGraphEmbedding φ).domRestrict s) hx
    Subset.rfl hdens (by simp) hψ

/-- Tangential Jacobian `(√(1 + ‖A‖²))⁻¹` of `WithLp.snd` along a normal graph. -/
theorem tangentialJacobian_snd_normalGraphEmbedding :
    tangentialJacobian kE (Gφ '' s) WithLp.snd (Gφ x) = (Real.sqrt (1 + ‖A‖ ^ 2))⁻¹ := by
  have hid := (hasFDerivWithinAt_id (𝕜 := ℝ) x s).congr (fun y _ => normalGraphEmbedding_snd φ y)
    (normalGraphEmbedding_snd φ x)
  have hm := hφ.tangentialJacobian_normalGraphEmbedding_mul_sqrt hx hdens (ψ := WithLp.snd) hid
  rw [ContinuousLinearMap.coe_id, LinearMap.normDet_id] at hm; exact eq_inv_of_mul_eq_one_left hm

end HasFDerivWithinAt

namespace HasFDerivAt
variable (hφ : HasFDerivAt φ A x)
include hφ

/-- Uniqueness of the approximate tangent `(dim E)`-plane over `s ∈ 𝓝 x`. -/
theorem isApproximateTangentPlane_normalGraphEmbedding_image_iff (hs : s ∈ 𝓝 x) {Q : Submodule ℝ
    (WithLp 2 (ℝ × E))} : IsApproximateTangentPlane kE (Gφ '' s) (Gφ x) Q ↔ Q = R[A] :=
  hφ.hasFDerivWithinAt.isApproximateTangentPlane_normalGraphEmbedding_image_iff (mem_of_mem_nhds hs)
    (tendsto_volume_inter_closedBall_div_of_mem_nhds hs)

/-- Canonical approximate tangent `(dim E)`-plane over `s ∈ 𝓝 x`. -/
theorem approximateTangentPlane_normalGraphEmbedding_image_eq (hs : s ∈ 𝓝 x) :
    approximateTangentPlane kE (Gφ '' s) (Gφ x) = R[A] :=
  ((hφ.isApproximateTangentPlane_normalGraphEmbedding_image_iff hs).mpr
    rfl).approximateTangentPlane_eq
    fun _ hQ => (hφ.isApproximateTangentPlane_normalGraphEmbedding_image_iff hs).mp hQ

/-- Direct set-level agreement of `approximateTangentPlane` with `tangentConeAt` over `s ∈ 𝓝 x`. -/
theorem coe_approximateTangentPlane_normalGraphEmbedding_image_eq_tangentConeAt (hs : s ∈ 𝓝 x) :
    (approximateTangentPlane kE (Gφ '' s) (Gφ x) : Set (WithLp 2 (ℝ × E))) =
      tangentConeAt ℝ (Gφ '' s) (Gφ x) := by
  rw [hφ.approximateTangentPlane_normalGraphEmbedding_image_eq hs,
    hφ.tangentConeAt_normalGraphEmbedding_image hs]

/-- Agreement of `approximateTangentPlane` with the span of `tangentConeAt` over `s ∈ 𝓝 x`. -/
theorem approximateTangentPlane_normalGraphEmbedding_image_eq_span_tangentConeAt (hs : s ∈ 𝓝 x) :
    approximateTangentPlane kE (Gφ '' s) (Gφ x) =
      Submodule.span ℝ (tangentConeAt ℝ (Gφ '' s) (Gφ x)) :=
  (hφ.approximateTangentPlane_normalGraphEmbedding_image_eq hs).trans
    (hφ.span_tangentConeAt_normalGraphEmbedding_image hs).symm

/-- Agreement of `tangentialFDeriv` with `D ∘L (range A.normalGraphL).starProjection` over
`s ∈ 𝓝 x`. -/
theorem tangentialFDeriv_normalGraphEmbedding_image_eq_of_hasFDerivWithinAt
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {ψ : WithLp 2 (ℝ × E) → W} {D : WithLp 2 (ℝ × E) →L[ℝ] W} (hs : s ∈ 𝓝 x)
    (hψ : HasFDerivWithinAt ψ D (Gφ '' s) (Gφ x)) :
    tangentialFDeriv kE (Gφ '' s) ψ (Gφ x) = D ∘L (R[A]).starProjection :=
  hφ.hasFDerivWithinAt.tangentialFDeriv_normalGraphEmbedding_image_eq_of_hasFDerivWithinAt
    (mem_of_mem_nhds hs) (tendsto_volume_inter_closedBall_div_of_mem_nhds hs) hψ

/-- Explicit Gram-inverse formula for `tangentialFDeriv` over `s ∈ 𝓝 x`. -/
theorem tangentialFDeriv_normalGraphEmbedding_image_eq
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {ψ : WithLp 2 (ℝ × E) → W} {B : E →L[ℝ] W} (hs : s ∈ 𝓝 x)
    (hψ : HasFDerivWithinAt (ψ ∘ Gφ) B s x) :
    tangentialFDeriv kE (Gφ '' s) ψ (Gφ x) = B ∘L A.normalGraphL.gramLeftInverse :=
  hφ.hasFDerivWithinAt.tangentialFDeriv_normalGraphEmbedding_image_eq (mem_of_mem_nhds hs)
    (tendsto_volume_inter_closedBall_div_of_mem_nhds hs) hψ

/-- Uniqueness of the approximate tangent `(dim E)`-plane on the full normal graph. -/
theorem isApproximateTangentPlane_range_normalGraphEmbedding_iff {Q : Submodule ℝ (WithLp 2 (ℝ ×
    E))} : IsApproximateTangentPlane kE (range Gφ) (Gφ x) Q ↔ Q = R[A] :=
  image_univ (f := Gφ) ▸ hφ.isApproximateTangentPlane_normalGraphEmbedding_image_iff univ_mem

/-- Canonical approximate tangent `(dim E)`-plane on `range Gφ`. -/
theorem approximateTangentPlane_range_normalGraphEmbedding_eq :
    approximateTangentPlane kE (range Gφ) (Gφ x) = R[A] :=
  image_univ (f := Gφ) ▸ hφ.approximateTangentPlane_normalGraphEmbedding_image_eq univ_mem

/-- Direct set-level agreement of `approximateTangentPlane` with `tangentConeAt` on `range Gφ`. -/
theorem coe_approximateTangentPlane_range_normalGraphEmbedding_eq_tangentConeAt :
    (approximateTangentPlane kE (range Gφ) (Gφ x) : Set (WithLp 2 (ℝ × E))) =
      tangentConeAt ℝ (range Gφ) (Gφ x) :=
  image_univ (f := Gφ) ▸
    hφ.coe_approximateTangentPlane_normalGraphEmbedding_image_eq_tangentConeAt univ_mem

/-- Agreement of `approximateTangentPlane` with the span of `tangentConeAt` on the full graph. -/
theorem approximateTangentPlane_range_normalGraphEmbedding_eq_span_tangentConeAt :
    approximateTangentPlane kE (range Gφ) (Gφ x) =
      Submodule.span ℝ (tangentConeAt ℝ (range Gφ) (Gφ x)) :=
  image_univ (f := Gφ) ▸
    hφ.approximateTangentPlane_normalGraphEmbedding_image_eq_span_tangentConeAt univ_mem

/-- Tangential Jacobian `(√(1 + ‖A‖²))⁻¹` of `WithLp.snd` on the full normal graph. -/
theorem tangentialJacobian_snd_range_normalGraphEmbedding :
    tangentialJacobian kE (range Gφ) WithLp.snd (Gφ x) = (Real.sqrt (1 + ‖A‖ ^ 2))⁻¹ :=
  image_univ (f := Gφ) ▸
    (hφ.hasFDerivWithinAt (s := univ)).tangentialJacobian_snd_normalGraphEmbedding (mem_univ x)
      (tendsto_volume_inter_closedBall_div_of_mem_nhds univ_mem)

end HasFDerivAt
end InnerProductParameter

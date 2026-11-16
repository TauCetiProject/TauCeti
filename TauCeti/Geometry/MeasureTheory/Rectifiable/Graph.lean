/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.TangentCone.Graph
public import TauCeti.Geometry.MeasureTheory.Rectifiable.TangentialFDeriv

/-!
# Approximate tangency and tangential calculus on differentiable normal graphs

At every differentiability point of a normal graph, the classical tangent plane satisfies the
measure-theoretic cone condition without finite-dimensionality or measurability assumptions. When
`E` is a finite-dimensional real inner product space, combining this cone condition with the
`1`-antilipschitz inverse projection `WithLp.snd` upgrades `LinearMap.range A.normalGraphL` to the
**unique** approximate tangent `(finrank ℝ E)`-plane:
* at any Lebesgue density-one point `x ∈ s` with `HasFDerivWithinAt φ A s x`
  (`HasFDerivWithinAt.existsUnique_isApproxTangentPlane_normalGraphEmbedding_image`,
  `HasFDerivWithinAt.approxTangentPlane_normalGraphEmbedding_image`);
* over any neighborhood `s ∈ 𝓝 x` of `HasFDerivAt φ A x`, matching `tangentConeAt`
  (`HasFDerivAt.coe_approxTangentPlane_normalGraphEmbedding_image_eq_tangentConeAt`), restricting
  ambient derivatives via `tangentialFDeriv`
  (`HasFDerivAt.tangentialFDeriv_normalGraphEmbedding_image_comp_orthogonalProjectionOnto`), and
  recovering the classical surface area factor `√(1 + ‖A‖²)`
  (`HasFDerivAt.normDet_tangentialFDeriv_normalGraphEmbedding`,
  `HasFDerivAt.normDet_tangentialFDeriv_normalGraphEmbedding_image_mul`,
  `HasFDerivAt.normDet_tangentialFDeriv_sndL_normalGraphEmbedding_image`), uniformly down to
  `finrank ℝ E = 0`.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11 (approximate tangent planes).
-/

public section

open Filter Metric MeasureTheory Module Set
open scoped ENNReal Topology

namespace HasFDerivWithinAt

section ConeCondition

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

end ConeCondition

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {φ : E → ℝ} {A : E →L[ℝ] ℝ} {s : Set E} {x : E}

/-- At a density-one point `x ∈ s`, `range A.normalGraphL` is an approximate tangent plane. -/
theorem isApproxTangentPlane_normalGraphEmbedding_image (hφ : HasFDerivWithinAt φ A s x)
    (hx : x ∈ s)
    (hs : Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall x r)) (𝓝[>] 0) (𝓝 1)) :
    TauCeti.IsApproxTangentPlane (finrank ℝ E) (TauCeti.normalGraphEmbedding φ '' s)
      (LinearMap.range A.normalGraphL.toLinearMap) (TauCeti.normalGraphEmbedding φ x) :=
  hφ.normalGraphEmbedding.isApproxTangentPlane_image hx
    ((TauCeti.antilipschitzWith_normalGraphEmbedding φ).domRestrict s) hs

/-- At a density-one point `x ∈ s`, the normal graph admits a unique approximate tangent plane. -/
theorem existsUnique_isApproxTangentPlane_normalGraphEmbedding_image
    (hφ : HasFDerivWithinAt φ A s x) (hx : x ∈ s)
    (hs : Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall x r)) (𝓝[>] 0) (𝓝 1)) :
    ∃! P : Submodule ℝ (WithLp 2 (ℝ × E)),
      TauCeti.IsApproxTangentPlane (finrank ℝ E) (TauCeti.normalGraphEmbedding φ '' s) P
        (TauCeti.normalGraphEmbedding φ x) :=
  hφ.normalGraphEmbedding.existsUnique_isApproxTangentPlane_image hx
    ((TauCeti.antilipschitzWith_normalGraphEmbedding φ).domRestrict s) hs

/-- At a density-one point `x ∈ s`, `approxTangentPlane` to the normal graph is
`range A.normalGraphL`. -/
theorem approxTangentPlane_normalGraphEmbedding_image (hφ : HasFDerivWithinAt φ A s x) (hx : x ∈ s)
    (hs : Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall x r)) (𝓝[>] 0) (𝓝 1)) :
    TauCeti.approxTangentPlane (finrank ℝ E) (TauCeti.normalGraphEmbedding φ '' s)
      (TauCeti.normalGraphEmbedding φ x) = LinearMap.range A.normalGraphL.toLinearMap :=
  hφ.normalGraphEmbedding.approxTangentPlane_image hx
    ((TauCeti.antilipschitzWith_normalGraphEmbedding φ).domRestrict s) hs

end InnerProduct

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

namespace HasFDerivAt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {φ : E → ℝ} {A : E →L[ℝ] ℝ} {s : Set E} {x : E}

private theorem tendsto_volume_inter_closedBall_div_of_mem_nhds (hs : s ∈ 𝓝 x) :
    Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall x r)) (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.1 hs
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ)] with r (hr : 0 < r) hrδ
  rw [inter_eq_right.2 ((closedBall_subset_ball hrδ).trans hsub),
    ENNReal.div_self (Metric.measure_closedBall_pos volume x hr).ne' measure_closedBall_lt_top.ne]

private theorem tendsto_empty_diff_div (x₀ : WithLp 2 (ℝ × E)) :
    Tendsto (fun r => μHE[finrank ℝ E]
      ((TauCeti.normalGraphEmbedding φ '' s \ TauCeti.normalGraphEmbedding φ '' s) ∩
        closedBall x₀ r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) r)) (𝓝[>] 0) (𝓝 0) := by
  simp only [sdiff_self, empty_inter, measure_empty, ENNReal.zero_div, tendsto_const_nhds]

/-- Over `s ∈ 𝓝 x`, `range A.normalGraphL` is an approximate tangent plane to the normal graph. -/
theorem isApproxTangentPlane_normalGraphEmbedding_image (hφ : HasFDerivAt φ A x) (hs : s ∈ 𝓝 x) :
    TauCeti.IsApproxTangentPlane (finrank ℝ E) (TauCeti.normalGraphEmbedding φ '' s)
      (LinearMap.range A.normalGraphL.toLinearMap) (TauCeti.normalGraphEmbedding φ x) :=
  hφ.hasFDerivWithinAt.isApproxTangentPlane_normalGraphEmbedding_image (mem_of_mem_nhds hs)
    (tendsto_volume_inter_closedBall_div_of_mem_nhds hs)

/-- Over `s ∈ 𝓝 x`, the normal graph admits a **unique** approximate tangent plane. -/
theorem existsUnique_isApproxTangentPlane_normalGraphEmbedding_image
    (hφ : HasFDerivAt φ A x) (hs : s ∈ 𝓝 x) :
    ∃! P : Submodule ℝ (WithLp 2 (ℝ × E)),
      TauCeti.IsApproxTangentPlane (finrank ℝ E) (TauCeti.normalGraphEmbedding φ '' s) P
        (TauCeti.normalGraphEmbedding φ x) :=
  hφ.hasFDerivWithinAt.existsUnique_isApproxTangentPlane_normalGraphEmbedding_image
    (mem_of_mem_nhds hs) (tendsto_volume_inter_closedBall_div_of_mem_nhds hs)

/-- Over `s ∈ 𝓝 x`, `approxTangentPlane` to the normal graph is `range A.normalGraphL`. -/
theorem approxTangentPlane_normalGraphEmbedding_image (hφ : HasFDerivAt φ A x) (hs : s ∈ 𝓝 x) :
    TauCeti.approxTangentPlane (finrank ℝ E) (TauCeti.normalGraphEmbedding φ '' s)
      (TauCeti.normalGraphEmbedding φ x) = LinearMap.range A.normalGraphL.toLinearMap :=
  hφ.hasFDerivWithinAt.approxTangentPlane_normalGraphEmbedding_image (mem_of_mem_nhds hs)
    (tendsto_volume_inter_closedBall_div_of_mem_nhds hs)

/-- **Agreement of `approxTangentPlane` with `tangentConeAt`** over `s ∈ 𝓝 x`. -/
theorem coe_approxTangentPlane_normalGraphEmbedding_image_eq_tangentConeAt
    (hφ : HasFDerivAt φ A x) (hs : s ∈ 𝓝 x) :
    (TauCeti.approxTangentPlane (finrank ℝ E) (TauCeti.normalGraphEmbedding φ '' s)
      (TauCeti.normalGraphEmbedding φ x) : Set (WithLp 2 (ℝ × E))) =
      tangentConeAt ℝ (TauCeti.normalGraphEmbedding φ '' s) (TauCeti.normalGraphEmbedding φ x) := by
  rw [hφ.approxTangentPlane_normalGraphEmbedding_image hs,
    hφ.tangentConeAt_normalGraphEmbedding_image hs]

/-- **Agreement of `approxTangentPlane` with `Submodule.span` of `tangentConeAt`**. -/
theorem approxTangentPlane_normalGraphEmbedding_image_eq_span_tangentConeAt
    (hφ : HasFDerivAt φ A x) (hs : s ∈ 𝓝 x) :
    TauCeti.approxTangentPlane (finrank ℝ E) (TauCeti.normalGraphEmbedding φ '' s)
      (TauCeti.normalGraphEmbedding φ x) = Submodule.span ℝ
        (tangentConeAt ℝ (TauCeti.normalGraphEmbedding φ '' s)
          (TauCeti.normalGraphEmbedding φ x)) := by
  rw [hφ.approxTangentPlane_normalGraphEmbedding_image hs,
    hφ.span_tangentConeAt_normalGraphEmbedding_image hs]

private theorem hasTangentialFDerivAt_normalGraphEmbedding_image_unique
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {g : WithLp 2 (ℝ × E) → W}
    {P : Submodule ℝ (WithLp 2 (ℝ × E))} [P.HasOrthogonalProjection] {L₁ L₂ : P →L[ℝ] W}
    (hφ : HasFDerivAt φ A x) (hs : s ∈ 𝓝 x)
    (h₁ : TauCeti.HasTangentialFDerivAt (finrank ℝ E) g P L₁ (TauCeti.normalGraphEmbedding φ '' s)
      (TauCeti.normalGraphEmbedding φ x))
    (h₂ : TauCeti.HasTangentialFDerivAt (finrank ℝ E) g P L₂ (TauCeti.normalGraphEmbedding φ '' s)
      (TauCeti.normalGraphEmbedding φ x)) : L₁ = L₂ :=
  hφ.normalGraphEmbedding.hasFDerivWithinAt.hasTangentialFDerivAt_unique (mem_of_mem_nhds hs)
    ((TauCeti.antilipschitzWith_normalGraphEmbedding φ).domRestrict s)
    (tendsto_volume_inter_closedBall_div_of_mem_nhds hs) Subset.rfl h₁ h₂

/-- Relative differentiability along a normal graph implies unique tangential differentiability. -/
theorem existsUnique_hasTangentialFDerivAt_normalGraphEmbedding_image
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : WithLp 2 (ℝ × E) → W} {D : WithLp 2 (ℝ × E) →L[ℝ] W} (hφ : HasFDerivAt φ A x)
    (hs : s ∈ 𝓝 x) (hg : HasFDerivWithinAt g D (TauCeti.normalGraphEmbedding φ '' s)
      (TauCeti.normalGraphEmbedding φ x)) :
    ∃! L : TauCeti.approxTangentPlane (finrank ℝ E) (TauCeti.normalGraphEmbedding φ '' s)
        (TauCeti.normalGraphEmbedding φ x) →L[ℝ] W,
      TauCeti.HasTangentialFDerivAt (finrank ℝ E) g
        (TauCeti.approxTangentPlane (finrank ℝ E) (TauCeti.normalGraphEmbedding φ '' s)
          (TauCeti.normalGraphEmbedding φ x))
        L (TauCeti.normalGraphEmbedding φ '' s) (TauCeti.normalGraphEmbedding φ x) :=
  let hL := hg.hasTangentialFDerivAt (hφ.isApproxTangentPlane_normalGraphEmbedding_image hs)
  TauCeti.existsUnique_hasTangentialFDerivAt_of_unique
    (hφ.existsUnique_isApproxTangentPlane_normalGraphEmbedding_image hs) hL fun _ hL' =>
      hφ.hasTangentialFDerivAt_normalGraphEmbedding_image_unique hs hL' hL

/-- **Agreement of `tangentialFDeriv` with `D.comp starProjection` on a normal graph.** -/
theorem tangentialFDeriv_normalGraphEmbedding_image_comp_orthogonalProjectionOnto
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : WithLp 2 (ℝ × E) → W} {D : WithLp 2 (ℝ × E) →L[ℝ] W} (hφ : HasFDerivAt φ A x)
    (hs : s ∈ 𝓝 x) (hg : HasFDerivWithinAt g D (TauCeti.normalGraphEmbedding φ '' s)
      (TauCeti.normalGraphEmbedding φ x)) :
    (TauCeti.tangentialFDeriv (finrank ℝ E) g (TauCeti.normalGraphEmbedding φ '' s)
        (TauCeti.normalGraphEmbedding φ x)).comp
      (TauCeti.approxTangentPlane (finrank ℝ E) (TauCeti.normalGraphEmbedding φ '' s)
        (TauCeti.normalGraphEmbedding φ x)).orthogonalProjectionOnto =
      D.comp (LinearMap.range A.normalGraphL.toLinearMap).starProjection := by
  have hL := hg.hasTangentialFDerivAt (hφ.isApproxTangentPlane_normalGraphEmbedding_image hs)
  rw [TauCeti.tangentialFDeriv_comp_orthogonalProjectionOnto_eq_of_unique
    (hφ.existsUnique_isApproxTangentPlane_normalGraphEmbedding_image hs) hL fun _ hL' =>
      hφ.hasTangentialFDerivAt_normalGraphEmbedding_image_unique hs hL' hL]
  ext; simp [ContinuousLinearMap.comp_apply]

/-- **Agreement of `normDet` of `tangentialFDeriv` with the surface factor `√(1 + ‖A‖²)`**. -/
theorem normDet_tangentialFDeriv_normalGraphEmbedding (hφ : HasFDerivAt φ A x) (hs : s ∈ 𝓝 x) :
    (TauCeti.tangentialFDeriv (finrank ℝ E) (TauCeti.normalGraphEmbedding φ) s x).normDet =
      Real.sqrt (1 + ‖A‖ ^ 2) := by
  have hval := (hasFDerivWithinAt_id x s).normDet_tangentialFDeriv_eq_div (mem_of_mem_nhds hs)
    (AntilipschitzWith.id.domRestrict s) (tendsto_volume_inter_closedBall_div_of_mem_nhds hs)
    (by rw [image_id]) (by simp only [image_id, sdiff_self, empty_inter, measure_empty,
      ENNReal.zero_div, tendsto_const_nhds])
    (by simpa only [Function.comp_id] using hφ.normalGraphEmbedding.hasFDerivWithinAt (s := s))
  rw [show x = (_root_.id : E → E) x from rfl, hval,
    show (ContinuousLinearMap.id ℝ E).normDet = 1 from LinearMap.normDet_id, div_one,
    ContinuousLinearMap.normDet_normalGraphL]

/-- **Surface Jacobian factorization along a normal graph**: `* √(1 + ‖A‖²) = B.normDet`. -/
theorem normDet_tangentialFDeriv_normalGraphEmbedding_image_mul
    {W₀ : Type*} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀]
    {g : WithLp 2 (ℝ × E) → W₀} {B : E →L[ℝ] W₀} (hφ : HasFDerivAt φ A x) (hs : s ∈ 𝓝 x)
    (hg : HasFDerivWithinAt (g ∘ TauCeti.normalGraphEmbedding φ) B s x) :
    (TauCeti.tangentialFDeriv (finrank ℝ E) g (TauCeti.normalGraphEmbedding φ '' s)
        (TauCeti.normalGraphEmbedding φ x)).normDet * Real.sqrt (1 + ‖A‖ ^ 2) = B.normDet := by
  rw [← ContinuousLinearMap.normDet_normalGraphL]
  exact hφ.normalGraphEmbedding.hasFDerivWithinAt.normDet_tangentialFDeriv_mul_eq
    (mem_of_mem_nhds hs) ((TauCeti.antilipschitzWith_normalGraphEmbedding φ).domRestrict s)
    (tendsto_volume_inter_closedBall_div_of_mem_nhds hs) Subset.rfl (tendsto_empty_diff_div _) hg

/-- **Tangential Jacobian of the base projection `WithLp.sndL` on a normal graph.** -/
theorem normDet_tangentialFDeriv_sndL_normalGraphEmbedding_image
    (hφ : HasFDerivAt φ A x) (hs : s ∈ 𝓝 x) :
    (TauCeti.tangentialFDeriv (finrank ℝ E) (WithLp.sndL 2 ℝ ℝ E)
        (TauCeti.normalGraphEmbedding φ '' s) (TauCeti.normalGraphEmbedding φ x)).normDet =
      (Real.sqrt (1 + ‖A‖ ^ 2))⁻¹ := by
  have hgf : HasFDerivWithinAt
      ((WithLp.sndL 2 ℝ ℝ E : WithLp 2 (ℝ × E) → E) ∘ TauCeti.normalGraphEmbedding φ)
      (ContinuousLinearMap.id ℝ E) s x := by
    rw [show ((WithLp.sndL 2 ℝ ℝ E : WithLp 2 (ℝ × E) → E) ∘ TauCeti.normalGraphEmbedding φ) = id
      from funext (TauCeti.normalGraphEmbedding_snd φ)]
    exact hasFDerivWithinAt_id x s
  have hmul := hφ.normDet_tangentialFDeriv_normalGraphEmbedding_image_mul hs hgf
  rw [show (ContinuousLinearMap.id ℝ E).normDet = 1 from LinearMap.normDet_id] at hmul
  exact eq_inv_of_mul_eq_one_left hmul

end HasFDerivAt

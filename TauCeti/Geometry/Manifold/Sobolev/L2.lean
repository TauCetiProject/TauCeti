/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Measure.SmoothDensity
public import TauCeti.Geometry.Manifold.Sobolev.Completion
import TauCeti.Analysis.Normed.Lp.PiLp.Basic
import TauCeti.Geometry.Manifold.ContMDiffMap.L2
import TauCeti.MeasureTheory.Function.Lp.ContinuousFunctions

/-!
# The Sobolev space `H⁰(M)` of a compact manifold is `L²(M, μ)`

Let `M` be a compact manifold modelled on `ℝⁿ` and `ψᵢ` finitely many cutoffs in charts `eᵢ`
whose readings `Ψᵢ = ψᵢ ∘ eᵢ` on `M` add up to `1`. The Sobolev space `H^s(M)` of this chart
partition (`TauCeti.chartSobolevSpace`) is the completion of the smooth functions in the norm
`(∑ᵢ ‖ψᵢ · (u ∘ eᵢ⁻¹)‖²_{H^s})^{1/2}`. Let `μ` be a finite measure on `M` with a smooth positive
density (`TauCeti.HasSmoothPositiveDensity`), such as a Riemannian volume. This file shows that at
order `s = 0` the chart norm and the `L²(μ)` norm are equivalent on smooth functions:

`c ‖u‖_{L²(μ)} ≤ (∑ᵢ ‖ψᵢ · (u ∘ eᵢ⁻¹)‖²_{L²})^{1/2} ≤ C ‖u‖_{L²(μ)}`

(`TauCeti.exists_norm_chartReading_zero_le_norm_toLp` and
`TauCeti.exists_norm_toLp_le_norm_chartReading_zero`).
Since the smooth functions are dense in both spaces (`ContMDiffMap.denseRange_toL2`), the identity
of smooth functions extends to an isomorphism of Banach spaces `H⁰(M) ≃ L²(M, μ)`
(`TauCeti.chartSobolevSpaceZeroEquivLp`). It is not an isometry: the chart norm depends on the
partition, while the `L²(μ)` norm depends on `μ`.

The `L²(μ)` inner product `∫ ⟪u, v⟫ dμ` is the one in which formal adjoints are taken, so this
isomorphism lets the formal adjoint of an operator on smooth functions act on the Hilbert space
`H⁰(M)` of the chart partition, as needed to describe the cokernel of an elliptic operator.
For `s ≥ 0` the space `H^s(M)` is a subspace of `L²(M, μ)` (`TauCeti.chartSobolevToLp`, injective
by `TauCeti.chartSobolevToLp_injective`), and if `Q` is a formal adjoint of `P` for `μ`, then any
extensions of `P` and `Q` to the Sobolev scale are adjoint for the `L²` inner product
(`TauCeti.inner_chartSobolevToLp_eq_of_forall_integral_inner_eq`).

The bounds are local, and hold in every `Lᵖ` (`TauCeti.exists_eLpNorm_cutoffPushforwardSchwartz_le`,
`TauCeti.exists_eLpNorm_mulLeft_ofReal_cutoffPullback_le`). In a chart `e` where `μ` is `ρ(y) dy`,
the density `ρ` is bounded above and below by positive constants on the compact support `K` of the
cutoff `ψ`, so `dy` and `ρ dy` dominate each other on `K`. For the upper bound, the reading
`ψ · (u ∘ e⁻¹)` is supported in `K`, where its `Lᵖ(dy)` norm is controlled by its `Lᵖ(ρ dy)` norm,
which is the `Lᵖ(μ)` norm of `(ψ ∘ e) u`, at most `sup |ψ|` times that of `u`.
For the lower bound, `u = ∑ᵢ Ψᵢ u`, and the `Lᵖ(μ)` norm of `Ψᵢ u` is the `Lᵖ(ρ dy)` norm of the
reading `ψᵢ · (u ∘ eᵢ⁻¹)`, supported in `K`, where it is controlled by its `Lᵖ(dy)` norm.

## Main results

* `TauCeti.exists_eLpNorm_cutoffPushforwardSchwartz_le`,
  `TauCeti.exists_eLpNorm_mulLeft_ofReal_cutoffPullback_le`: reading a function in a chart through
  a cutoff is bounded in `Lᵖ`, in both directions.
* `TauCeti.exists_norm_chartReading_zero_le_norm_toLp`: the chart norm of order `0` is bounded by
  the `L²(μ)` norm.
* `TauCeti.exists_norm_toLp_le_norm_chartReading_zero`: for a chart partition, the `L²(μ)` norm is
  bounded by the chart norm of order `0`.
* `TauCeti.chartSobolevSpaceZeroEquivLp`: the isomorphism `H⁰(M) ≃ L²(M, μ)` extending the
  identity of smooth functions (`TauCeti.chartSobolevSpaceZeroEquivLp_toChartSobolevSpace`).
* `TauCeti.chartSobolevToLp`: the injection `H^s(M) → L²(M, μ)` for `s ≥ 0`.
* `TauCeti.inner_chartSobolevToLp_eq_of_forall_integral_inner_eq`: extensions of formally adjoint
  operators are adjoint in `L²(μ)`.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §3
  (Sobolev spaces on compact manifolds, defined through a partition of unity and charts).
-/

public section

noncomputable section

open Set MeasureTheory OpenPartialHomeomorph
open scoped ContDiff Manifold Distributions SchwartzMap BesselPotentialSpace ENNReal NNReal

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [MeasurableSpace M] [BorelSpace M] {μ : Measure M}

/-! ### Comparisons in one chart -/

section Chart

variable [IsFiniteMeasureOnCompacts μ] (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ)
  {e : OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)

include hμ in
/-- **Reading a function in a chart is bounded in `Lᵖ`.** For a measure `μ` with smooth positive
density and a cutoff `ψ` in a chart `e`, the `Lᵖ` norm of the reading `ψ · (u ∘ e⁻¹)` of a smooth
function `u` is bounded by a constant times the `Lᵖ(μ)` norm of `u`. -/
theorem exists_eLpNorm_cutoffPushforwardSchwartz_le (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (p : ℝ≥0∞) :
    ∃ C : ℝ≥0, ∀ u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      eLpNorm (e.cutoffPushforwardSchwartz he ψ u) p volume ≤ C * eLpNorm u p μ := by
  obtain ⟨a, -, ha, -, hle, -⟩ :=
    hμ.exists_measure_le_smul he ψ.hasCompactSupport.isCompact ψ.tsupport_subset
  obtain ⟨A, hA⟩ := ψ.continuous.bounded_above_of_compact_support ψ.hasCompactSupport
  have he' : AEMeasurable e (μ.restrict e.source) :=
    e.continuousOn.aemeasurable e.open_source.measurableSet
  refine ⟨(a ^ (1 / p).toReal).toNNReal * A.toNNReal, fun u ↦ ?_⟩
  set F := e.cutoffPushforwardSchwartz he ψ u
  have hF : AEStronglyMeasurable F ((μ.restrict e.source).map e) :=
    F.continuous.aestronglyMeasurable
  -- On the chart source, `|F ∘ e| ≤ A |u|`.
  have hFe : ∀ᵐ x ∂μ.restrict e.source, ‖(F ∘ e) x‖ ≤ A * ‖u x‖ := by
    refine (ae_restrict_iff' e.open_source.measurableSet).2 (.of_forall fun x hx ↦ ?_)
    rw [Function.comp_apply, cutoffPushforwardSchwartz_apply, e.left_inv hx, norm_smul]
    exact mul_le_mul_of_nonneg_right (hA _) (norm_nonneg _)
  calc eLpNorm F p volume = eLpNorm F p (volume.restrict (tsupport ψ)) :=
        (eLpNorm_restrict_eq_of_support_subset F.continuous.aestronglyMeasurable
          (support_cutoffPushforwardSchwartz_subset he ψ u)).symm
    _ ≤ a ^ (1 / p).toReal • eLpNorm F p ((μ.restrict e.source).map e) :=
        eLpNorm_le_of_measure_le_smul hle
    _ = a ^ (1 / p).toReal • eLpNorm (F ∘ e) p (μ.restrict e.source) := by
        rw [eLpNorm_map_measure hF he']
    _ ≤ a ^ (1 / p).toReal • (ENNReal.ofReal A * eLpNorm u p (μ.restrict e.source)) := by
        gcongr
        exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hF.comp_aemeasurable he') hFe p
    _ ≤ a ^ (1 / p).toReal • (ENNReal.ofReal A * eLpNorm u p μ) := by
        grw [eLpNorm_restrict_le (u : M → ℂ) p μ e.source]
    _ = _ := by
        rw [ENNReal.coe_mul, ENNReal.coe_toNNReal
          (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ha), ENNReal.ofNNReal_toNNReal,
          smul_eq_mul, mul_assoc]

include hμ in
/-- **A function is bounded in `Lᵖ` by its reading in a chart.** For a measure `μ` with smooth
positive density and a cutoff `ψ` in a chart `e`, the `Lᵖ(μ)` norm of `(ψ ∘ e) · u`, for a smooth
function `u` on `M`, is bounded by a constant times the `Lᵖ` norm of the reading `ψ · (u ∘ e⁻¹)`. -/
theorem exists_eLpNorm_mulLeft_ofReal_cutoffPullback_le (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (p : ℝ≥0∞) :
    ∃ C : ℝ≥0, ∀ u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      eLpNorm (LinearMap.mulLeft ℂ (ContMDiffMap.ofReal (e.cutoffPullback he ψ 1)) u) p μ ≤
        C * eLpNorm (e.cutoffPushforwardSchwartz he ψ u) p volume := by
  obtain ⟨-, b, -, hb, -, hle⟩ :=
    hμ.exists_measure_le_smul he ψ.hasCompactSupport.isCompact ψ.tsupport_subset
  have he' : AEMeasurable e (μ.restrict e.source) :=
    e.continuousOn.aemeasurable e.open_source.measurableSet
  refine ⟨(b ^ (1 / p).toReal).toNNReal, fun u ↦ ?_⟩
  set F := e.cutoffPushforwardSchwartz he ψ u
  set G := LinearMap.mulLeft ℂ (ContMDiffMap.ofReal (e.cutoffPullback he ψ 1)) u
  have hG (x : M) : G x = (e.cutoffPullback he ψ 1 x : ℂ) * u x := by
    simp [G]
  have hGsupp : Function.support G ⊆ e.source := fun x hx ↦ by
    by_contra h
    exact hx (by rw [hG, cutoffPullback_apply_of_notMem he _ _ h, Complex.ofReal_zero, zero_mul])
  calc eLpNorm G p μ = eLpNorm G p (μ.restrict e.source) :=
        (eLpNorm_restrict_eq_of_support_subset
          G.contMDiff.continuous.aestronglyMeasurable hGsupp).symm
    _ = eLpNorm (F ∘ e) p (μ.restrict e.source) := by
        refine eLpNorm_congr_ae ((ae_restrict_iff' e.open_source.measurableSet).2
          (.of_forall fun x hx ↦ ?_))
        rw [hG, Function.comp_apply, cutoffPushforwardSchwartz_apply_eq_of_mem he ψ u hx]
    _ = eLpNorm F p ((μ.restrict e.source).map e) :=
        (eLpNorm_map_measure F.continuous.aestronglyMeasurable he').symm
    _ = eLpNorm F p (((μ.restrict e.source).map e).restrict (tsupport ψ)) :=
        (eLpNorm_restrict_eq_of_support_subset F.continuous.aestronglyMeasurable
          (support_cutoffPushforwardSchwartz_subset he ψ u)).symm
    _ ≤ b ^ (1 / p).toReal • eLpNorm F p volume := eLpNorm_le_of_measure_le_smul hle
    _ = _ := by
        rw [ENNReal.coe_toNNReal (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hb),
          smul_eq_mul]

end Chart

/-! ### Comparison of the norms on a compact manifold -/

variable [CompactSpace M] [IsFiniteMeasure μ] {ι : Type*} [Fintype ι]
  {e : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
  (ψ : ∀ i, 𝓓(⟨(e i).target, (e i).open_target⟩, ℝ))

/-- **The chart norm of order `0` is bounded by the `L²(μ)` norm.** For a measure `μ` with a smooth
positive density and finitely many cutoffs `ψᵢ` in charts `eᵢ`, there is a constant `C` such that
every smooth `u` on `M` satisfies

`(∑ᵢ ‖ψᵢ · (u ∘ eᵢ⁻¹)‖²_{L²})^{1/2} ≤ C ‖u‖_{L²(μ)}`. -/
theorem exists_norm_chartReading_zero_le_norm_toLp
    (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ) :
    ∃ C, ∀ u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ‖chartReading he ψ 0 u‖ ≤ C * ‖ContinuousMap.toLp 2 μ ℂ (u : C(M, ℂ))‖ := by
  choose C hC using fun i ↦ exists_eLpNorm_cutoffPushforwardSchwartz_le hμ (he i) (ψ i) 2
  refine ⟨∑ i, (C i : ℝ), fun u ↦ ?_⟩
  have hu := (ContinuousMap.memLp (p := 2) (μ := μ) ℂ (u : C(M, ℂ))).eLpNorm_ne_top
  rw [ContinuousMap.norm_toLp, Finset.sum_mul]
  refine (PiLp.norm_le_sum_norm _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [chartReading_apply, SchwartzMap.norm_toBesselPotentialSpaceCLM_zero, ← ENNReal.coe_toReal,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hu) (hC i u)

/-- **The `L²(μ)` norm is bounded by the chart norm of order `0`.** For a measure `μ` with a
smooth positive density and cutoffs `ψᵢ` in charts `eᵢ` whose readings on `M` add up to `1`, there
is a constant `C` such that every smooth `u` on `M` satisfies

`‖u‖_{L²(μ)} ≤ C (∑ᵢ ‖ψᵢ · (u ∘ eᵢ⁻¹)‖²_{L²})^{1/2}`. -/
theorem exists_norm_toLp_le_norm_chartReading_zero
    (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ)
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1) :
    ∃ C, ∀ u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ‖ContinuousMap.toLp 2 μ ℂ (u : C(M, ℂ))‖ ≤ C * ‖chartReading he ψ 0 u‖ := by
  choose C hC using fun i ↦ exists_eLpNorm_mulLeft_ofReal_cutoffPullback_le hμ (he i) (ψ i) 2
  refine ⟨∑ i, (C i : ℝ), fun u ↦ ?_⟩
  -- `u = ∑ᵢ Ψᵢ u` with `Ψᵢ = ψᵢ ∘ eᵢ`.
  have hsum : (u : M → ℂ) = ∑ i, fun x ↦ ((e i).cutoffPullback (he i) (ψ i) 1 x : ℂ) * u x := by
    ext x
    rw [Finset.sum_apply, ← Finset.sum_mul, ← Complex.ofReal_sum, hψ x, Complex.ofReal_one,
      one_mul]
  have hpiece (i : ι) : eLpNorm (fun x ↦ ((e i).cutoffPullback (he i) (ψ i) 1 x : ℂ) * u x) 2 μ =
      eLpNorm (LinearMap.mulLeft ℂ
        (ContMDiffMap.ofReal ((e i).cutoffPullback (he i) (ψ i) 1)) u) 2 μ := by
    congr 1
    ext x
    simp
  have hw (i : ι) : eLpNorm ((e i).cutoffPushforwardSchwartz (he i) (ψ i) u) 2 volume ≠ ⊤ :=
    ((e i).cutoffPushforwardSchwartz (he i) (ψ i) u).memLp 2 volume |>.eLpNorm_ne_top
  have hle : eLpNorm u 2 μ ≤
      ∑ i, C i * eLpNorm ((e i).cutoffPushforwardSchwartz (he i) (ψ i) u) 2 volume := by
    calc eLpNorm u 2 μ
        = eLpNorm (∑ i, fun x ↦ ((e i).cutoffPullback (he i) (ψ i) 1 x : ℂ) * u x) 2 μ := by
          rw [← hsum]
      _ ≤ _ := (eLpNorm_sum_le one_le_two).trans
          (Finset.sum_le_sum fun i _ ↦ (hpiece i).trans_le (hC i u))
  rw [ContinuousMap.norm_toLp, Finset.sum_mul]
  refine (ENNReal.toReal_mono
    (ENNReal.sum_ne_top.2 fun i _ ↦ ENNReal.mul_ne_top ENNReal.coe_ne_top (hw i)) hle).trans ?_
  rw [ENNReal.toReal_sum fun i _ ↦ ENNReal.mul_ne_top ENNReal.coe_ne_top (hw i)]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ← SchwartzMap.norm_toBesselPotentialSpaceCLM_zero,
    ← chartReading_apply]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ i) (C i).coe_nonneg

/-! ### The isomorphism `H⁰(M) ≃ L²(M, μ)` -/

variable [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]

variable (μ) in
/-- **`H⁰(M)` is `L²(M, μ)`.** For a chart partition of a compact manifold, whose cutoffs read on
`M` add up to `1`, and a finite measure `μ` with a smooth positive density, the Sobolev space
`H⁰(M)` of the partition is isomorphic as a Banach space to `L²(M, μ)`, through the isomorphism
that sends the chart readings of a smooth function to its class in `L²(M, μ)`
(`TauCeti.chartSobolevSpaceZeroEquivLp_toChartSobolevSpace`). -/
def chartSobolevSpaceZeroEquivLp (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ)
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1) :
    chartSobolevSpace he ψ 0 ≃L[ℂ] Lp ℂ 2 μ :=
  (LinearEquiv.refl ℂ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯).extend
    (toChartSobolevSpace he ψ 0) (ContMDiffMap.toL2 μ) (denseRange_toChartSobolevSpace he ψ 0)
    (by simpa using exists_norm_toLp_le_norm_chartReading_zero he ψ hμ hψ)
    (ContMDiffMap.denseRange_toL2 μ)
    (by simpa using exists_norm_chartReading_zero_le_norm_toLp he ψ hμ)

@[simp]
theorem chartSobolevSpaceZeroEquivLp_toChartSobolevSpace
    (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ)
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1)
    (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    chartSobolevSpaceZeroEquivLp μ he ψ hμ hψ (toChartSobolevSpace he ψ 0 u) =
      ContinuousMap.toLp 2 μ ℂ (u : C(M, ℂ)) := by
  rw [chartSobolevSpaceZeroEquivLp, LinearEquiv.extend_eq, LinearEquiv.refl_apply,
    ContMDiffMap.toL2_apply]

@[simp]
theorem chartSobolevSpaceZeroEquivLp_symm_toLp
    (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ)
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1)
    (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (chartSobolevSpaceZeroEquivLp μ he ψ hμ hψ).symm (ContinuousMap.toLp 2 μ ℂ (u : C(M, ℂ))) =
      toChartSobolevSpace he ψ 0 u := by
  rw [← chartSobolevSpaceZeroEquivLp_toChartSobolevSpace he ψ hμ hψ u,
    ContinuousLinearEquiv.symm_apply_apply]

/-! ### The Sobolev spaces of nonnegative order in `L²(M, μ)` -/

section ToLp

variable (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ)
  (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1)

variable (μ) in
/-- For `s ≥ 0`, the Sobolev space `H^s(M)` of a chart partition as a subspace of `L²(M, μ)`: the
inclusion `H^s(M) ⊆ H⁰(M)` followed by the isomorphism `H⁰(M) ≃ L²(M, μ)`. It is injective
(`TauCeti.chartSobolevToLp_injective`) and sends the chart readings of a smooth function to its
class in `L²` (`TauCeti.chartSobolevToLp_toChartSobolevSpace`). -/
def chartSobolevToLp {s : ℝ} (hs : 0 ≤ s) : chartSobolevSpace he ψ s →L[ℂ] Lp ℂ 2 μ :=
  (chartSobolevSpaceZeroEquivLp μ he ψ hμ hψ : chartSobolevSpace he ψ 0 →L[ℂ] Lp ℂ 2 μ) ∘L
    chartSobolevInclusion he ψ hs

/-- `TauCeti.chartSobolevToLp` is the inclusion `H^s(M) ⊆ H⁰(M)` followed by `H⁰(M) ≃ L²(M, μ)`. -/
theorem chartSobolevToLp_apply {s : ℝ} (hs : 0 ≤ s) (x : chartSobolevSpace he ψ s) :
    chartSobolevToLp μ he ψ hμ hψ hs x =
      chartSobolevSpaceZeroEquivLp μ he ψ hμ hψ (chartSobolevInclusion he ψ hs x) :=
  (rfl)

/-- `TauCeti.chartSobolevToLp` sends the chart readings of a smooth function to its class in `L²`.
-/
@[simp]
theorem chartSobolevToLp_toChartSobolevSpace {s : ℝ} (hs : 0 ≤ s)
    (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    chartSobolevToLp μ he ψ hμ hψ hs (toChartSobolevSpace he ψ s u) =
      ContinuousMap.toLp 2 μ ℂ (u : C(M, ℂ)) := by
  simp [chartSobolevToLp]

/-- On `H⁰(M)`, `TauCeti.chartSobolevToLp` is the isomorphism `H⁰(M) ≃ L²(M, μ)`. -/
@[simp]
theorem chartSobolevToLp_zero :
    chartSobolevToLp μ he ψ hμ hψ (le_refl (0 : ℝ)) =
      (chartSobolevSpaceZeroEquivLp μ he ψ hμ hψ : chartSobolevSpace he ψ 0 →L[ℂ] Lp ℂ 2 μ) := by
  rw [chartSobolevToLp, chartSobolevInclusion_self, ContinuousLinearMap.one_def,
    ContinuousLinearMap.comp_id]

/-- For `s ≥ 0`, an element of `H^s(M)` is determined by its image in `L²(M, μ)`. -/
theorem chartSobolevToLp_injective {s : ℝ} (hs : 0 ≤ s) :
    Function.Injective (chartSobolevToLp μ he ψ hμ hψ hs) :=
  (chartSobolevSpaceZeroEquivLp μ he ψ hμ hψ).injective.comp
    (chartSobolevInclusion_injective he ψ hs)

/-- **Formal adjoints are adjoint in `L²`.** Let `Q` be a formal adjoint of `P` for `μ`:
`∫ ⟪P u, v⟫ dμ = ∫ ⟪u, Q v⟫ dμ` for all smooth `u`, `v`. If `A : H^s(M) → H^t(M)` and
`B : H^{s'}(M) → H^{t'}(M)` are continuous extensions of `P` and `Q`, all four orders being
nonnegative, then `⟪A x, y⟫ = ⟪x, B y⟫` in `L²(M, μ)` for all `x ∈ H^s(M)` and `y ∈ H^{s'}(M)`.
For a formally self-adjoint operator `P` of order `m ≥ 0`, extended to `H^m(M) → H⁰(M)`, this
says that its realization in `L²(M, μ)` with domain `H^m(M)` is symmetric. -/
theorem inner_chartSobolevToLp_eq_of_forall_integral_inner_eq
    {P Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hPQ : ∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ∫ x, inner ℂ (P u x) (v x) ∂μ = ∫ x, inner ℂ (u x) (Q v x) ∂μ)
    {s t s' t' : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hs' : 0 ≤ s') (ht' : 0 ≤ t')
    {A : chartSobolevSpace he ψ s →L[ℂ] chartSobolevSpace he ψ t}
    (hA : ∀ u, A (toChartSobolevSpace he ψ s u) = toChartSobolevSpace he ψ t (P u))
    {B : chartSobolevSpace he ψ s' →L[ℂ] chartSobolevSpace he ψ t'}
    (hB : ∀ v, B (toChartSobolevSpace he ψ s' v) = toChartSobolevSpace he ψ t' (Q v))
    (x : chartSobolevSpace he ψ s) (y : chartSobolevSpace he ψ s') :
    inner ℂ (chartSobolevToLp μ he ψ hμ hψ ht (A x)) (chartSobolevToLp μ he ψ hμ hψ hs' y) =
      inner ℂ (chartSobolevToLp μ he ψ hμ hψ hs x) (chartSobolevToLp μ he ψ hμ hψ ht' (B y)) := by
  -- Both sides are continuous in `x` and `y`, and agree on smooth functions.
  refine (denseRange_toChartSobolevSpace he ψ s).induction_on x
    (isClosed_eq (by fun_prop) (by fun_prop)) fun u ↦ ?_
  refine (denseRange_toChartSobolevSpace he ψ s').induction_on y
    (isClosed_eq (by fun_prop) (by fun_prop)) fun v ↦ ?_
  simp only [hA, hB, chartSobolevToLp_toChartSobolevSpace, ← ContMDiffMap.toL2_apply,
    ContMDiffMap.inner_toL2, hPQ]

end ToLp

end TauCeti

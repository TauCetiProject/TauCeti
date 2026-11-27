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

The bounds are local. In a chart `e` where `μ` is `ρ(y) dy`, the density `ρ` is bounded above and
below by positive constants on the compact support `K` of the cutoff `ψ`, so `dy` and `ρ dy`
dominate each other on `K`. For the upper bound, the reading `ψ · (u ∘ e⁻¹)` is supported in `K`,
where its `L²(dy)` norm is controlled by its `L²(ρ dy)` norm, which is the `L²(μ)` norm of
`(ψ ∘ e) u`, at most `sup |ψ|` times that of `u`.
For the lower bound, `u = ∑ᵢ Ψᵢ u`, and the `L²(μ)` norm of `Ψᵢ u` is the `L²(ρ dy)` norm of the
reading `ψᵢ · (u ∘ eᵢ⁻¹)`, supported in `K`, where it is controlled by its `L²(dy)` norm.

## Main results

* `TauCeti.exists_norm_chartReading_zero_le_norm_toLp`: the chart norm of order `0` is bounded by
  the `L²(μ)` norm.
* `TauCeti.exists_norm_toLp_le_norm_chartReading_zero`: for a chart partition, the `L²(μ)` norm is
  bounded by the chart norm of order `0`.
* `TauCeti.chartSobolevSpaceZeroEquivLp`: the isomorphism `H⁰(M) ≃ L²(M, μ)` extending the
  identity of smooth functions (`TauCeti.chartSobolevSpaceZeroEquivLp_toChartSobolevSpace`).

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §3
  (Sobolev spaces on compact manifolds, defined through a partition of unity and charts).
-/

public section

noncomputable section

open Set MeasureTheory OpenPartialHomeomorph
open scoped ContDiff Manifold Distributions SchwartzMap BesselPotentialSpace ENNReal

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [MeasurableSpace M] [BorelSpace M] {μ : Measure M}

/-! ### Comparisons in one chart -/

section Chart

variable {e : OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
  (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))

include he

/-- **Upper bound in a chart.** The `L²` norm of the reading `ψ · (u ∘ e⁻¹)` is at most a constant
times the `L²(μ)` norm of `u`. -/
private theorem exists_eLpNorm_cutoffPushforwardSchwartz_le [IsFiniteMeasureOnCompacts μ]
    (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      eLpNorm (e.cutoffPushforwardSchwartz he ψ u) 2 volume ≤ C * eLpNorm u 2 μ := by
  obtain ⟨c, -, hc, -, hcμ, -⟩ :=
    hμ.exists_measure_le_smul he ψ.hasCompactSupport.isCompact ψ.tsupport_subset
  obtain ⟨B, hB⟩ := ψ.continuous.bounded_above_of_compact_support ψ.hasCompactSupport
  refine ⟨c ^ (1 / (2 : ℝ≥0∞)).toReal * ENNReal.ofReal B, by finiteness, fun u ↦ ?_⟩
  set w := e.cutoffPushforwardSchwartz he ψ u
  have hw : AEStronglyMeasurable w volume := w.continuous.aestronglyMeasurable
  have he' : AEMeasurable e (μ.restrict e.source) :=
    e.continuousOn.aemeasurable e.open_source.measurableSet
  -- `w (e x) = ψ (e x) u x` on the chart source, of norm at most `B ‖u x‖`.
  have hwe : ∀ᵐ x ∂μ.restrict e.source, ‖(w ∘ e) x‖ ≤ B * ‖u x‖ := by
    filter_upwards [ae_restrict_mem e.open_source.measurableSet] with x hx
    rw [Function.comp_apply, cutoffPushforwardSchwartz_apply, e.left_inv hx, norm_smul]
    exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  calc eLpNorm w 2 volume
      = eLpNorm w 2 (volume.restrict (tsupport ψ)) :=
        (eLpNorm_restrict_eq_of_support_subset hw
          (support_cutoffPushforwardSchwartz_subset he ψ u)).symm
    _ ≤ c ^ (1 / (2 : ℝ≥0∞)).toReal • eLpNorm w 2 ((μ.restrict e.source).map e) :=
        eLpNorm_le_of_measure_le_smul hcμ
    _ = c ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm (w ∘ e) 2 (μ.restrict e.source) := by
        rw [smul_eq_mul, eLpNorm_map_measure w.continuous.aestronglyMeasurable he']
    _ ≤ c ^ (1 / (2 : ℝ≥0∞)).toReal * (ENNReal.ofReal B * eLpNorm u 2 (μ.restrict e.source)) := by
        gcongr
        exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul
          (w.continuous.comp_continuousOn e.continuousOn |>.aestronglyMeasurable
            e.open_source.measurableSet) hwe 2
    _ ≤ c ^ (1 / (2 : ℝ≥0∞)).toReal * ENNReal.ofReal B * eLpNorm u 2 μ := by
        rw [mul_assoc]
        gcongr
        exact Measure.restrict_le_self

/-- **Lower bound in a chart.** The `L²(μ)` norm of `(ψ ∘ e) u` is at most a constant times the
`L²` norm of the reading `ψ · (u ∘ e⁻¹)`. -/
private theorem exists_eLpNorm_cutoffPullback_mul_le [IsFiniteMeasureOnCompacts μ]
    (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      eLpNorm (fun x ↦ (e.cutoffPullback he ψ 1 x : ℂ) * u x) 2 μ ≤
        C * eLpNorm (e.cutoffPushforwardSchwartz he ψ u) 2 volume := by
  obtain ⟨-, D, -, hD, -, hDμ⟩ :=
    hμ.exists_measure_le_smul he ψ.hasCompactSupport.isCompact ψ.tsupport_subset
  refine ⟨D ^ (1 / (2 : ℝ≥0∞)).toReal, by finiteness, fun u ↦ ?_⟩
  set w := e.cutoffPushforwardSchwartz he ψ u
  have he' : AEMeasurable e (μ.restrict e.source) :=
    e.continuousOn.aemeasurable e.open_source.measurableSet
  have hF : Continuous fun x ↦ (e.cutoffPullback he ψ 1 x : ℂ) * u x :=
    (Complex.continuous_ofReal.comp (e.cutoffPullback he ψ 1).contMDiff.continuous).mul
      u.contMDiff.continuous
  -- `(ψ ∘ e) u` vanishes off the chart source, and equals `w ∘ e` on it.
  have hFs : Function.support (fun x ↦ (e.cutoffPullback he ψ 1 x : ℂ) * u x) ⊆ e.source :=
    fun x hx ↦ by_contra fun hxs ↦ hx (by simp [cutoffPullback_apply_of_notMem he _ _ hxs])
  have hFw : (fun x ↦ (e.cutoffPullback he ψ 1 x : ℂ) * u x) =ᵐ[μ.restrict e.source] w ∘ e := by
    filter_upwards [ae_restrict_mem e.open_source.measurableSet] with x hx
    exact (cutoffPushforwardSchwartz_apply_eq_of_mem he ψ u hx).symm
  calc eLpNorm (fun x ↦ (e.cutoffPullback he ψ 1 x : ℂ) * u x) 2 μ
      = eLpNorm (w ∘ e) 2 (μ.restrict e.source) := by
        rw [← eLpNorm_restrict_eq_of_support_subset hF.aestronglyMeasurable hFs,
          eLpNorm_congr_ae hFw]
    _ = eLpNorm w 2 (((μ.restrict e.source).map e).restrict (tsupport ψ)) := by
        rw [eLpNorm_restrict_eq_of_support_subset w.continuous.aestronglyMeasurable
          (support_cutoffPushforwardSchwartz_subset he ψ u),
          eLpNorm_map_measure w.continuous.aestronglyMeasurable he']
    _ ≤ D ^ (1 / (2 : ℝ≥0∞)).toReal • eLpNorm w 2 volume := eLpNorm_le_of_measure_le_smul hDμ

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
  choose C hC hCu using fun i ↦ exists_eLpNorm_cutoffPushforwardSchwartz_le (he i) (ψ i) hμ
  refine ⟨∑ i, (C i).toReal, fun u ↦ ?_⟩
  have hu := (ContinuousMap.memLp (p := 2) (μ := μ) ℂ (u : C(M, ℂ))).eLpNorm_ne_top
  rw [ContinuousMap.norm_toLp, Finset.sum_mul]
  refine (PiLp.norm_le_sum_norm _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [chartReading_apply, SchwartzMap.norm_toBesselPotentialSpaceCLM_zero, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (hC i) hu) (hCu i u)

/-- **The `L²(μ)` norm is bounded by the chart norm of order `0`.** For a measure `μ` with a
smooth positive density and cutoffs `ψᵢ` in charts `eᵢ` whose readings on `M` add up to `1`, there
is a constant `C` such that every smooth `u` on `M` satisfies

`‖u‖_{L²(μ)} ≤ C (∑ᵢ ‖ψᵢ · (u ∘ eᵢ⁻¹)‖²_{L²})^{1/2}`. -/
theorem exists_norm_toLp_le_norm_chartReading_zero
    (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ)
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1) :
    ∃ C, ∀ u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ‖ContinuousMap.toLp 2 μ ℂ (u : C(M, ℂ))‖ ≤ C * ‖chartReading he ψ 0 u‖ := by
  choose C hC hCu using fun i ↦ exists_eLpNorm_cutoffPullback_mul_le (he i) (ψ i) hμ
  refine ⟨∑ i, (C i).toReal, fun u ↦ ?_⟩
  -- `u = ∑ᵢ Ψᵢ u` with `Ψᵢ = ψᵢ ∘ eᵢ`.
  have hsum : (u : M → ℂ) = ∑ i, fun x ↦ ((e i).cutoffPullback (he i) (ψ i) 1 x : ℂ) * u x := by
    ext x
    rw [Finset.sum_apply, ← Finset.sum_mul, ← Complex.ofReal_sum, hψ x, Complex.ofReal_one,
      one_mul]
  have hw (i : ι) : eLpNorm ((e i).cutoffPushforwardSchwartz (he i) (ψ i) u) 2 volume ≠ ⊤ :=
    ((e i).cutoffPushforwardSchwartz (he i) (ψ i) u).memLp 2 volume |>.eLpNorm_ne_top
  have hle : eLpNorm u 2 μ ≤
      ∑ i, C i * eLpNorm ((e i).cutoffPushforwardSchwartz (he i) (ψ i) u) 2 volume := by
    calc eLpNorm u 2 μ
        = eLpNorm (∑ i, fun x ↦ ((e i).cutoffPullback (he i) (ψ i) 1 x : ℂ) * u x) 2 μ := by
          rw [← hsum]
      _ ≤ _ := (eLpNorm_sum_le one_le_two).trans (Finset.sum_le_sum fun i _ ↦ hCu i u)
  rw [ContinuousMap.norm_toLp, Finset.sum_mul]
  refine (ENNReal.toReal_mono
    (ENNReal.sum_ne_top.2 fun i _ ↦ ENNReal.mul_ne_top (hC i) (hw i)) hle).trans ?_
  rw [ENNReal.toReal_sum fun i _ ↦ ENNReal.mul_ne_top (hC i) (hw i)]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [ENNReal.toReal_mul, ← SchwartzMap.norm_toBesselPotentialSpaceCLM_zero, ← chartReading_apply]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ i) ENNReal.toReal_nonneg

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

end TauCeti

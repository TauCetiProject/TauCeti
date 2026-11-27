/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Lp
public import TauCeti.Geometry.Manifold.Measure.SmoothDensity
public import TauCeti.Geometry.Manifold.Sobolev.Completion
import TauCeti.Analysis.Normed.Lp.PiLp.Basic
import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz

/-!
# The Sobolev space `H⁰(M)` of a compact manifold is `L²`

Let `M` be a compact manifold modelled on `ℝⁿ` and `μ` a measure on `M` with a smooth positive
density (`TauCeti.HasSmoothPositiveDensity`), for instance the Riemannian volume. Let `ψᵢ` be
finitely many cutoffs in charts `eᵢ` whose readings `ψᵢ ∘ eᵢ` on `M`, extended by `0`, add up to
`1`. The Sobolev spaces `H^s(M)` of this chart partition (`TauCeti.chartSobolevSpace`) are the
closures of the chart readings `(ψᵢ · (u ∘ eᵢ⁻¹))ᵢ` of smooth functions `u` in `⨁ᵢ H^s(ℝⁿ)`. This
file identifies the space of order `0` with `L²(M, μ)`, through the isomorphism that is the
identity on smooth functions (`TauCeti.chartSobolevSpaceZeroEquivLp`):

`H⁰(M) ≃ L²(M, μ)`.

So for `s ≥ 0` the space `H^s(M)` is a subspace of `L²(M, μ)` (`TauCeti.chartSobolevToLp`,
injective by `TauCeti.chartSobolevToLp_injective`), and operators on smooth functions that extend
to the Sobolev scale become operators in the Hilbert space `L²(M, μ)`, where their adjoints,
symmetry and orthogonality to kernels are taken. In particular, if `Q` is a formal adjoint of `P`
for `μ`, that is `∫ ⟪P u, v⟫ dμ = ∫ ⟪u, Q v⟫ dμ` for smooth `u` and `v`, then the extensions of
`P` and `Q` to the Sobolev scale are adjoint for the `L²` inner product
(`TauCeti.inner_chartSobolevToLp_eq_of_forall_integral_inner_eq`). For a formally self-adjoint
elliptic operator of order `m ≥ 0` this is the symmetry of its realization in `L²` with domain
`H^m(M)`.

## The argument

Fix a chart `e` of the maximal atlas and a cutoff `ψ` in it, with support `K` in the chart target.
In the chart, `μ` reads as `ρ(y) dy` for a smooth positive density `ρ`
(`TauCeti.HasSmoothPositiveDensity.exists_map_restrict_source_eq_withDensity`), which is bounded
above and below by positive constants on the compact set `K`. So the Lebesgue measure on `K` and
the reading of `μ` on `K` are each bounded by a multiple of the other
(`TauCeti.HasSmoothPositiveDensity.exists_restrict_le_smul_map_and_map_restrict_le_smul`), and
for every `1 ≤ p ≤ ∞` the `Lᵖ` norm of the reading `ψ · (u ∘ e⁻¹)` and that of `(ψ ∘ e) · u` on
`M` are comparable (`TauCeti.exists_eLpNorm_cutoffPushforwardSchwartz_le`,
`TauCeti.exists_eLpNorm_mulLeft_ofReal_cutoffPullback_le`). The first is bounded by the `Lᵖ(μ)`
norm of `u`, since `|ψ|` is bounded. For the second, `u = ∑ᵢ (ψᵢ ∘ eᵢ) · u`, so the `Lᵖ(μ)` norm
of `u` is bounded by the sum of those of the pieces. Since the `H⁰` norm of a Schwartz function is
its `L²` norm, the chart-reading norm of order `0` and the `L²(μ)` norm are equivalent on smooth
functions. Smooth functions are dense in both spaces (`TauCeti.denseRange_toChartSobolevSpace`,
`ContMDiffMap.denseRange_toLp`), so the identity of smooth functions extends to an isomorphism
(`LinearEquiv.extend`).

## Main definitions

* `TauCeti.chartSobolevSpaceZeroEquivLp`: the isomorphism `H⁰(M) ≃ L²(M, μ)`.
* `TauCeti.chartSobolevToLp`: the injection `H^s(M) → L²(M, μ)` for `s ≥ 0`.

## Main results

* `TauCeti.exists_eLpNorm_cutoffPushforwardSchwartz_le`,
  `TauCeti.exists_eLpNorm_mulLeft_ofReal_cutoffPullback_le`: reading a function in a chart through
  a cutoff is bounded in `Lᵖ`, in both directions.
* `TauCeti.exists_norm_chartReading_zero_le`, `TauCeti.exists_norm_toLp_le`: the chart-reading
  norm of order `0` and the `L²(μ)` norm are equivalent on smooth functions.
* `TauCeti.inner_chartSobolevToLp_eq_of_forall_integral_inner_eq`: extensions of formally adjoint
  operators are adjoint in `L²(μ)`.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §3
  (Sobolev spaces on compact manifolds, defined through a partition of unity and charts).
-/

public section

noncomputable section

open MeasureTheory Set OpenPartialHomeomorph
open scoped ENNReal NNReal ContDiff Manifold Distributions SchwartzMap BesselPotentialSpace

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [MeasurableSpace M] [BorelSpace M] {μ : Measure M}

/-! ### Reading a function in a chart, in `Lᵖ` -/

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
  obtain ⟨a, -, hle, -⟩ := hμ.exists_restrict_le_smul_map_and_map_restrict_le_smul he
    ψ.hasCompactSupport.isCompact ψ.tsupport_subset
  obtain ⟨A, hA⟩ := ψ.continuous.bounded_above_of_compact_support ψ.hasCompactSupport
  have he' : AEMeasurable e (μ.restrict e.source) :=
    e.continuousOn.aemeasurable e.open_source.measurableSet
  refine ⟨((a : ℝ≥0∞) ^ (1 / p).toReal).toNNReal * A.toNNReal, fun u ↦ ?_⟩
  set F := e.cutoffPushforwardSchwartz he ψ u
  have hF : AEStronglyMeasurable F ((μ.restrict e.source).map e) :=
    F.continuous.aestronglyMeasurable
  -- On the chart source, `|F ∘ e| ≤ A |u|`.
  have hFe : ∀ᵐ x ∂μ.restrict e.source, ‖(F ∘ e) x‖ ≤ A * ‖u x‖ := by
    refine (ae_restrict_iff' e.open_source.measurableSet).2 (.of_forall fun x hx ↦ ?_)
    simpa [F, e.cutoffPushforwardSchwartz_apply_of_mem he ψ u hx] using
      mul_le_mul_of_nonneg_right (hA (e x)) (norm_nonneg (u x))
  calc eLpNorm F p volume = eLpNorm F p (volume.restrict (tsupport ψ)) :=
        (eLpNorm_restrict_eq_of_support_subset F.continuous.aestronglyMeasurable
          (e.support_cutoffPushforwardSchwartz_subset he ψ u)).symm
    _ ≤ (a : ℝ≥0∞) ^ (1 / p).toReal • eLpNorm F p ((μ.restrict e.source).map e) :=
        eLpNorm_le_of_measure_le_smul hle
    _ = (a : ℝ≥0∞) ^ (1 / p).toReal • eLpNorm (F ∘ e) p (μ.restrict e.source) := by
        rw [eLpNorm_map_measure hF he']
    _ ≤ (a : ℝ≥0∞) ^ (1 / p).toReal •
          (ENNReal.ofReal A * eLpNorm u p (μ.restrict e.source)) := by
        gcongr
        exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hF.comp_aemeasurable he') hFe p
    _ ≤ (a : ℝ≥0∞) ^ (1 / p).toReal • (ENNReal.ofReal A * eLpNorm u p μ) := by
        grw [eLpNorm_restrict_le (u : M → ℂ) p μ e.source]
    _ = _ := by
        simp [ENNReal.ofNNReal_toNNReal, ENNReal.coe_rpow_of_nonneg, mul_assoc]

include hμ in
/-- **A function is bounded in `Lᵖ` by its reading in a chart.** For a measure `μ` with smooth
positive density and a cutoff `ψ` in a chart `e`, the `Lᵖ(μ)` norm of `(ψ ∘ e) · u`, for a smooth
function `u` on `M`, is bounded by a constant times the `Lᵖ` norm of the reading `ψ · (u ∘ e⁻¹)`. -/
theorem exists_eLpNorm_mulLeft_ofReal_cutoffPullback_le (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (p : ℝ≥0∞) :
    ∃ C : ℝ≥0, ∀ u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      eLpNorm (LinearMap.mulLeft ℂ (ContMDiffMap.ofReal (e.cutoffPullback he ψ 1)) u) p μ ≤
        C * eLpNorm (e.cutoffPushforwardSchwartz he ψ u) p volume := by
  obtain ⟨-, b, -, hle⟩ := hμ.exists_restrict_le_smul_map_and_map_restrict_le_smul he
    ψ.hasCompactSupport.isCompact ψ.tsupport_subset
  have he' : AEMeasurable e (μ.restrict e.source) :=
    e.continuousOn.aemeasurable e.open_source.measurableSet
  refine ⟨((b : ℝ≥0∞) ^ (1 / p).toReal).toNNReal, fun u ↦ ?_⟩
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
        rw [hG, Function.comp_apply, e.cutoffPushforwardSchwartz_apply_of_mem he ψ u hx,
          cutoffPullback_one_apply_of_mem he _ hx]
    _ = eLpNorm F p ((μ.restrict e.source).map e) :=
        (eLpNorm_map_measure F.continuous.aestronglyMeasurable he').symm
    _ = eLpNorm F p (((μ.restrict e.source).map e).restrict (tsupport ψ)) :=
        (eLpNorm_restrict_eq_of_support_subset F.continuous.aestronglyMeasurable
          (e.support_cutoffPushforwardSchwartz_subset he ψ u)).symm
    _ ≤ (b : ℝ≥0∞) ^ (1 / p).toReal • eLpNorm F p volume := eLpNorm_le_of_measure_le_smul hle
    _ = _ := by
        rw [ENNReal.coe_toNNReal (ENNReal.rpow_ne_top_of_nonneg (by positivity)
          ENNReal.coe_ne_top), smul_eq_mul]

end Chart

/-! ### The Sobolev space of order `0` is `L²` -/

section Equiv

variable [CompactSpace M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [IsFiniteMeasure μ]
  (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ) {ι : Type*} [Fintype ι]
  {e : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
  (ψ : ∀ i, 𝓓(⟨(e i).target, (e i).open_target⟩, ℝ))

omit [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
include hμ in
/-- The chart readings of order `0` of a smooth function are bounded by its `L²(μ)` norm. -/
theorem exists_norm_chartReading_zero_le :
    ∃ C, ∀ u, ‖chartReading he ψ 0 u‖ ≤ C * ‖ContMDiffMap.toLp 𝓘(ℝ, CoordinateSpace n) 2 μ u‖ := by
  choose C hC using fun i ↦ exists_eLpNorm_cutoffPushforwardSchwartz_le hμ (he i) (ψ i) 2
  refine ⟨∑ i, (C i : ℝ), fun u ↦ ?_⟩
  rw [ContMDiffMap.norm_toLp, Finset.sum_mul]
  refine (PiLp.norm_le_sum_norm _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [chartReading_apply, SchwartzMap.norm_toBesselPotentialSpaceCLM_zero,
    ← ENNReal.coe_toReal, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top
    (u.contMDiff.continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).eLpNorm_ne_top) (hC i u)

omit [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
include hμ in
/-- The `L²(μ)` norm of a smooth function is bounded by its chart readings of order `0`, for
cutoffs whose readings on `M` add up to `1`. -/
theorem exists_norm_toLp_le (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1) :
    ∃ C, ∀ u, ‖ContMDiffMap.toLp 𝓘(ℝ, CoordinateSpace n) 2 μ u‖ ≤ C * ‖chartReading he ψ 0 u‖ := by
  choose C hC using fun i ↦ exists_eLpNorm_mulLeft_ofReal_cutoffPullback_le hμ (he i) (ψ i) 2
  refine ⟨∑ i, (C i : ℝ), fun u ↦ ?_⟩
  -- `u = ∑ᵢ (ψᵢ ∘ eᵢ) u`, and each piece is bounded by its reading in `eᵢ`.
  have hu : u = ∑ i, LinearMap.mulLeft ℂ
      (ContMDiffMap.ofReal ((e i).cutoffPullback (he i) (ψ i) 1)) u :=
    ContMDiffMap.eq_sum_mulLeft_ofReal _ _ (subset_univ _) fun x _ ↦ hψ x
  conv_lhs => rw [hu]
  rw [map_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  calc ‖ContMDiffMap.toLp 𝓘(ℝ, CoordinateSpace n) 2 μ
        (LinearMap.mulLeft ℂ (ContMDiffMap.ofReal ((e i).cutoffPullback (he i) (ψ i) 1)) u)‖
      ≤ ((C i : ℝ≥0∞) *
          eLpNorm ((e i).cutoffPushforwardSchwartz (he i) (ψ i) u) 2 volume).toReal := by
        rw [ContMDiffMap.norm_toLp]
        exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top
          (SchwartzMap.memLp _ 2 volume).eLpNorm_ne_top) (hC i u)
    _ = C i * ‖chartReading he ψ 0 u i‖ := by
        rw [ENNReal.toReal_mul, ENNReal.coe_toReal, chartReading_apply,
          SchwartzMap.norm_toBesselPotentialSpaceCLM_zero]
    _ ≤ C i * ‖chartReading he ψ 0 u‖ := by
        gcongr
        exact PiLp.norm_apply_le _ _

variable (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1)
include hμ hψ

/-- **The Sobolev space of order `0` is `L²`.** For a measure `μ` with smooth positive density on
a compact manifold and cutoffs `ψᵢ` in charts `eᵢ` whose readings on `M` add up to `1`, the
Sobolev space `H⁰(M)` of the chart partition is isomorphic to `L²(M, μ)`, through the isomorphism
that sends the chart readings of a smooth function to its class in `L²`
(`TauCeti.chartSobolevSpaceZeroEquivLp_toChartSobolevSpace`). -/
def chartSobolevSpaceZeroEquivLp : chartSobolevSpace he ψ 0 ≃L[ℂ] Lp ℂ 2 μ :=
  (LinearEquiv.refl ℂ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯).extend
    (toChartSobolevSpace he ψ 0) (ContMDiffMap.toLp 𝓘(ℝ, CoordinateSpace n) 2 μ)
    (denseRange_toChartSobolevSpace he ψ 0) (by simpa using exists_norm_toLp_le hμ he ψ hψ)
    ContMDiffMap.denseRange_toLp (by simpa using exists_norm_chartReading_zero_le hμ he ψ)

/-- The isomorphism `H⁰(M) ≃ L²(M, μ)` sends the chart readings of a smooth function to its class in
`L²`. -/
@[simp]
theorem chartSobolevSpaceZeroEquivLp_toChartSobolevSpace
    (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    chartSobolevSpaceZeroEquivLp hμ he ψ hψ (toChartSobolevSpace he ψ 0 u) =
      ContMDiffMap.toLp 𝓘(ℝ, CoordinateSpace n) 2 μ u := by
  rw [chartSobolevSpaceZeroEquivLp, LinearEquiv.extend_eq, LinearEquiv.refl_apply]

/-- The inverse isomorphism `L²(M, μ) ≃ H⁰(M)` sends the class of a smooth function to its chart
readings. -/
@[simp]
theorem chartSobolevSpaceZeroEquivLp_symm_toLp
    (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (chartSobolevSpaceZeroEquivLp hμ he ψ hψ).symm
        (ContMDiffMap.toLp 𝓘(ℝ, CoordinateSpace n) 2 μ u) = toChartSobolevSpace he ψ 0 u := by
  rw [chartSobolevSpaceZeroEquivLp, LinearEquiv.extend_symm_eq, LinearEquiv.refl_symm,
    LinearEquiv.refl_apply]

/-- For `s ≥ 0`, the Sobolev space `H^s(M)` of a chart partition as a subspace of `L²(M, μ)`: the
inclusion `H^s(M) ⊆ H⁰(M)` followed by the isomorphism `H⁰(M) ≃ L²(M, μ)`. It is injective
(`TauCeti.chartSobolevToLp_injective`) and sends the chart readings of a smooth function to its
class in `L²` (`TauCeti.chartSobolevToLp_toChartSobolevSpace`). -/
def chartSobolevToLp {s : ℝ} (hs : 0 ≤ s) : chartSobolevSpace he ψ s →L[ℂ] Lp ℂ 2 μ :=
  (chartSobolevSpaceZeroEquivLp hμ he ψ hψ : chartSobolevSpace he ψ 0 →L[ℂ] Lp ℂ 2 μ) ∘L
    chartSobolevInclusion he ψ hs

/-- `TauCeti.chartSobolevToLp` is the inclusion `H^s(M) ⊆ H⁰(M)` followed by `H⁰(M) ≃ L²(M, μ)`. -/
theorem chartSobolevToLp_apply {s : ℝ} (hs : 0 ≤ s) (x : chartSobolevSpace he ψ s) :
    chartSobolevToLp hμ he ψ hψ hs x =
      chartSobolevSpaceZeroEquivLp hμ he ψ hψ (chartSobolevInclusion he ψ hs x) :=
  (rfl)

/-- `TauCeti.chartSobolevToLp` sends the chart readings of a smooth function to its class in `L²`.
-/
@[simp]
theorem chartSobolevToLp_toChartSobolevSpace {s : ℝ} (hs : 0 ≤ s)
    (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    chartSobolevToLp hμ he ψ hψ hs (toChartSobolevSpace he ψ s u) =
      ContMDiffMap.toLp 𝓘(ℝ, CoordinateSpace n) 2 μ u := by
  simp [chartSobolevToLp]

/-- On `H⁰(M)`, `TauCeti.chartSobolevToLp` is the isomorphism `H⁰(M) ≃ L²(M, μ)`. -/
@[simp]
theorem chartSobolevToLp_zero :
    chartSobolevToLp hμ he ψ hψ (le_refl (0 : ℝ)) =
      (chartSobolevSpaceZeroEquivLp hμ he ψ hψ : chartSobolevSpace he ψ 0 →L[ℂ] Lp ℂ 2 μ) := by
  rw [chartSobolevToLp, chartSobolevInclusion_self, ContinuousLinearMap.one_def,
    ContinuousLinearMap.comp_id]

/-- For `s ≥ 0`, an element of `H^s(M)` is determined by its image in `L²(M, μ)`. -/
theorem chartSobolevToLp_injective {s : ℝ} (hs : 0 ≤ s) :
    Function.Injective (chartSobolevToLp hμ he ψ hψ hs) :=
  (chartSobolevSpaceZeroEquivLp hμ he ψ hψ).injective.comp
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
    inner ℂ (chartSobolevToLp hμ he ψ hψ ht (A x)) (chartSobolevToLp hμ he ψ hψ hs' y) =
      inner ℂ (chartSobolevToLp hμ he ψ hψ hs x) (chartSobolevToLp hμ he ψ hψ ht' (B y)) := by
  -- Both sides are continuous in `x` and `y`, and agree on smooth functions.
  refine (denseRange_toChartSobolevSpace he ψ s).induction_on x
    (isClosed_eq (by fun_prop) (by fun_prop)) fun u ↦ ?_
  refine (denseRange_toChartSobolevSpace he ψ s').induction_on y
    (isClosed_eq (by fun_prop) (by fun_prop)) fun v ↦ ?_
  simp only [hA, hB, chartSobolevToLp_toChartSobolevSpace, ContMDiffMap.inner_toLp, hPQ]

end Equiv

end TauCeti

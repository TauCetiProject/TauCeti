/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Geometry.Manifold.ExtChartAt.SelfModel
import TauCeti.MeasureTheory.Measure.Haar.OfBasis

/-!
# The Riemannian volume against a Haar measure in a chart

Let `M` be a manifold modelled on a finite-dimensional real normed space `E`, with a continuous
Riemannian metric, and let `μ` be an additive Haar measure on `E`, for instance Lebesgue measure.
In the preferred chart at `α`, the Riemannian volume is `ρ μ` for the *chart density*
`ρ y = c · TauCeti.chartVolumeDensity α (chart⁻¹ y)`
(`TauCeti.chartHaarDensity`), where the constant `c` compares the Haar measure of
`Module.finBasis ℝ E`, in which `TauCeti.setIntegral_riemannianVolume_of_subset` is stated, with
`μ`. The density is positive on the chart target (`TauCeti.chartHaarDensity_pos`) and `Cⁿ` there
for a `Cⁿ` metric (`TauCeti.contDiffOn_chartHaarDensity`), and a function vanishing off the
points read in an open subset `Q` of the chart target integrates as `∫_Q ρ f(chart⁻¹ y) dμ`
(`TauCeti.integral_riemannianVolume_eq_setIntegral_chartHaarDensity`).

## Main definitions

* `TauCeti.chartHaarDensity`: the density of the Riemannian volume read in a chart, against `μ`.

## Main results

* `TauCeti.chartHaarDensity_pos`, `TauCeti.contDiffOn_chartHaarDensity`: positivity and
  smoothness on the chart target.
* `TauCeti.integral_riemannianVolume_eq_setIntegral_chartHaarDensity`: integration in the chart.
-/

public section

noncomputable section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)] (α : M)

/-- **The chart density of the Riemannian volume** against an additive Haar measure `μ` on the
model: at `y` in the target of the preferred chart at `α`, the chart volume density at the point
read at `y`, times the constant comparing the Haar measure of `Module.finBasis ℝ E` with `μ`. The
Riemannian volume read in the chart is this density times `μ`
(`TauCeti.integral_riemannianVolume_eq_setIntegral_chartHaarDensity`). -/
def chartHaarDensity (y : E) : ℝ :=
  (Measure.addHaarScalarFactor (Module.finBasis ℝ E).addHaar μ : ℝ) *
    chartVolumeDensity (I := 𝓘(ℝ, E)) α ((chartAt E α).symm y)

/-- The chart density is the chart volume density at the point read at `y`, times the constant
comparing the Haar measure of `Module.finBasis ℝ E` with `μ`. -/
theorem chartHaarDensity_def (y : E) :
    chartHaarDensity μ α y =
      (Measure.addHaarScalarFactor (Module.finBasis ℝ E).addHaar μ : ℝ) *
        chartVolumeDensity (I := 𝓘(ℝ, E)) α ((chartAt E α).symm y) :=
  (rfl)

variable {α}

/-- The chart density is positive on the chart target. -/
theorem chartHaarDensity_pos {y : E} (hy : y ∈ (chartAt E α).target) :
    0 < chartHaarDensity μ α y := by
  rw [chartHaarDensity_def]
  exact mul_pos (NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _))
    (chartVolumeDensity_pos _ (by
      simpa only [TangentBundle.trivializationAt_baseSet] using (chartAt E α).map_target hy))

variable (α) in
/-- The chart density of a `Cⁿ` metric is `Cⁿ` on the chart target. -/
theorem contDiffOn_chartHaarDensity {n : ℕ∞ω} [IsManifold 𝓘(ℝ, E) (n + 1) M]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) n E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)] :
    ContDiffOn ℝ n (chartHaarDensity μ α) (chartAt E α).target := by
  have : IsManifold 𝓘(ℝ, E) n M := IsManifold.of_le (n := n + 1) le_self_add
  have h : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) n
      (fun y ↦ chartVolumeDensity (I := 𝓘(ℝ, E)) α ((chartAt E α).symm y)) (chartAt E α).target :=
    (contMDiffOn_chartVolumeDensity α).comp contMDiffOn_chart_symm fun y hy ↦ by
      rw [mem_preimage, TangentBundle.trivializationAt_baseSet]
      exact (chartAt E α).map_target hy
  exact (contDiffOn_const.mul (contMDiffOn_iff_contDiffOn.1 h)).congr fun y _ ↦
    chartHaarDensity_def μ α y

variable [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]

/-- **Integration in a chart against a Haar measure.** If `f` vanishes off the points read in the
preferred chart at `α` inside an open subset `Q` of the chart target, its integral against the
Riemannian volume is the integral over `Q`, against `μ`, of `f` read in the chart weighted by the
chart density. -/
theorem integral_riemannianVolume_eq_setIntegral_chartHaarDensity {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {Q : Set E} (hQ : IsOpen Q)
    (hQt : Q ⊆ (chartAt E α).target) {f : M → G} (hf : ∀ x ∉ (chartAt E α).symm '' Q, f x = 0) :
    ∫ x, f x ∂riemannianVolume 𝓘(ℝ, E) M =
      ∫ y in Q, chartHaarDensity μ α y • f ((chartAt E α).symm y) ∂μ := by
  have hSs : (chartAt E α).symm '' Q ⊆ (chartAt E α).source := by
    rintro _ ⟨y, hy, rfl⟩
    exact (chartAt E α).map_target (hQt hy)
  have hSo : IsOpen ((chartAt E α).symm '' Q) :=
    (chartAt E α).isOpen_image_symm_of_subset_target hQ hQt
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hf,
    setIntegral_riemannianVolume_of_subset hSs hSo.measurableSet,
    extChartAt_modelWithCornersSelf_eq]
  simp only [OpenPartialHomeomorph.coe_toPartialEquiv,
    OpenPartialHomeomorph.coe_toPartialEquiv_symm]
  -- The chart and its underlying partial equivalence are the same function.
  rw [show chartAt E α '' ((chartAt E α).symm '' Q) = Q from
      (chartAt E α).toPartialEquiv.image_symm_image_of_subset_target hQt,
    Module.Basis.setIntegral_addHaar_congr_measurableSpace _ _ _ _ _ _ ‹BorelSpace E›,
    Measure.isAddLeftInvariant_eq_smul (Module.finBasis ℝ E).addHaar μ,
    Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def, ← integral_smul]
  refine setIntegral_congr_fun hQ.measurableSet fun y _ ↦ ?_
  simp only [chartHaarDensity_def, smul_smul]

end TauCeti

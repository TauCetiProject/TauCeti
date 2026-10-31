/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.SquaredDistance
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
-- Private: used only inside proofs.
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Geometry.Manifold.Morse.Hessian

/-!
# Squared distance from almost every point is a Morse function on an immersed manifold

Let `i : M → V` be an immersion of a second-countable boundaryless finite-dimensional manifold
into a finite-dimensional real inner product space. For almost every point `a ∈ V`, with respect
to any Haar measure, the squared distance `x ↦ ‖i x - a‖²` has only nondegenerate critical points:
for a `C²` immersion every critical point is nondegenerate
(`TauCeti.ae_forall_isManifoldNondegenerateCriticalPoint_norm_sq_sub_comp`), and for a smooth
immersion the squared distance is a Morse function (`TauCeti.ae_isMorse_norm_sq_sub_comp`).

No closedness or properness of `i` is needed for genericity. When `i` is a closed embedding the
squared distance is moreover proper (`TauCeti.isProperMap_norm_sq_sub_comp`), and together these
give a proper Morse exhaustion of `M` bounded below. For a holomorphic immersion of a complex
manifold its critical points also have real Morse index at most the complex dimension
(`TauCeti.manifoldMorseIndex_norm_sq_sub_comp_le`), which is Milnor's route to the homotopy type
of affine varieties and Stein manifolds.

The proof reads `i` in countably many charts, where
`TauCeti.ae_hasNondegenerateCriticalPointsOn_norm_sq_sub_comp` applies, and transfers criticality
and nondegeneracy between those charts and the preferred charts of the manifold.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §6, Theorem 6.6, and §7.
-/

public section

open Function MeasureTheory Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M] [SecondCountableTopology M]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {i : M → V}

/-- **The squared distance from almost every point has nondegenerate critical points along a
`C²` immersion.** If `i : M → V` is `C²` with injective differential everywhere, then for almost
every `a ∈ V`, with respect to any Haar measure `μ`, every critical point of `x ↦ ‖i x - a‖²` is
nondegenerate. -/
theorem ae_forall_isManifoldNondegenerateCriticalPoint_norm_sq_sub_comp (μ : Measure V)
    [μ.IsAddHaarMeasure] (hi : ContMDiff I 𝓘(ℝ, V) 2 i)
    (hinj : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) i x)) :
    ∀ᵐ a ∂μ, ∀ x ∈ criticalPoints I (fun y ↦ ‖i y - a‖ ^ 2),
      IsManifoldNondegenerateCriticalPoint I (fun y ↦ ‖i y - a‖ ^ 2) x := by
  -- In each chart, `i` reads as a `C²` map with injective differential on the chart target.
  have hF : ∀ x₀ z, z ∈ (extChartAt I x₀).target →
      ContDiffAt ℝ 2 (i ∘ (extChartAt I x₀).symm) z := fun x₀ z hz ↦ by
    have hy := (extChartAt I x₀).map_target hz
    have h : ContDiffAt ℝ 2 (i ∘ (extChartAt I x₀).symm)
        (extChartAt I x₀ ((extChartAt I x₀).symm z)) :=
      (contMDiffAt_iff_contDiffAt_comp_extend_symm (IsManifold.chart_mem_maximalAtlas x₀)
        (by simpa using hy)).1 (hi _)
    rwa [(extChartAt I x₀).right_inv hz] at h
  have hchart : ∀ x₀, ∀ᵐ a ∂μ, HasNondegenerateCriticalPointsOn
      (fun z ↦ ‖(i ∘ (extChartAt I x₀).symm) z - a‖ ^ 2) (extChartAt I x₀).target := fun x₀ ↦ by
    refine ae_hasNondegenerateCriticalPointsOn_norm_sq_sub_comp μ (isOpen_extChartAt_target x₀)
      (fun z hz ↦ (hF x₀ z hz).contDiffWithinAt) fun z hz ↦ ?_
    have hy := (extChartAt I x₀).map_target hz
    have h := fderiv_comp_extChartAt_symm_injective hy
      (by rw [(extChartAt I x₀).right_inv hz]; exact (hF x₀ z hz).differentiableAt two_ne_zero)
      (hinj _)
    rwa [(extChartAt I x₀).right_inv hz] at h
  -- Countably many chart sources cover `M`.
  obtain ⟨T, hTc, hcover⟩ := TopologicalSpace.countable_cover_nhds
    (fun x : M ↦ extChartAt_source_mem_nhds (I := I) x)
  filter_upwards [(ae_ball_iff hTc).2 fun x₀ _ ↦ hchart x₀] with a ha x hx
  obtain ⟨x₀, hx₀, hxs⟩ := mem_iUnion₂.1 (hcover.symm ▸ mem_univ x)
  have hz := (extChartAt I x₀).map_source hxs
  have hd : DifferentiableAt ℝ ((fun y ↦ ‖i y - a‖ ^ 2) ∘ (extChartAt I x₀).symm)
      (extChartAt I x₀ x) :=
    (ContDiffAt.norm_sq ℝ ((hF x₀ _ hz).sub contDiffAt_const)).differentiableAt two_ne_zero
  have hcrit := (mfderiv_eq_zero_iff_fderiv_comp_extChartAt_symm_eq_zero hxs hd).1
    (mem_criticalPoints_iff_mfderiv_eq_zero.1 hx)
  exact (isManifoldNondegenerateCriticalPoint_iff_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas x₀) (by simpa using hxs)).2
    (hasNondegenerateCriticalPointsOn_iff.1 (ha x₀ hx₀) hz hcrit)

/-- **The squared distance from almost every point is a Morse function on a smoothly immersed
manifold.** If `i : M → V` is smooth with injective differential everywhere, then for almost every
`a ∈ V`, with respect to any Haar measure `μ`, the function `x ↦ ‖i x - a‖²` is Morse. -/
theorem ae_isMorse_norm_sq_sub_comp (μ : Measure V) [μ.IsAddHaarMeasure]
    (hi : ContMDiff I 𝓘(ℝ, V) ∞ i) (hinj : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) i x)) :
    ∀ᵐ a ∂μ, IsMorse I (fun y ↦ ‖i y - a‖ ^ 2) := by
  filter_upwards [ae_forall_isManifoldNondegenerateCriticalPoint_norm_sq_sub_comp μ
    (hi.of_le (by norm_num)) hinj] with a ha
  have hsmooth : ContMDiff I 𝓘(ℝ) ∞ (fun y ↦ ‖i y - a‖ ^ 2) :=
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).comp_contMDiff hi
  rw [← isMorseOn_univ, isMorseOn_iff_criticalPoints]
  exact ⟨hsmooth.contMDiffOn, fun x _ hx ↦ ha x hx⟩

end TauCeti

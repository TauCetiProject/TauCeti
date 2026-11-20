/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
import TauCeti.Analysis.Calculus.Morse.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# Łojasiewicz's gradient inequality on a Riemannian manifold

Let `f` be a function on a manifold `M` carrying a continuous Riemannian metric. The
**Łojasiewicz inequality with exponent `1/2`** near a point `p`,

`lam * |f y - f p| ≤ ‖grad f y‖ ^ 2`,

is the estimate that controls negative gradient trajectories approaching `p`: while a trajectory
stays where it holds, the drop of `f` bounds both the decay of the energy and the length of the
trajectory.

This file transports the inequality from coordinates to the Riemannian gradient. If the coordinate
expression of `f` in the extended chart at `p` satisfies it, then so does the Riemannian gradient
(`TauCeti.exists_mul_abs_sub_le_norm_mgradient_sq_of_comp_extChartAt_symm`), since near `p` the
differential of that expression is bounded by a multiple of the Riemannian length of the gradient
(`TauCeti.Manifold.eventually_norm_fderiv_comp_extChartAt_symm_le_mul_norm_mgradient`). The metric
need not be adapted to the chart, nor smooth. On a boundaryless manifold the coordinate expression
may be taken in any chart of the `C¹` maximal atlas, read through a linear isomorphism
(`TauCeti.exists_mul_abs_sub_le_norm_mgradient_sq_of_mem_maximalAtlas`): the inequality passes to
the extended chart through the `C¹` chart transition
(`TauCeti.exists_mul_abs_sub_le_norm_fderiv_sq_of_comp`).

Near a nondegenerate critical point the coordinate expression satisfies the inequality by
`TauCeti.IsNondegenerateCriticalPoint.exists_mul_abs_sub_le_norm_fderiv_sq`, which gives the
**Morse form of Łojasiewicz's gradient inequality**
(`TauCeti.IsManifoldNondegenerateCriticalPoint.exists_mul_abs_sub_le_norm_mgradient_sq`).

## Main results

* `TauCeti.exists_mul_abs_sub_le_norm_mgradient_sq_of_comp_extChartAt_symm` and
  `TauCeti.exists_mul_abs_sub_le_norm_mgradient_sq_of_mem_maximalAtlas`: the Łojasiewicz
  inequality for the Riemannian gradient follows from the one for the coordinate expression in the
  extended chart, or in any chart of the maximal atlas.
* `TauCeti.IsManifoldNondegenerateCriticalPoint.exists_mul_abs_sub_le_norm_mgradient_sq`: the
  Łojasiewicz inequality with exponent `1/2` near a nondegenerate critical point, for the
  Riemannian gradient.

## References

* S. Łojasiewicz, *Une propriété topologique des sous-ensembles analytiques réels*, Les Équations
  aux Dérivées Partielles, Éditions du CNRS, Paris, 1963, 87--89.
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
-/

public section

open Bundle Filter Set Topology TauCeti.Manifold
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {p : M}

/-- **Łojasiewicz's inequality from a chart.** If the coordinate expression of `f` in the extended
chart at `p` satisfies the Łojasiewicz inequality with exponent `1 / 2` near the chart image of `p`,
then near `p` the absolute energy difference `|f y - f p|` is bounded by a multiple of the squared
Riemannian length of the gradient of `f` at `y`, for any continuous Riemannian metric: near `p` the
coordinate differential is bounded by a multiple of that length. -/
theorem exists_mul_abs_sub_le_norm_mgradient_sq_of_comp_extChartAt_symm {lam : ℝ} (hlam : 0 < lam)
    (hloj : ∀ᶠ x in 𝓝 (extChartAt I p p), lam * |f ((extChartAt I p).symm x) - f p| ≤
      ‖fderiv ℝ (f ∘ (extChartAt I p).symm) x‖ ^ 2) :
    ∃ lam > 0, ∀ᶠ y in 𝓝 p, lam * |f y - f p| ≤ ‖mgradient I f y‖ ^ 2 := by
  obtain ⟨C, hC, hbd⟩ :=
    eventually_norm_fderiv_comp_extChartAt_symm_le_mul_norm_mgradient (I := I) p
  refine ⟨lam / C ^ 2, by positivity, ?_⟩
  filter_upwards [(continuousAt_extChartAt (I := I) p).eventually hloj, hbd,
    extChartAt_source_mem_nhds (I := I) p] with y hy hyb hys
  rw [(extChartAt I p).left_inv hys] at hy
  calc lam / C ^ 2 * |f y - f p| = lam * |f y - f p| / C ^ 2 := by ring
    _ ≤ ‖fderiv ℝ (f ∘ (extChartAt I p).symm) (extChartAt I p y)‖ ^ 2 / C ^ 2 := by gcongr
    _ ≤ (C * ‖mgradient I f y‖) ^ 2 / C ^ 2 := by gcongr; exact hyb f
    _ = ‖mgradient I f y‖ ^ 2 := by field_simp

/-- **Łojasiewicz's inequality from any chart.** Let `e` be a chart of the `C¹` maximal atlas of a
boundaryless manifold at `p`, read through a linear isomorphism `L : E₁ ≃ E` with
`e.extend I p = L z₀`. If `f` is `C¹` at `p` and its coordinate expression `f ∘ e⁻¹ ∘ L` satisfies
the Łojasiewicz inequality with exponent `1 / 2` near `z₀`, then near `p` the absolute energy
difference `|f y - f p|` is bounded by a multiple of the squared Riemannian length of the gradient
of `f` at `y`, for any continuous Riemannian metric. -/
theorem exists_mul_abs_sub_le_norm_mgradient_sq_of_mem_maximalAtlas [I.Boundaryless]
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (hp : p ∈ e.source) (L : E₁ ≃L[ℝ] E) {z₀ : E₁}
    (hz₀ : e.extend I p = L z₀) (hf : ContMDiffAt I 𝓘(ℝ) 1 f p) {lam : ℝ} (hlam : 0 < lam)
    (hloj : ∀ᶠ z in 𝓝 z₀, lam * |f ((e.extend I).symm (L z)) - f p| ≤
      ‖fderiv ℝ (f ∘ (e.extend I).symm ∘ L) z‖ ^ 2) :
    ∃ lam > 0, ∀ᶠ y in 𝓝 p, lam * |f y - f p| ≤ ‖mgradient I f y‖ ^ 2 := by
  obtain ⟨hτ, hτz₀, hσ, hστ, hτσ⟩ :=
    contDiffAt_extChartAt_comp_extend_symm_comp_and_eventually_rightInverse he hp L hz₀
  set κ := extChartAt I p
  set τ := κ ∘ (e.extend I).symm ∘ L
  rw [← hτz₀] at hσ hστ hτσ
  -- The coordinate expression `f ∘ κ⁻¹` is differentiable near `κ p`, and near `z₀` its pullback
  -- by `τ` is the coordinate expression in `e`, which satisfies the inequality.
  have hg : ∀ᶠ x in 𝓝 (τ z₀), DifferentiableAt ℝ (f ∘ κ.symm) x := by
    rw [hτz₀]
    exact (hf.contDiffAt_comp_extChartAt_symm.eventually (by simp)).mono
      fun x hx ↦ hx.differentiableAt (by simp)
  have hpull : (f ∘ κ.symm) ∘ τ =ᶠ[𝓝 z₀] f ∘ (e.extend I).symm ∘ L := by
    have hsrc : κ.source ∈ 𝓝 (((e.extend I).symm ∘ L) z₀) := by
      rw [Function.comp_apply, ← hz₀, e.extend_left_inv hp]
      exact extChartAt_source_mem_nhds p
    have hc : ContinuousAt ((e.extend I).symm ∘ L) z₀ := by
      refine ContinuousAt.comp ?_ L.continuous.continuousAt
      rw [← hz₀]
      exact e.continuousAt_extend_symm hp
    filter_upwards [hc.eventually_mem hsrc] with z hz
    rw [Function.comp_apply] at hz
    simp only [τ, Function.comp_apply]
    rw [κ.left_inv hz]
  have hfp : (f ∘ κ.symm) (τ z₀) = f p := by rw [hτz₀]; exact congrArg f (extChartAt_to_inv p)
  obtain ⟨lam', hlam', hloj'⟩ := exists_mul_abs_sub_le_norm_fderiv_sq_of_comp hlam hτ hσ hστ hτσ
    hg <| by
      filter_upwards [hloj, hpull.eventuallyEq_nhds] with z hz hzpull
      rw [hfp, hzpull.fderiv_eq]
      exact hzpull.self_of_nhds ▸ hz
  refine exists_mul_abs_sub_le_norm_mgradient_sq_of_comp_extChartAt_symm hlam' ?_
  simpa only [hτz₀, Function.comp_apply, κ, extChartAt_to_inv] using hloj'

/-- **The Morse form of Łojasiewicz's gradient inequality on a Riemannian manifold.** Near a
nondegenerate critical point `p` of `f`, the absolute energy difference `|f y - f p|` is bounded by
a multiple of the squared Riemannian length of the gradient of `f` at `y`, for any continuous
Riemannian metric. -/
theorem IsManifoldNondegenerateCriticalPoint.exists_mul_abs_sub_le_norm_mgradient_sq
    (hp : IsManifoldNondegenerateCriticalPoint I f p) :
    ∃ lam > 0, ∀ᶠ y in 𝓝 p, lam * |f y - f p| ≤ ‖mgradient I f y‖ ^ 2 := by
  obtain ⟨lam, hlam, hloj⟩ :=
    ((isManifoldNondegenerateCriticalPoint_iff I).1 hp).exists_mul_abs_sub_le_norm_fderiv_sq
  refine exists_mul_abs_sub_le_norm_mgradient_sq_of_comp_extChartAt_symm hlam ?_
  simpa only [Function.comp_apply, (extChartAt I p).left_inv (mem_extChartAt_source p)] using hloj

end TauCeti

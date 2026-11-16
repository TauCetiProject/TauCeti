/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.BumpFunction
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension

/-!
# Smooth functions as functions of a localized chart

On a finite-dimensional Hausdorff real manifold, multiplying the extended chart at `x` by a bump
function gives a globally smooth map with the chart's germ at `x`. On any finite-dimensional real
manifold, near every interior point of a chart target the chart expression of a smooth real
function agrees with a smooth function on the model space, hence every smooth real function agrees
near an interior point `x` with a smooth function on the model space composed with such a localized
chart. These steps reduce local statements about smooth functions to the model space.

## Main results

* `TauCeti.exists_contMDiffMap_eventuallyEq_extChartAt`: a globally smooth map with the germ of
  the extended chart at `x`.
* `TauCeti.exists_contMDiffMap_comp_eventuallyEq`: near an interior point, every smooth function
  agrees with a smooth function of that localized chart.
* `TauCeti.exists_contDiff_comp_extChartAt_symm_eventuallyEq`: near every interior point of the
  chart target, the chart expression of a smooth function agrees with a smooth function on the
  model space.
-/

public section

open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

/-- **A globally smooth map with the germ of the extended chart.** There is a `C^∞` map `M → E`
that agrees with `extChartAt I x` on a neighbourhood of `x`. -/
theorem exists_contMDiffMap_eventuallyEq_extChartAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] (x : M) :
    ∃ F : C^∞⟮I, M; modelWithCornersSelf ℝ E, E⟯,
      Filter.EventuallyEq (nhds x) (F : M → E) (extChartAt I x) := by
  -- Multiplying the chart by a bump function at `x` leaves its germ there and makes the product
  -- smooth everywhere.
  let b : SmoothBumpFunction I x := Classical.choice inferInstance
  refine ⟨⟨fun y ↦ b y • extChartAt I x y, b.contMDiff_smul contMDiffOn_extChartAt⟩, ?_⟩
  filter_upwards [b.eventuallyEq_one] with y hy
  simp [hy]

/-- **Smooth chart expressions.** Near a point `z` of the interior of the target of the extended
chart at `x`, the chart expression `f ∘ (extChartAt I x).symm` of a smooth function agrees with a
smooth function on the model space. No separation assumption on `M` is needed. -/
theorem exists_contDiff_comp_extChartAt_symm_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {x : M} {z : E} (hz : z ∈ interior (extChartAt I x).target) (f : C^∞⟮I, M; ℝ⟯) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ (f : M → ℝ) ∘ (extChartAt I x).symm =ᶠ[nhds z] g := by
  -- The chart expression is smooth on the interior of the chart target, and its germ there extends
  -- to the model space, so no separation assumption on `M` is needed.
  have hsmooth : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ((f : M → ℝ) ∘ (extChartAt I x).symm)
      (interior (extChartAt I x).target) := fun y hy ↦
    (f.contMDiff.contMDiffAt.comp_contMDiffWithinAt y
      (contMDiffWithinAt_extChartAt_symm_target x (interior_subset hy))).mono interior_subset
  obtain ⟨G, hG⟩ := hsmooth.exists_contMDiffMap_eventuallyEq (isOpen_interior.mem_nhds hz)
  exact ⟨G, G.contMDiff.contDiff, hG.symm⟩

/-- **A smooth function factors through the chart near an interior point.** If `F` has the germ of
the extended chart at an interior point `x`, then every `f : C^∞⟮I, M; ℝ⟯` agrees near `x` with
`g' ∘ F` for some `C^∞` function `g'` on the model space. -/
theorem exists_contMDiffMap_comp_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {x : M} (hx : I.IsInteriorPoint x) (F : C^∞⟮I, M; modelWithCornersSelf ℝ E, E⟯)
    (hF : Filter.EventuallyEq (nhds x) (F : M → E) (extChartAt I x))
    (f : C^∞⟮I, M; ℝ⟯) :
    ∃ g' : C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯,
      Filter.EventuallyEq (nhds x) (f : M → ℝ) (g' ∘ F) := by
  obtain ⟨g, hg, hfg⟩ := exists_contDiff_comp_extChartAt_symm_eventuallyEq
    ((ModelWithCorners.isInteriorPoint_iff (I := I)).mp hx) f
  refine ⟨⟨g, hg.contMDiff⟩, ?_⟩
  have hFx : F x = extChartAt I x x := hF.eq_of_nhds
  have hFt : Filter.Tendsto (F : M → E) (nhds x) (nhds (extChartAt I x x)) :=
    hFx ▸ F.contMDiff.continuous.continuousAt
  have hsource : ∀ᶠ y in nhds x, y ∈ (extChartAt I x).source :=
    (isOpen_extChartAt_source x).mem_nhds (mem_extChartAt_source x)
  -- Pull the chart expression back along `F`, which agrees with the chart on its source.
  filter_upwards [hfg.comp_tendsto hFt, hF, hsource] with y hgy hFy hy
  simp only [Function.comp_apply] at hgy
  simp only [Function.comp_apply, ContMDiffMap.coeFn_mk]
  rw [hFy] at hgy ⊢
  rwa [(extChartAt I x).left_inv hy] at hgy

/-- **Chart expressions of local factorizations.** Near an interior point `x`, if `f` agrees with
`g ∘ F` for a map `F` with the germ of the extended chart, then the chart expression
`f ∘ (extChartAt I x).symm` agrees with `g` near `extChartAt I x x`. -/
theorem comp_extChartAt_symm_eventuallyEq_of_eventuallyEq_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {Y : Type*}
    {x : M} (hx : I.IsInteriorPoint x) {F : M → E} (hF : F =ᶠ[nhds x] extChartAt I x)
    {f : M → Y} {g : E → Y} (hg : f =ᶠ[nhds x] g ∘ F) :
    f ∘ (extChartAt I x).symm =ᶠ[nhds (extChartAt I x x)] g := by
  have htarget : (extChartAt I x).target ∈ nhds (extChartAt I x x) :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds
      ((ModelWithCorners.isInteriorPoint_iff (I := I)).mp hx)) interior_subset
  have hsymm : Filter.Tendsto (extChartAt I x).symm (nhds (extChartAt I x x)) (nhds x) := by
    simpa only [extChartAt_to_inv] using (continuousAt_extChartAt_symm (I := I) x).tendsto
  filter_upwards [htarget, hsymm.eventually hg, hsymm.eventually hF] with y hy hgy hFy
  simp only [Function.comp_apply] at hgy hFy ⊢
  rw [hgy, hFy, (extChartAt I x).right_inv hy]

end TauCeti

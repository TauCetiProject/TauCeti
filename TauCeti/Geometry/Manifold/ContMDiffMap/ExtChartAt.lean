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

/-!
# Smooth functions as functions of a localized chart

On a finite-dimensional Hausdorff real manifold, multiplying the extended chart at `x` by a bump
function gives a globally smooth map with the chart's germ at `x`. Near an interior point, every
smooth real function agrees with a smooth function on the model space composed with this localized
chart. These two steps reduce local statements about smooth functions to the model space.

## Main results

* `TauCeti.exists_contMDiffMap_eventuallyEq_extChartAt`: a globally smooth map with the germ of
  the extended chart at `x`.
* `TauCeti.exists_contMDiffMap_comp_eventuallyEq`: near an interior point, every smooth function
  agrees with a smooth function of that localized chart.
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
  -- Cut the chart expression of `f` off inside the interior of the chart target.
  have hFx : F x = extChartAt I x x := hF.eq_of_nhds
  have htarget : interior (extChartAt I x).target ∈ nhds (F x) := by
    rw [hFx]
    exact isOpen_interior.mem_nhds
      ((ModelWithCorners.isInteriorPoint_iff (I := I)).mp hx)
  obtain ⟨β, hβ, -⟩ :=
    (SmoothBumpFunction.nhds_basis_support
      (I := modelWithCornersSelf ℝ E) htarget).mem_iff.mp htarget
  let g : E → ℝ := fun y ↦ β y * f ((extChartAt I x).symm y)
  have hg : ContDiff ℝ ∞ g := by
    apply ContMDiff.contDiff
    refine contMDiff_of_tsupport fun y hy ↦ ?_
    have hytarget : y ∈ interior (extChartAt I x).target :=
      hβ (tsupport_mul_subset_left hy)
    have hsymmWithin :=
      contMDiffWithinAt_extChartAt_symm_target (n := ∞) x (interior_subset hytarget)
    have hsymm := hsymmWithin.contMDiffAt
      (Filter.mem_of_superset (isOpen_interior.mem_nhds hytarget) interior_subset)
    exact β.contMDiffAt.mul (f.contMDiff.contMDiffAt.comp y hsymm)
  refine ⟨⟨g, hg.contMDiff⟩, ?_⟩
  have hβF : Filter.EventuallyEq (nhds x) (β ∘ F) (fun _ ↦ 1) :=
    β.eventuallyEq_one.comp_tendsto F.contMDiff.continuous.continuousAt
  have hsource : ∀ᶠ y in nhds x, y ∈ (extChartAt I x).source :=
    (isOpen_extChartAt_source x).mem_nhds (mem_extChartAt_source x)
  filter_upwards [hF, hβF, hsource] with y hFy hβy hy
  -- Unfold composition and the bundled chart-local function; no theorem rewrites through both
  -- bundled-map coercions at once.
  change f y = β (F y) * f ((extChartAt I x).symm (F y))
  -- Likewise expose the constant function in the eventual equality supplied by the bump.
  change β (F y) = 1 at hβy
  rw [hβy, one_mul, hFy, (extChartAt I x).left_inv hy]

end TauCeti

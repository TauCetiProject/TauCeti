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
* `TauCeti.exists_contMDiffMap_comp_extChartAt_symm_eventuallyEq`: equivalently, near the image of
  an interior point, the chart expression of a smooth function agrees with a smooth function on
  the model space.
* `TauCeti.contDiffAt_comp_extChartAt_symm`: the chart expression of a smooth function is smooth
  at the image of an interior point.
-/

public section

open Filter
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

/-- Near an interior point `x`, if `f` agrees with `g ∘ F` for a map `F` with the germ of the
extended chart at `x`, then the chart expression `f ∘ (extChartAt I x).symm` agrees with `g` near
`extChartAt I x x`. -/
theorem comp_extChartAt_symm_eventuallyEq_of_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {x : M} (hx : I.IsInteriorPoint x)
    {F : C^∞⟮I, M; modelWithCornersSelf ℝ E, E⟯} (hF : (F : M → E) =ᶠ[𝓝 x] extChartAt I x)
    {f : C^∞⟮I, M; ℝ⟯} {g : C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯}
    (hg : (f : M → ℝ) =ᶠ[𝓝 x] g ∘ F) :
    (f ∘ (extChartAt I x).symm) =ᶠ[𝓝 (extChartAt I x x)] g := by
  have ht : Tendsto (extChartAt I x).symm (𝓝 (extChartAt I x x)) (𝓝 x) := by
    simpa using (continuousAt_extChartAt_symm (I := I) x).tendsto
  have htarget : (extChartAt I x).target ∈ 𝓝 (extChartAt I x x) :=
    mem_interior_iff_mem_nhds.mp (I.isInteriorPoint_iff.mp hx)
  filter_upwards [ht.eventually hg, ht.eventually hF, htarget] with z hz hFz hzt
  simp only [Function.comp_apply] at hz hFz ⊢
  rw [hz, hFz, (extChartAt I x).right_inv hzt]

/-- **The chart expression of a smooth function near an interior point.** Near the image of an
interior point `x`, the chart expression `f ∘ (extChartAt I x).symm` of a smooth function agrees
with a smooth function on the model space. -/
theorem exists_contMDiffMap_comp_extChartAt_symm_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {x : M} (hx : I.IsInteriorPoint x) (f : C^∞⟮I, M; ℝ⟯) :
    ∃ g : C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯,
      (f ∘ (extChartAt I x).symm) =ᶠ[𝓝 (extChartAt I x x)] g := by
  obtain ⟨F, hF⟩ := exists_contMDiffMap_eventuallyEq_extChartAt (I := I) x
  obtain ⟨g, hg⟩ := exists_contMDiffMap_comp_eventuallyEq hx F hF f
  exact ⟨g, comp_extChartAt_symm_eventuallyEq_of_eventuallyEq hx hF hg⟩

/-- At an interior point `x`, the chart expression `f ∘ (extChartAt I x).symm` of a smooth
function is smooth at `extChartAt I x x`. -/
theorem contDiffAt_comp_extChartAt_symm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {x : M} (hx : I.IsInteriorPoint x) (f : C^∞⟮I, M; ℝ⟯) :
    ContDiffAt ℝ ∞ (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  obtain ⟨g, hg⟩ := exists_contMDiffMap_comp_extChartAt_symm_eventuallyEq hx f
  exact g.contMDiff.contDiff.contDiffAt.congr_of_eventuallyEq hg

end TauCeti

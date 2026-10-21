/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Constancy from a vanishing manifold differential

A differentiable map with zero differential on an open subset of a real manifold is locally
constant there. Both manifolds may have boundary or corners, and neither needs to be finite
dimensional. On a preconnected source the map is constant.

These results turn infinitesimal independence of a parameter into independence of that
parameter itself, for example when separating the factors of a product isometry.
The argument applies Mathlib's `Convex.is_const_of_fderivWithin_eq_zero` in source and target
charts, on a ball intersected with the convex range of the source model.
-/

public section

open Set Filter Topology
open scoped Manifold

namespace MDifferentiableOn

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold I 1 M] [IsManifold J 1 N]
  {f : M → N} {s : Set M}

/-- A differentiable map with zero differential on an open set agrees locally with its
value at each point of that set. Both manifolds may have boundary or corners. -/
theorem eventuallyEq_const_of_mfderiv_eq_zero (hf : MDifferentiableOn I J f s)
    (hs : IsOpen s) (hzero : ∀ y ∈ s, mfderiv I J f y = 0) {x : M} (hx : x ∈ s) :
    f =ᶠ[𝓝 x] fun _ => f x := by
  -- Work in one source chart, and shrink to where the image stays in one target chart.
  let c := extChartAt I x
  let d := extChartAt J (f x)
  let U := c.target ∩ c.symm ⁻¹' (s ∩ f ⁻¹' d.source)
  let g : E → F := d ∘ f ∘ c.symm
  have hdopen : IsOpen d.source := isOpen_extChartAt_source (f x)
  have hVopen : IsOpen (s ∩ f ⁻¹' d.source) :=
    hf.continuousOn.isOpen_inter_preimage hs hdopen
  have hcx : c x ∈ U := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    simp only [mem_preimage, c, extChartAt_to_inv]
    exact ⟨hx, mem_extChartAt_source (f x)⟩
  have hU : U ∈ 𝓝[range I] c x :=
    inter_mem (extChartAt_target_mem_nhdsWithin x)
      ((continuousAt_extChartAt_symm x).continuousWithinAt.preimage_mem_nhdsWithin
        (hVopen.mem_nhds hcx.2))
  -- The chain rule transfers the vanishing differential to the coordinate expression,
  -- computed within the model range.
  have hdiff : ∀ u ∈ U,
      DifferentiableWithinAt ℝ g (range I) u ∧ fderivWithin ℝ g (range I) u = 0 := by
    intro u hu
    have hc : MDifferentiableWithinAt 𝓘(ℝ, E) I c.symm (range I) u :=
      mdifferentiableWithinAt_extChartAt_symm hu.1
    have hfu := (hf (c.symm u) hu.2.1).mdifferentiableAt (hs.mem_nhds hu.2.1)
    have hd : MDifferentiableAt J 𝓘(ℝ, F) d (f (c.symm u)) :=
      mdifferentiableAt_extChartAt (by
        simpa only [mem_preimage, d, extChartAt_source] using hu.2.2)
    have hg := (hd.comp _ hfu).comp_mdifferentiableWithinAt _ hc
    refine ⟨hg.differentiableWithinAt, ?_⟩
    have hderiv : mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, F) g (range I) u = 0 := by
      dsimp only [g]
      rw [← Function.comp_assoc, mfderiv_comp_mfderivWithin u (hd.comp _ hfu) hc
        ((uniqueMDiffOn_iff_uniqueDiffOn.mpr I.uniqueDiffOn) u
          (extChartAt_target_subset_range x hu.1)),
        mfderiv_comp (c.symm u) hd hfu, hzero _ hu.2.1,
        ContinuousLinearMap.comp_zero, ContinuousLinearMap.zero_comp]
    have hz : mvfderivWithin 𝓘(ℝ, E) g (range I) u = 0 := by
      rw [mvfderivWithin, hderiv, ContinuousLinearMap.comp_zero]
    rw [mvfderivWithin_eq_fderivWithin] at hz
    ext v
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, zero_apply] using
      DFunLike.congr_fun hz ((NormedSpace.fromTangentSpace (𝕜 := ℝ) u).symm v)
  -- The mean value theorem on a convex neighbourhood in the model range makes the coordinate
  -- expression constant there; chart injectivity recovers `f`.
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.mp hU
  have hconv : Convex ℝ (range I ∩ Metric.ball (c x) r) :=
    I.convex_range.inter (convex_ball _ _)
  have hsub : range I ∩ Metric.ball (c x) r ⊆ U := fun u hu => hball ⟨hu.2, hu.1⟩
  have hcxr : c x ∈ range I ∩ Metric.ball (c x) r :=
    ⟨extChartAt_target_subset_range x (mem_extChartAt_target x), Metric.mem_ball_self hr⟩
  have hconst : ∀ u ∈ range I ∩ Metric.ball (c x) r, g u = g (c x) := fun u hu =>
    hconv.is_const_of_fderivWithin_eq_zero
      (fun v hv => (hdiff v (hsub hv)).1.mono inter_subset_left)
      (fun v hv => by
        rw [fderivWithin_inter (Metric.isOpen_ball.mem_nhds hv.2)]
        exact (hdiff v (hsub hv)).2) hu hcxr
  have hnear : ∀ᶠ y in 𝓝 x, c y ∈ Metric.ball (c x) r :=
    (continuousAt_extChartAt (I := I) x).preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  filter_upwards [hnear, (isOpen_extChartAt_source (I := I) x).mem_nhds
    (mem_extChartAt_source x)] with y hy hys
  have hyr : c y ∈ range I ∩ Metric.ball (c x) r :=
    ⟨extChartAt_target_subset_range x (c.map_source hys), hy⟩
  have hfy : f y ∈ d.source := by
    simpa only [mem_preimage, c.left_inv hys] using (hsub hyr).2.2
  apply d.injOn hfy (mem_extChartAt_source (f x))
  simpa only [g, Function.comp_apply, c.left_inv hys, c.left_inv (mem_extChartAt_source x)]
    using hconst _ hyr

end MDifferentiableOn

namespace MDifferentiable

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold I 1 M] [IsManifold J 1 N] {f : M → N}

/-- A differentiable map from a real manifold with zero differential is locally constant.
The source may have boundary or corners. -/
theorem isLocallyConstant_of_mfderiv_eq_zero (hf : MDifferentiable I J f)
    (hzero : ∀ x, mfderiv I J f x = 0) : IsLocallyConstant f :=
  (IsLocallyConstant.iff_eventually_eq f).mpr fun x =>
    hf.mdifferentiableOn.eventuallyEq_const_of_mfderiv_eq_zero isOpen_univ
      (fun y _ => hzero y) (mem_univ x)

/-- A differentiable map with zero differential on a preconnected real manifold takes the
same value at every two points. -/
theorem apply_eq_of_mfderiv_eq_zero [PreconnectedSpace M] (hf : MDifferentiable I J f)
    (hzero : ∀ x, mfderiv I J f x = 0) (x y : M) : f x = f y :=
  (hf.isLocallyConstant_of_mfderiv_eq_zero hzero).apply_eq_of_preconnectedSpace x y

end MDifferentiable

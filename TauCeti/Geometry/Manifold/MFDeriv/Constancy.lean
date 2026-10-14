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

A differentiable map with zero differential on an open subset of a real boundaryless
manifold is locally constant there. Its target may have boundary or corners, and neither
manifold needs to be finite dimensional. On a preconnected source the map is constant.

These results turn infinitesimal independence of a parameter into independence of that
parameter itself, for example when separating the factors of a product isometry.
The argument uses Mathlib's `IsOpen.isOpen_inter_preimage_of_fderiv_eq_zero`
in source and target charts.
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
  [IsManifold I 1 M] [IsManifold J 1 N] [I.Boundaryless]
  {f : M → N} {s : Set M}

/-- A differentiable map with zero differential on an open set agrees locally with its
value at each point of that set. The source is boundaryless; the target need not be. -/
theorem eventuallyEq_const_of_mfderiv_eq_zero (hf : MDifferentiableOn I J f s)
    (hs : IsOpen s) (hzero : ∀ y ∈ s, mfderiv I J f y = 0) {x : M} (hx : x ∈ s) :
    f =ᶠ[𝓝 x] fun _ => f x := by
  -- Work in one source chart, and shrink to where the image stays in one target chart.
  let c := extChartAt I x
  let d := extChartAt J (f x)
  let U := c.target ∩ c.symm ⁻¹' (s ∩ f ⁻¹' d.source)
  let g : E → F := d ∘ f ∘ c.symm
  have hcopen : IsOpen c.target := isOpen_extChartAt_target x
  have hdopen : IsOpen d.source := isOpen_extChartAt_source (f x)
  have hVopen : IsOpen (s ∩ f ⁻¹' d.source) :=
    hf.continuousOn.isOpen_inter_preimage hs hdopen
  have hUopen : IsOpen U :=
    (continuousOn_extChartAt_symm x).isOpen_inter_preimage hcopen hVopen
  have hcx : c x ∈ U := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    simp only [mem_preimage, c, extChartAt_to_inv]
    exact ⟨hx, mem_extChartAt_source (f x)⟩
  -- The chain rule transfers the vanishing differential to the coordinate expression.
  have hdiff : ∀ u ∈ U, DifferentiableAt ℝ g u ∧ fderiv ℝ g u = 0 := by
    intro u hu
    have hc : MDifferentiableAt 𝓘(ℝ, E) I c.symm u := by
      have h := mdifferentiableWithinAt_extChartAt_symm (I := I) hu.1
      simpa only [I.range_eq_univ, mdifferentiableWithinAt_univ] using h
    have hfu := (hf (c.symm u) hu.2.1).mdifferentiableAt (hs.mem_nhds hu.2.1)
    have hd : MDifferentiableAt J 𝓘(ℝ, F) d (f (c.symm u)) :=
      mdifferentiableAt_extChartAt (by
        simpa only [mem_preimage, d, extChartAt_source] using hu.2.2)
    refine ⟨((hd.comp _ hfu).comp _ hc).differentiableAt, ?_⟩
    have hderiv : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g u = 0 := by
      dsimp only [g]
      rw [← Function.comp_assoc, mfderiv_comp u (hd.comp _ hfu) hc,
        mfderiv_comp (c.symm u) hd hfu, hzero _ hu.2.1,
        ContinuousLinearMap.comp_zero, ContinuousLinearMap.zero_comp]
    have hz : mvfderiv 𝓘(ℝ, E) g u = 0 := by
      rw [mvfderiv, hderiv, ContinuousLinearMap.comp_zero]
    rw [mvfderiv_eq_fderiv] at hz
    ext v
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, zero_apply] using
      DFunLike.congr_fun hz ((NormedSpace.fromTangentSpace (𝕜 := ℝ) u).symm v)
  -- The mean value theorem makes the coordinate fibre open; chart injectivity recovers `f`.
  have hWopen : IsOpen (U ∩ g ⁻¹' {g (c x)}) :=
    hUopen.isOpen_inter_preimage_of_fderiv_eq_zero
      (fun u hu => (hdiff u hu).1.differentiableWithinAt)
      (fun u hu => (hdiff u hu).2) _
  have hnear : ∀ᶠ y in 𝓝 x, c y ∈ U ∩ g ⁻¹' {g (c x)} :=
    (continuousAt_extChartAt (I := I) x).preimage_mem_nhds
      (hWopen.mem_nhds ⟨hcx, rfl⟩)
  filter_upwards [hnear, (isOpen_extChartAt_source (I := I) x).mem_nhds
    (mem_extChartAt_source x)] with y hy hys
  have hyU := hy.1
  have hfy : f y ∈ d.source := by
    simpa only [mem_preimage, c.left_inv hys] using hyU.2.2
  apply d.injOn hfy (mem_extChartAt_source (f x))
  simpa only [mem_preimage, mem_singleton_iff, g, Function.comp_apply, c.left_inv hys, c.left_inv
    (mem_extChartAt_source x)] using hy.2

end MDifferentiableOn

namespace MDifferentiable

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold I 1 M] [IsManifold J 1 N] [I.Boundaryless] {f : M → N}

/-- A differentiable map from a real boundaryless manifold with zero differential
is locally constant. -/
theorem isLocallyConstant_of_mfderiv_eq_zero (hf : MDifferentiable I J f)
    (hzero : ∀ x, mfderiv I J f x = 0) : IsLocallyConstant f :=
  (IsLocallyConstant.iff_eventually_eq f).mpr fun x =>
    hf.mdifferentiableOn.eventuallyEq_const_of_mfderiv_eq_zero isOpen_univ
      (fun y _ => hzero y) (mem_univ x)

/-- A differentiable map with zero differential on a preconnected real boundaryless
manifold takes the same value at every two points. -/
theorem apply_eq_of_mfderiv_eq_zero [PreconnectedSpace M] (hf : MDifferentiable I J f)
    (hzero : ∀ x, mfderiv I J f x = 0) (x y : M) : f x = f y :=
  (hf.isLocallyConstant_of_mfderiv_eq_zero hzero).apply_eq_of_preconnectedSpace x y

end MDifferentiable

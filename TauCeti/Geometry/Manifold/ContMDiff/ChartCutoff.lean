/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Cutting a function off in a chart

Let `u` be a `C¹` real function on a manifold without boundary and `b` a smooth bump function on
the model space, centred at the chart image of a point `c`, whose closed support ball lies in the
target of the extended chart at `c`. The product `y ↦ b y * u ((extChartAt I c).symm y)` is then a
compactly supported `C¹` function on the model space, agreeing with the coordinate expression of
`u` where `b = 1`. This is the standard way to localize an estimate from the model space to a
manifold. This file records its regularity and the bound on its derivative.

Conversely, a compactly supported function on the model space whose support lies in the chart
target is the coordinate expression of a compactly supported function on the manifold, extended by
zero outside the chart. This is the standard way to transplant a test function from the model
space to a manifold.

## Main results

* `ContDiffBump.contDiff_mul_comp_extChartAt_symm`: the cut-off coordinate expression is `C¹`.
* `ContDiffBump.norm_fderiv_mul_comp_extChartAt_symm_le`: in the chart target its derivative is
  bounded by the derivative of the coordinate expression plus `G |u|`, where `G` bounds the
  derivative of the bump.
* `ContDiffBump.fderiv_mul_comp_extChartAt_symm_eq_zero`: its derivative vanishes outside the
  closed support ball of the bump.
* `TauCeti.Manifold.exists_contMDiff_comp_extChartAt_symm_eq`: a `C^n` function on the model
  space with compact support in the chart target is the coordinate expression of a compactly
  supported `C^n` function on the manifold.
-/

public section

open Function Metric Set
open scoped Manifold

namespace ContDiffBump

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {c : M} (b : ContDiffBump (extChartAt I c c)) {u : M → ℝ}

/-- A bump function whose closed support ball lies in the chart target, times the coordinate
expression of a `C¹` function, is a `C¹` function on the model space. -/
theorem contDiff_mul_comp_extChartAt_symm [I.Boundaryless] [IsManifold I 1 M]
    (hb : closedBall (extChartAt I c c) b.rOut ⊆ (extChartAt I c).target)
    (hu : ContMDiff I 𝓘(ℝ) 1 u) :
    ContDiff ℝ 1 fun y ↦ b y * u ((extChartAt I c).symm y) := by
  refine contDiff_iff_contDiffAt.2 fun y ↦ ?_
  by_cases hy : y ∈ (extChartAt I c).target
  · exact b.contDiffAt.mul ((hu.comp_contMDiffOn (contMDiffOn_extChartAt_symm c)).contDiffOn
      |>.contDiffAt ((isOpen_extChartAt_target c).mem_nhds hy))
  · -- Off the chart target, the bump vanishes near `y`.
    have hy' : y ∉ tsupport b := by
      rw [b.tsupport_eq]
      exact fun h ↦ hy (hb h)
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport b).isOpen_compl.mem_nhds hy'] with z hz
    rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]

/-- The derivative of the cut-off coordinate expression at a point of the chart target is bounded
by the derivative of the coordinate expression plus `G |u|`, where `G` bounds the derivative of
the bump. -/
theorem norm_fderiv_mul_comp_extChartAt_symm_le [I.Boundaryless] [IsManifold I 1 M]
    (hu : ContMDiff I 𝓘(ℝ) 1 u) {G : ℝ} (hG : ∀ y, ‖fderiv ℝ b y‖ ≤ G) {y : E}
    (hy : y ∈ (extChartAt I c).target) :
    ‖fderiv ℝ (fun y ↦ b y * u ((extChartAt I c).symm y)) y‖ ≤
      ‖fderiv ℝ (fun y ↦ u ((extChartAt I c).symm y)) y‖ + G * |u ((extChartAt I c).symm y)| := by
  have hd : DifferentiableAt ℝ (fun y ↦ u ((extChartAt I c).symm y)) y :=
    ((hu.comp_contMDiffOn (contMDiffOn_extChartAt_symm c)).contDiffOn.contDiffAt
      ((isOpen_extChartAt_target c).mem_nhds hy)).differentiableAt one_ne_zero
  rw [fderiv_fun_mul (b.contDiffAt (n := 1).differentiableAt one_ne_zero) hd]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg b.nonneg,
    mul_comm |u _|]
  gcongr
  · exact mul_le_of_le_one_left (norm_nonneg _) b.le_one
  · exact hG y

/-- The cut-off coordinate expression has zero derivative outside the closed support ball of the
bump. -/
theorem fderiv_mul_comp_extChartAt_symm_eq_zero {y : E}
    (hy : y ∉ closedBall (extChartAt I c c) b.rOut) :
    fderiv ℝ (fun y ↦ b y * u ((extChartAt I c).symm y)) y = 0 :=
  notMem_support.1 fun h ↦ hy <| b.tsupport_eq ▸
    tsupport_mul_subset_left (support_fderiv_subset ℝ h)

end ContDiffBump

namespace TauCeti.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]

/-- **Transplanting a function from a chart.** A `C^n` function `w` on the model space whose
support is a compact subset of the target of the extended chart at `c` is, on that target, the
coordinate expression of a compactly supported `C^n` function `u` on `M` whose support lies in the
chart preimage of the support of `w`. -/
theorem exists_contMDiff_comp_extChartAt_symm_eq {n : WithTop ℕ∞} [IsManifold I n M] {c : M}
    {w : E → F} (hw : ContDiff 𝕜 n w) (hwc : HasCompactSupport w)
    (hwt : tsupport w ⊆ (extChartAt I c).target) :
    ∃ u : M → F, ContMDiff I 𝓘(𝕜, F) n u ∧ HasCompactSupport u ∧
      tsupport u ⊆ (extChartAt I c).symm '' tsupport w ∧
      ∀ y ∈ (extChartAt I c).target, u ((extChartAt I c).symm y) = w y := by
  classical
  set φ := extChartAt I c
  set u : M → F := fun x ↦ if x ∈ φ.source then w (φ x) else 0
  have hK : IsCompact (φ.symm '' tsupport w) :=
    hwc.isCompact.image_of_continuousOn ((continuousOn_extChartAt_symm c).mono hwt)
  have hsupp : tsupport u ⊆ φ.symm '' tsupport w := by
    refine closure_minimal (fun x hx ↦ ?_) hK.isClosed
    by_cases hxs : x ∈ φ.source
    · have hx' : w (φ x) ≠ 0 := by simpa [u, hxs] using hx
      exact ⟨φ x, subset_tsupport _ hx', φ.left_inv hxs⟩
    · exact absurd (by simp [u, hxs]) hx
  refine ⟨u, contMDiff_of_tsupport fun x hx ↦ ?_, hK.of_isClosed_subset (isClosed_tsupport u) hsupp,
    hsupp, fun y hy ↦ (ite_eq_left (φ.map_target hy)).trans (congrArg w (φ.right_inv hy))⟩
  -- On the chart source, `u` is the coordinate expression `w ∘ φ`.
  obtain ⟨y, hy, rfl⟩ := hsupp hx
  have hxs : φ.symm y ∈ φ.source := φ.map_target (hwt hy)
  refine ContMDiffAt.congr_of_eventuallyEq (f := w ∘ φ) ?_ (Filter.eventually_of_mem
    ((isOpen_extChartAt_source c).mem_nhds hxs) fun z hz ↦ ite_eq_left hz)
  exact hw.contMDiff.contMDiffAt.comp _
    (contMDiffAt_extChartAt' (by rwa [extChartAt_source] at hxs))

end TauCeti.Manifold

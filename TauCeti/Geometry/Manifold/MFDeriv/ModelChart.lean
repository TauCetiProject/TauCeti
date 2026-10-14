/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Calculus in the charts of a manifold modelled on its own model space

Let `M` be a manifold modelled on a real normed space `E` with the trivial model `𝓘(ℝ, E)`, so that
a chart `e` of the maximal atlas is an honest map `M → E`. If `f = h ∘ e` on the source of `e`,
then the differential of `f` is the Fréchet derivative of `h` composed with the derivative of the
chart, which is invertible, so the critical points of `f` in the source of `e` are the preimages of
the critical points of `h`. This file records these facts and their consequences for a smooth real
function: its coordinate expression in the preferred chart is smooth, it has the same critical
points, and its regular points form an open set.

## Main results

* `TauCeti.mfderiv_eq_fderiv_comp_of_eqOn`: `df_y = dh_{e y} ∘ de_y` where `f = h ∘ e`.
* `TauCeti.isInvertible_mfderiv_chart`: the derivative of a chart of the maximal atlas is
  invertible.
* `TauCeti.mfderiv_eq_zero_iff_of_eqOn`: the critical points of `f` in the source of `e` are the
  preimages of the critical points of `h`.
* `TauCeti.mfderiv_eq_zero_iff_fderiv_comp_extChartAt_symm`: a point is critical for a smooth `f`
  exactly when it is critical for the coordinate expression of `f` in the preferred chart.
* `TauCeti.isOpen_setOf_mfderiv_ne_zero`: the regular points of a smooth function form an open
  set.
-/

public section

open Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}

section Chart

variable {e : OpenPartialHomeomorph M E} {h : E → ℝ}

/-- If `f = h ∘ e` on the source of a chart `e` of the maximal atlas, with `h` differentiable,
then `df_y = dh_{e y} ∘ de_y`. -/
theorem mfderiv_eq_fderiv_comp_of_eqOn (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hfh : EqOn f (h ∘ e) e.source) {y : M} (hy : y ∈ e.source)
    (hh : DifferentiableAt ℝ h (e y)) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y =
      (fderiv ℝ h (e y) : E →L[ℝ] ℝ).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e y) := by
  have hev : f =ᶠ[𝓝 y] h ∘ e := Filter.eventuallyEq_of_mem (e.open_source.mem_nhds hy) hfh
  rw [hev.mfderiv_eq]
  have he1 : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) he
  rw [mfderiv_comp y (hh.mdifferentiableAt) (mdifferentiableAt_of_mem_maximalAtlas he1 hy),
    mfderiv_eq_fderiv]
  rfl

/-- `isInvertible_mfderiv_extend` for a chart of the maximal atlas of a manifold modelled on its
own model space, where the extended chart is the chart itself. -/
theorem isInvertible_mfderiv_chart (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {y : M} (hy : y ∈ e.source) : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e y).IsInvertible := by
  have := isInvertible_mfderiv_extend (IsManifold.maximalAtlas_subset_of_le (by simp) he) hy
  have hext : (e.extend 𝓘(ℝ, E) : M → E) = e := by ext z; simp
  rwa [hext] at this

/-- Where `f = h ∘ e` on the source of a chart `e`, the critical points of `f` in the source are the
preimages of the critical points of `h`. -/
theorem mfderiv_eq_zero_iff_of_eqOn (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hfh : EqOn f (h ∘ e) e.source) {y : M} (hy : y ∈ e.source)
    (hh : DifferentiableAt ℝ h (e y)) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 ↔ fderiv ℝ h (e y) = 0 := by
  rw [mfderiv_eq_fderiv_comp_of_eqOn he hfh hy hh]
  have hinv := isInvertible_mfderiv_chart he hy
  constructor
  · intro h0
    ext v
    have hw := DFunLike.congr_fun h0 ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e y).inverse v)
    have hv : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e y ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e y).inverse v) = v :=
      hinv.self_apply_inverse v
    exact (congrArg (fderiv ℝ h (e y)) hv).symm.trans hw
  · intro h0
    rw [h0]
    rfl

end Chart

section Preferred

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The coordinate expression of `f` in the preferred chart at `p`. -/
theorem eqOn_comp_chartAt_symm (p : M) :
    EqOn f ((f ∘ (chartAt E p).symm) ∘ chartAt E p) (chartAt E p).source := fun y hy ↦ by
  simp [(chartAt E p).left_inv hy]

omit [FiniteDimensional ℝ E] in
/-- The coordinate expression of a smooth function is smooth on the chart target. -/
theorem contDiffOn_comp_chartAt_symm (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (p : M) :
    ContDiffOn ℝ ∞ (f ∘ (chartAt E p).symm) (chartAt E p).target :=
  (hf.comp_contMDiffOn contMDiffOn_chart_symm).contDiffOn

omit [FiniteDimensional ℝ E] in
/-- A point is critical for a smooth `f` exactly when it is critical for the coordinate expression
of `f` in the preferred extended chart at that point. -/
theorem mfderiv_eq_zero_iff_fderiv_comp_extChartAt_symm (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    (x : M) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 ↔
      fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) x).symm) (extChartAt 𝓘(ℝ, E) x x) = 0 := by
  have hext : ((extChartAt 𝓘(ℝ, E) x).symm : E → M) = (chartAt E x).symm := by ext; simp
  have hext' : extChartAt 𝓘(ℝ, E) x x = chartAt E x x := by simp
  rw [hext, hext']
  exact mfderiv_eq_zero_iff_of_eqOn (IsManifold.chart_mem_maximalAtlas x)
    (eqOn_comp_chartAt_symm x) (mem_chart_source E x)
    (((contDiffOn_comp_chartAt_symm hf x).contDiffAt ((chartAt E x).open_target.mem_nhds
      (mem_chart_target E x))).differentiableAt (by simp))

omit [FiniteDimensional ℝ E] in
/-- The regular points of a smooth function form an open set. -/
theorem isOpen_setOf_mfderiv_ne_zero (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) :
    IsOpen {y : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0} := by
  refine isOpen_iff_mem_nhds.2 fun y₀ hy₀ ↦ ?_
  set c := chartAt E y₀
  have hcont : ContinuousOn (fderiv ℝ (f ∘ c.symm)) c.target :=
    (contDiffOn_comp_chartAt_symm hf y₀).continuousOn_fderiv_of_isOpen c.open_target (by simp)
  have hdiff : ∀ y ∈ c.source, DifferentiableAt ℝ (f ∘ c.symm) (c y) := fun y hy ↦
    ((contDiffOn_comp_chartAt_symm hf y₀).contDiffAt (c.open_target.mem_nhds
      (c.map_source hy))).differentiableAt (by simp)
  have hmem : y₀ ∈ c.source := mem_chart_source E y₀
  have hiff : ∀ y ∈ c.source, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 ↔ fderiv ℝ (f ∘ c.symm) (c y) = 0 :=
    fun y hy ↦ mfderiv_eq_zero_iff_of_eqOn (IsManifold.chart_mem_maximalAtlas y₀)
      (eqOn_comp_chartAt_symm y₀) hy (hdiff y hy)
  have h0 : fderiv ℝ (f ∘ c.symm) (c y₀) ≠ 0 := fun h ↦ hy₀ ((hiff y₀ hmem).2 h)
  have hca : ContinuousAt (fderiv ℝ (f ∘ c.symm)) (c y₀) :=
    hcont.continuousAt (c.open_target.mem_nhds (c.map_source hmem))
  have hev : ∀ᶠ y in 𝓝 y₀, fderiv ℝ (f ∘ c.symm) (c y) ≠ 0 :=
    (hca.comp (c.continuousAt hmem)).eventually_ne h0
  filter_upwards [hev, c.open_source.mem_nhds hmem] with y hy hys
  exact fun h ↦ hy ((hiff y hys).1 h)

end Preferred

end TauCeti

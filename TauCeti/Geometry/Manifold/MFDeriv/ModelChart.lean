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

Let `M` be a manifold modelled on a normed space `E` over `𝕜` with the trivial model `𝓘(𝕜, E)`, so
that a chart `e` of the maximal atlas is an honest map `M → E`. If `f = h ∘ e` on the source of `e`
for a map `f : M → F` into a normed space `F`, then the differential of `f` is the Fréchet
derivative of `h` composed with the derivative of the chart, which is invertible, so the
differential of `f` vanishes at a point in the source of `e` if and only if the Fréchet derivative
of `h` vanishes at its image under `e`. This file records these facts and their consequences in the
preferred chart: the coordinate expression of a `C^n` map is `C^n`, the differential of a
differentiable map vanishes at a point if and only if the Fréchet derivative of its coordinate
expression vanishes there, and the points where the differential of a `C^1` map is nonzero form an
open set.

## Main results

* `TauCeti.mfderiv_eq_fderiv_comp_of_eqOn`: `df_y = dh_{e y} ∘ de_y` where `f = h ∘ e`.
* `TauCeti.isInvertible_mfderiv_chart`: the derivative of a chart of the `C^1` maximal atlas is
  invertible.
* `TauCeti.contDiffAt_symm_trans_of_mem_maximalAtlas`: a transition map between two charts of the
  `C^n` maximal atlas is `C^n` on its source.
* `TauCeti.trans_mem_maximalAtlas_of_contDiffAt`: a chart of the `C^n` maximal atlas followed by a
  `C^n` chart of the model space with `C^n` inverse is again in the maximal atlas.
* `TauCeti.mfderiv_eq_zero_iff_of_eqOn`: on the source of `e`, the differential of `f` vanishes at
  `y` if and only if the Fréchet derivative of `h` vanishes at `e y`.
* `TauCeti.mfderiv_eq_zero_iff_fderiv_comp_extChartAt_symm`: the differential of a differentiable
  `f` vanishes at `x` if and only if the Fréchet derivative of its coordinate expression in the
  preferred chart vanishes at `extChartAt 𝓘(𝕜, E) x x`.
* `TauCeti.isOpen_setOf_mfderiv_ne_zero`: the points where the differential of a `C^1` map is
  nonzero form an open set.
-/

public section

open Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

section Chart

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → F} {e : OpenPartialHomeomorph M E} {h : E → F}

/-- If `f = h ∘ e` on the source of a chart `e` of the `C^1` maximal atlas, with `h` differentiable,
then `df_y = dh_{e y} ∘ de_y`. -/
theorem mfderiv_eq_fderiv_comp_of_eqOn (he : e ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) 1 M)
    (hfh : EqOn f (h ∘ e) e.source) {y : M} (hy : y ∈ e.source)
    (hh : DifferentiableAt 𝕜 h (e y)) :
    mfderiv 𝓘(𝕜, E) 𝓘(𝕜, F) f y =
      (fderiv 𝕜 h (e y) : E →L[𝕜] F).comp (mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) e y) := by
  have hev : f =ᶠ[𝓝 y] h ∘ e := Filter.eventuallyEq_of_mem (e.open_source.mem_nhds hy) hfh
  rw [hev.mfderiv_eq,
    mfderiv_comp y hh.mdifferentiableAt (mdifferentiableAt_of_mem_maximalAtlas he hy),
    mfderiv_eq_fderiv]
  rfl

/-- `isInvertible_mfderiv_extend` for a chart of the `C^1` maximal atlas of a manifold modelled on
its own model space, where the extended chart is the chart itself. -/
theorem isInvertible_mfderiv_chart (he : e ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) 1 M)
    {y : M} (hy : y ∈ e.source) : (mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) e y).IsInvertible := by
  have := isInvertible_mfderiv_extend he hy
  have hext : (e.extend 𝓘(𝕜, E) : M → E) = e := by ext z; simp
  rwa [hext] at this

/-- Where `f = h ∘ e` on the source of a chart `e` of the `C^1` maximal atlas, the differential of
`f` vanishes at `y` in the source if and only if the Fréchet derivative of `h` vanishes at `e y`. -/
theorem mfderiv_eq_zero_iff_of_eqOn (he : e ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) 1 M)
    (hfh : EqOn f (h ∘ e) e.source) {y : M} (hy : y ∈ e.source)
    (hh : DifferentiableAt 𝕜 h (e y)) :
    mfderiv 𝓘(𝕜, E) 𝓘(𝕜, F) f y = 0 ↔ fderiv 𝕜 h (e y) = 0 := by
  rw [mfderiv_eq_fderiv_comp_of_eqOn he hfh hy hh]
  have hinv := isInvertible_mfderiv_chart he hy
  constructor
  · intro h0
    ext v
    have hw := DFunLike.congr_fun h0 ((mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) e y).inverse v)
    have hv : mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) e y ((mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) e y).inverse v) = v :=
      hinv.self_apply_inverse v
    exact (congrArg (fderiv 𝕜 h (e y)) hv).symm.trans hw
  · intro h0
    rw [h0]
    rfl

end Chart

section MaximalAtlas

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {n : WithTop ℕ∞}
  {q : OpenPartialHomeomorph M E}

/-- A transition map `q.symm.trans q'` between two charts of the maximal atlas is `C^n` at every
point of its source. -/
theorem contDiffAt_symm_trans_of_mem_maximalAtlas {q' : OpenPartialHomeomorph M E}
    (hq : q ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M) (hq' : q' ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M)
    {z : E} (hz : z ∈ (q.symm.trans q').source) : ContDiffAt 𝕜 n (q.symm.trans q') z := by
  rw [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage] at hz
  rw [← contMDiffAt_iff_contDiffAt, OpenPartialHomeomorph.coe_trans]
  exact (contMDiffAt_of_mem_maximalAtlas hq' hz.2).comp z
    (contMDiffAt_symm_of_mem_maximalAtlas hq hz.1)

variable [IsManifold 𝓘(𝕜, E) n M]

/-- A chart `q` of the maximal atlas followed by a chart `e` of the model space which is `C^n` on
its source, with `C^n` inverse on its target, is again a chart of the maximal atlas. -/
theorem trans_mem_maximalAtlas_of_contDiffAt {e : OpenPartialHomeomorph E E}
    (hq : q ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M) (he : ∀ z ∈ e.source, ContDiffAt 𝕜 n e z)
    (hes : ∀ z ∈ e.target, ContDiffAt 𝕜 n e.symm z) :
    q.trans e ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M := by
  refine (IsManifold.mem_maximalAtlas_iff_contMDiffOn _).2 ⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage] at hz
    rw [OpenPartialHomeomorph.coe_trans]
    exact ((contMDiffAt_iff_contDiffAt.2 (he _ hz.2)).comp z
      (contMDiffAt_of_mem_maximalAtlas hq hz.1)).contMDiffWithinAt
  · rw [OpenPartialHomeomorph.trans_target, mem_inter_iff, mem_preimage] at hz
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.coe_trans]
    exact ((contMDiffAt_symm_of_mem_maximalAtlas hq hz.2).comp z
      (contMDiffAt_iff_contDiffAt.2 (hes _ hz.1))).contMDiffWithinAt

end MaximalAtlas

section Preferred

/-- The coordinate expression of `f` in the preferred chart at `p`. -/
theorem eqOn_comp_chartAt_symm {E M α : Type*} [TopologicalSpace E] [TopologicalSpace M]
    [ChartedSpace E M] {f : M → α} (p : M) :
    EqOn f ((f ∘ (chartAt E p).symm) ∘ chartAt E p) (chartAt E p).source := fun y hy ↦ by
  simp [(chartAt E p).left_inv hy]

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → F}

/-- The coordinate expression of a `C^n` function is `C^n` on the chart target. -/
theorem contDiffOn_comp_chartAt_symm {n : WithTop ℕ∞} [IsManifold 𝓘(𝕜, E) n M]
    (hf : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, F) n f) (p : M) :
    ContDiffOn 𝕜 n (f ∘ (chartAt E p).symm) (chartAt E p).target :=
  (hf.comp_contMDiffOn contMDiffOn_chart_symm).contDiffOn

variable [IsManifold 𝓘(𝕜, E) 1 M]

/-- The differential of a differentiable `f` vanishes at `x` if and only if the Fréchet derivative
of the coordinate expression of `f` in the preferred extended chart at `x` vanishes at
`extChartAt 𝓘(𝕜, E) x x`. -/
theorem mfderiv_eq_zero_iff_fderiv_comp_extChartAt_symm {x : M}
    (hf : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, F) f x) :
    mfderiv 𝓘(𝕜, E) 𝓘(𝕜, F) f x = 0 ↔
      fderiv 𝕜 (f ∘ (extChartAt 𝓘(𝕜, E) x).symm) (extChartAt 𝓘(𝕜, E) x x) = 0 := by
  have hext : ((extChartAt 𝓘(𝕜, E) x).symm : E → M) = (chartAt E x).symm := by ext; simp
  have hext' : extChartAt 𝓘(𝕜, E) x x = chartAt E x x := by simp
  rw [hext, hext']
  have hsymm : (chartAt E x).symm (chartAt E x x) = x :=
    (chartAt E x).left_inv (mem_chart_source E x)
  exact mfderiv_eq_zero_iff_of_eqOn (IsManifold.chart_mem_maximalAtlas x)
    (eqOn_comp_chartAt_symm x) (mem_chart_source E x)
    (((hsymm.symm ▸ hf).comp _
      (mdifferentiableAt_atlas_symm (chart_mem_atlas E x) (mem_chart_target E x))).differentiableAt)

/-- The points where the differential of a `C^1` function is nonzero form an open set. -/
theorem isOpen_setOf_mfderiv_ne_zero (hf : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, F) 1 f) :
    IsOpen {y : M | mfderiv 𝓘(𝕜, E) 𝓘(𝕜, F) f y ≠ 0} := by
  refine isOpen_iff_mem_nhds.2 fun y₀ hy₀ ↦ ?_
  set c := chartAt E y₀
  have hcont : ContinuousOn (fderiv 𝕜 (f ∘ c.symm)) c.target :=
    (contDiffOn_comp_chartAt_symm hf y₀).continuousOn_fderiv_of_isOpen c.open_target le_rfl
  have hdiff : ∀ y ∈ c.source, DifferentiableAt 𝕜 (f ∘ c.symm) (c y) := fun y hy ↦
    ((contDiffOn_comp_chartAt_symm hf y₀).contDiffAt (c.open_target.mem_nhds
      (c.map_source hy))).differentiableAt one_ne_zero
  have hmem : y₀ ∈ c.source := mem_chart_source E y₀
  have hiff : ∀ y ∈ c.source, mfderiv 𝓘(𝕜, E) 𝓘(𝕜, F) f y = 0 ↔ fderiv 𝕜 (f ∘ c.symm) (c y) = 0 :=
    fun y hy ↦ mfderiv_eq_zero_iff_of_eqOn (IsManifold.chart_mem_maximalAtlas y₀)
      (eqOn_comp_chartAt_symm y₀) hy (hdiff y hy)
  have h0 : fderiv 𝕜 (f ∘ c.symm) (c y₀) ≠ 0 := fun h ↦ hy₀ ((hiff y₀ hmem).2 h)
  have hca : ContinuousAt (fderiv 𝕜 (f ∘ c.symm)) (c y₀) :=
    hcont.continuousAt (c.open_target.mem_nhds (c.map_source hmem))
  have hev : ∀ᶠ y in 𝓝 y₀, fderiv 𝕜 (f ∘ c.symm) (c y) ≠ 0 :=
    (hca.comp (c.continuousAt hmem)).eventually_ne h0
  filter_upwards [hev, c.open_source.mem_nhds hmem] with y hy hys
  exact fun h ↦ hy ((hiff y hys).1 h)

end Preferred

end TauCeti

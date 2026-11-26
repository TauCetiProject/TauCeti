/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import TauCeti.Analysis.Calculus.TangentCone.Chart
import TauCeti.Geometry.Manifold.ContMDiff.Groupoid
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

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
  invertible, and so is the derivative of its inverse (`TauCeti.isInvertible_mfderiv_chart_symm`)
  and the derivative read in the model space (`TauCeti.isInvertible_mvfderiv_chart`).
* `TauCeti.hasMFDerivAt_iff_hasFDerivAt_comp_chartAt_symm`: a map into a normed space has a given
  derivative if and only if its expression in the preferred chart does.
* `TauCeti.contDiffAt_symm_trans_of_mem_maximalAtlas`: a transition map between two charts of the
  `C^n` maximal atlas is `C^n` at every point of its source
  (`TauCeti.contDiffOn_symm_trans_of_mem_maximalAtlas`: on its source), and
  `TauCeti.contDiffAt_symm_trans_symm_of_mem_maximalAtlas`: its inverse is `C^n` on its target.
* `TauCeti.exists_hasFDerivAt_symm_trans`: such a transition map, for `n ≠ 0`, has an invertible
  derivative at each point of its source, which is strict over `ℝ` or `ℂ`
  (`TauCeti.exists_hasStrictFDerivAt_symm_trans`), so the determinant of its derivative is nonzero
  (`TauCeti.det_fderiv_symm_trans_ne_zero`).
* `TauCeti.exists_hasFDerivAt_symm_trans_of_mem_atlas`: the same when the first chart is in the
  atlas, which avoids needing `IsManifold` to know that it lies in the maximal atlas; it rests on
  `TauCeti.contDiffAt_of_mem_contDiffGroupoid`.
* `TauCeti.fderiv_symm_trans_comp_eq`: the chain rule for transitions between open partial
  homeomorphisms into the model space, read through the preferred chart.
* `TauCeti.trans_mem_maximalAtlas_of_contDiffAt`: a chart of the `C^n` maximal atlas followed by a
  `C^n` chart of the model space with `C^n` inverse is again in the maximal atlas.
* `TauCeti.exists_trans_mem_maximalAtlas_of_contDiffOn`: in particular, so is a chart of the
  maximal atlas followed by a `C^n` partial diffeomorphism between other normed spaces, conjugated
  by linear isomorphisms and composed with a translation.
* `TauCeti.mfderiv_eq_zero_iff_of_eqOn`: on the source of `e`, the differential of `f` vanishes at
  `y` if and only if the Fréchet derivative of `h` vanishes at `e y`.
* `TauCeti.isOpen_setOf_mfderiv_ne_zero`: the points where the differential of a `C^1` map is
  nonzero form an open set.
* `TauCeti.toDual_symm_comp_inverse_mvfderiv`: on a manifold modelled on a real Hilbert space, the
  frequency in a chart `e₂` of the covector `⟪η, ·⟫ ∘ de₁_x` read in a chart `e₁` is the image of
  `η` under the inverse adjoint of the derivative of the transition `e₂ ∘ e₁⁻¹`, the
  transformation law of covectors; and
  `TauCeti.innerSL_toDual_symm_comp_inverse_mvfderiv`: a covector `ξ ∈ T*ₓM` is `⟪η, ·⟫ ∘ de_x`
  for the frequency `η` dual to `ξ ∘ (de_x)⁻¹`, which is nonzero when `ξ` is
  (`TauCeti.toDual_symm_comp_inverse_mvfderiv_ne_zero`).
* `TauCeti.adjoint_ringInverse_fderiv_comp_symm_eq_one`: the inverse adjoint of the derivative of
  the transition from a chart to itself is the identity on the chart target.
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

/-- If `f = h ∘ e` on the source of a chart `e` of the `C^1` maximal atlas, then
`df_y = dh_{e y} ∘ de_y`. -/
theorem mfderiv_eq_fderiv_comp_of_eqOn (he : e ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) 1 M)
    (hfh : EqOn f (h ∘ e) e.source) {y : M} (hy : y ∈ e.source) :
    mfderiv 𝓘(𝕜, E) 𝓘(𝕜, F) f y =
      (fderiv 𝕜 h (e y) : E →L[𝕜] F).comp (mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) e y) := by
  have hev : f =ᶠ[𝓝 y] h ∘ e := Filter.eventuallyEq_of_mem (e.open_source.mem_nhds hy) hfh
  by_cases hh : DifferentiableAt 𝕜 h (e y)
  · rw [hev.mfderiv_eq,
      mfderiv_comp y hh.mdifferentiableAt (mdifferentiableAt_of_mem_maximalAtlas he hy),
      mfderiv_eq_fderiv]
    -- `EventuallyEq.mfderiv_eq` inserts `tangentSpaceCast` between the tangent spaces of `F` at
    -- `f y` and at `h (e y)`, which are both `F`, so the cast is the identity.
    rfl
  -- If `h` is not differentiable at `e y`, then `f` is not differentiable at `y` either, and both
  -- sides vanish by convention.
  have hf : ¬MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, F) f y := fun hfd ↦ hh <| by
    have hsymm := mdifferentiableAt_symm_of_mem_maximalAtlas he (e.map_source hy)
    have hfd' : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, F) f (e.symm (e y)) := by rwa [e.left_inv hy]
    refine (mdifferentiableAt_iff_differentiableAt.1
      (hfd'.comp (e y) hsymm)).congr_of_eventuallyEq ?_
    filter_upwards [e.open_target.mem_nhds (e.map_source hy)] with w hw
    simp only [comp_apply]
    exact (congrArg h (e.right_inv hw)).symm.trans (hfh (e.map_target hw)).symm
  rw [mfderiv_zero_of_not_mdifferentiableAt hf, fderiv_zero_of_not_differentiableAt hh]
  exact (ContinuousLinearMap.zero_comp _).symm

/-- `isInvertible_mfderiv_extend` for a chart of the `C^1` maximal atlas of a manifold modelled on
its own model space, where the extended chart is the chart itself. -/
theorem isInvertible_mfderiv_chart (he : e ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) 1 M)
    {y : M} (hy : y ∈ e.source) : (mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) e y).IsInvertible := by
  have := isInvertible_mfderiv_extend he hy
  have hext : (e.extend 𝓘(𝕜, E) : M → E) = e := by ext z; simp
  rwa [hext] at this

/-- `isInvertible_mfderivWithin_extend_symm` for a chart of the `C^1` maximal atlas of a manifold
modelled on its own model space: the derivative of the inverse chart is invertible at every point
of the chart target. -/
theorem isInvertible_mfderiv_chart_symm (he : e ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) 1 M)
    {z : E} (hz : z ∈ e.target) : (mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E) e.symm z).IsInvertible := by
  have := isInvertible_mfderivWithin_extend_symm he (y := z) (by simpa using hz)
  have hext : ((e.extend 𝓘(𝕜, E)).symm : E → M) = e.symm := by ext w; simp
  rwa [hext, modelWithCornersSelf_coe, range_id, mfderivWithin_univ] at this

/-- The derivative of a chart of the `C^1` maximal atlas of a manifold modelled on its own model
space, read in the model space, is invertible at every point of the chart source. -/
theorem isInvertible_mvfderiv_chart (he : e ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) 1 M)
    {y : M} (hy : y ∈ e.source) : (mvfderiv 𝓘(𝕜, E) e y).IsInvertible := by
  -- `mvfderiv` is `mfderiv` followed by `fromTangentSpace`; both factors are invertible.
  unfold mvfderiv
  exact ContinuousLinearMap.IsInvertible.comp ⟨NormedSpace.fromTangentSpace (e y), rfl⟩
    (isInvertible_mfderiv_chart he hy)

/-- Where `f = h ∘ e` on the source of a chart `e` of the `C^1` maximal atlas, the differential of
`f` vanishes at `y` in the source if and only if the Fréchet derivative of `h` vanishes at `e y`. -/
theorem mfderiv_eq_zero_iff_of_eqOn (he : e ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) 1 M)
    (hfh : EqOn f (h ∘ e) e.source) {y : M} (hy : y ∈ e.source) :
    mfderiv 𝓘(𝕜, E) 𝓘(𝕜, F) f y = 0 ↔ fderiv 𝕜 h (e y) = 0 := by
  rw [mfderiv_eq_fderiv_comp_of_eqOn he hfh hy]
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
    exact ContinuousLinearMap.zero_comp _

/-- A map `g : M → F` has derivative `A` at `y` if and only if its expression
`g ∘ (chartAt E y)⁻¹` in the preferred chart at `y` has derivative `A` at the image of `y`. -/
theorem hasMFDerivAt_iff_hasFDerivAt_comp_chartAt_symm {g : M → F} {y : M} {A : E →L[𝕜] F} :
    HasMFDerivAt 𝓘(𝕜, E) 𝓘(𝕜, F) g y A ↔
      HasFDerivAt (g ∘ (chartAt E y).symm) A (chartAt E y y) := by
  simp only [HasMFDerivAt, writtenInExtChartAt, modelWithCornersSelf_coe, range_id, extChartAt,
    OpenPartialHomeomorph.extend, PartialEquiv.coe_trans_symm,
    OpenPartialHomeomorph.coe_toPartialEquiv_symm, PartialEquiv.coe_trans,
    OpenPartialHomeomorph.toFun_eq_coe, hasFDerivWithinAt_univ]
  -- The casts `tangentSpaceCastModel` identify the model spaces with their tangent spaces, and the
  -- continuity of `g` at `y` is that of its chart expression at the image of `y`.
  exact ⟨And.right, fun hA ↦ ⟨((chartAt E y).symm.continuousAt_iff_continuousAt_comp_right
    (mem_chart_source E y)).2 hA.continuousAt, hA⟩⟩

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
    {z : E} (hz : z ∈ (q.symm.trans q').source) : ContDiffAt 𝕜 n (q.symm.trans q') z :=
  contDiffAt_of_mem_contDiffGroupoid (IsManifold.compatible_of_mem_maximalAtlas hq hq') hz

/-- A transition map `q.symm.trans q'` between two charts of the maximal atlas is `C^n` on its
source. -/
theorem contDiffOn_symm_trans_of_mem_maximalAtlas {q' : OpenPartialHomeomorph M E}
    (hq : q ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M)
    (hq' : q' ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M) :
    ContDiffOn 𝕜 n (q.symm.trans q') (q.symm.trans q').source := fun _ hz ↦
  (contDiffAt_symm_trans_of_mem_maximalAtlas hq hq' hz).contDiffWithinAt

/-- **Chain rule for chart transitions.** Let `q` and `e` be open partial homeomorphisms from `M`
to `E` with `y` in the source of `q`, and read them through the preferred chart at `y`: if the
transition to `q` has an invertible derivative `A` at `chartAt E y y` and the transition to `e` has
a derivative `B` there, then the derivative at `q y` of the transition `e ∘ q⁻¹`, composed with
`A`, is `B`. -/
theorem fderiv_symm_trans_comp_eq {e : OpenPartialHomeomorph M E} {y : M}
    (hy : y ∈ q.source) {A : E ≃L[𝕜] E} {B : E →L[𝕜] E}
    (hA : HasFDerivAt ((chartAt E y).symm.trans q) (A : E →L[𝕜] E) (chartAt E y y))
    (hB : HasFDerivAt ((chartAt E y).symm.trans e) B (chartAt E y y)) :
    fderiv 𝕜 (q.symm.trans e) (q y) ∘L (A : E →L[𝕜] E) = B := by
  set τ := (chartAt E y).symm.trans q
  have hqy : q y ∈ τ.target := by simp [τ, q.map_source hy, q.left_inv hy]
  have hτy : τ.symm (q y) = chartAt E y y := by simp [τ, q.left_inv hy]
  have hτ := τ.hasFDerivAt_symm hqy (by rwa [hτy])
  rw [← hτy] at hB
  -- Near `q y`, the transition `e ∘ q⁻¹` is the transition to `e` after the inverse of `τ`.
  have hτe := (hB.comp (q y) hτ).congr_of_eventuallyEq (f₁ := q.symm.trans e) <| by
    filter_upwards [τ.open_target.mem_nhds hqy] with z hz
    have hz' : q.symm z ∈ (chartAt E y).source := by simpa [τ] using hz.2
    simp [τ, (chartAt E y).left_inv hz']
  rw [hτe.fderiv]
  ext v
  simp

/-- The inverse of a transition map `q.symm.trans q'` between two charts of the maximal atlas is
`C^n` at every point of its target. -/
theorem contDiffAt_symm_trans_symm_of_mem_maximalAtlas {q' : OpenPartialHomeomorph M E}
    (hq : q ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M) (hq' : q' ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M)
    {z : E} (hz : z ∈ (q.symm.trans q').target) : ContDiffAt 𝕜 n (q.symm.trans q').symm z :=
  contDiffAt_of_mem_contDiffGroupoid
    ((contDiffGroupoid n 𝓘(𝕜, E)).symm (IsManifold.compatible_of_mem_maximalAtlas hq hq')) hz

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

/-- A chart `q` of the maximal atlas, followed by the inverse of a linear isomorphism `L`, a
partial homeomorphism `ψ` that is `C^n` with `C^n` inverse, the translation by `-b` and a linear
isomorphism `K` back to the model, is again a chart of the maximal atlas. -/
theorem exists_trans_mem_maximalAtlas_of_contDiffOn {E₁ E₂ : Type*} [NormedAddCommGroup E₁]
    [NormedSpace 𝕜 E₁] [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
    (hq : q ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M) (L : E₁ ≃L[𝕜] E)
    (ψ : OpenPartialHomeomorph E₁ E₂) (hψ : ContDiffOn 𝕜 n ψ ψ.source)
    (hψinv : ContDiffOn 𝕜 n ψ.symm ψ.target) (K : E₂ ≃L[𝕜] E) (b : E₂) :
    ∃ Φ : OpenPartialHomeomorph E E, (∀ w, Φ w = K (ψ (L.symm w) - b)) ∧
      Φ.source = L.symm ⁻¹' ψ.source ∧ q.trans Φ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M := by
  let Φ : OpenPartialHomeomorph E E :=
    (L.symm.toHomeomorph.toOpenPartialHomeomorph.trans ψ).trans
      ((Homeomorph.subRight b).trans K.toHomeomorph).toOpenPartialHomeomorph
  have hΦsrc : Φ.source = L.symm ⁻¹' ψ.source := by simp [Φ]
  have hΦtgt : Φ.target = (fun w ↦ K.symm w + b) ⁻¹' ψ.target := by
    ext w
    simp [Φ]
  refine ⟨Φ, fun _ ↦ rfl, hΦsrc, trans_mem_maximalAtlas_of_contDiffAt hq (fun z hz ↦ ?_)
    (fun z hz ↦ ?_)⟩
  · rw [hΦsrc] at hz
    have hψz : ContDiffAt 𝕜 n ψ (L.symm z) := (hψ _ hz).contDiffAt (ψ.open_source.mem_nhds hz)
    exact K.contDiff.contDiffAt.comp z ((hψz.comp z L.symm.contDiff.contDiffAt).sub
      contDiffAt_const)
  · rw [hΦtgt] at hz
    have hψz : ContDiffAt 𝕜 n ψ.symm (K.symm z + b) :=
      (hψinv _ hz).contDiffAt (ψ.open_target.mem_nhds hz)
    exact L.contDiff.contDiffAt.comp z
      (hψz.comp z (K.symm.contDiff.contDiffAt.add contDiffAt_const))

end MaximalAtlas

section FDeriv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {n : WithTop ℕ∞}
  {q q' : OpenPartialHomeomorph M E}

/-- The transition map `q.symm.trans q'` between two charts of the `C^n` maximal atlas, `n ≠ 0`,
has an invertible derivative at each point of its source. -/
theorem exists_hasFDerivAt_symm_trans (hn : n ≠ 0)
    (hq : q ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M) (hq' : q' ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M)
    {z : E} (hz : z ∈ (q.symm.trans q').source) :
    ∃ A : E ≃L[𝕜] E, HasFDerivAt (q.symm.trans q') (A : E →L[𝕜] E) z :=
  OpenPartialHomeomorph.exists_hasFDerivAt_of_chart _ hz
    ((contDiffAt_symm_trans_of_mem_maximalAtlas hq hq' hz).differentiableAt hn)
    ((contDiffAt_symm_trans_symm_of_mem_maximalAtlas hq hq'
      ((q.symm.trans q').map_source hz)).differentiableAt hn)

/-- The derivative of the transition map `q.symm.trans q'` between two charts of the `C^n` maximal
atlas, `n ≠ 0`, has nonzero determinant at each point of its source. -/
theorem det_fderiv_symm_trans_ne_zero (hn : n ≠ 0)
    (hq : q ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M) (hq' : q' ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M)
    {z : E} (hz : z ∈ (q.symm.trans q').source) :
    (fderiv 𝕜 (q.symm.trans q') z).det ≠ 0 := by
  obtain ⟨A, hA⟩ := exists_hasFDerivAt_symm_trans hn hq hq' hz
  rw [hA.fderiv]
  exact A.toLinearEquiv.isUnit_det'.ne_zero

/-- The transition map `q.symm.trans q'` from a chart `q` of the atlas to a chart `q'` of the
`C^n` maximal atlas, `n ≠ 0`, has an invertible derivative at each point of its source. Since `q`
is in the atlas, its membership in the `C^n` maximal atlas, which `exists_hasFDerivAt_symm_trans`
takes as a hypothesis and which in general comes from an `IsManifold` instance, is not needed. -/
theorem exists_hasFDerivAt_symm_trans_of_mem_atlas (hn : n ≠ 0) (hq : q ∈ atlas E M)
    (hq' : q' ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M)
    {z : E} (hz : z ∈ (q.symm.trans q').source) :
    ∃ A : E ≃L[𝕜] E, HasFDerivAt (q.symm.trans q') (A : E →L[𝕜] E) z :=
  have h := (hq' q hq).2
  OpenPartialHomeomorph.exists_hasFDerivAt_of_chart _ hz
    ((contDiffAt_of_mem_contDiffGroupoid h hz).differentiableAt hn)
    ((contDiffAt_of_mem_contDiffGroupoid ((contDiffGroupoid n 𝓘(𝕜, E)).symm h)
      ((q.symm.trans q').map_source hz)).differentiableAt hn)

end FDeriv

section StrictFDeriv

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {n : WithTop ℕ∞}
  {q q' : OpenPartialHomeomorph M E}

/-- Over `ℝ` or `ℂ`, the invertible derivative of `exists_hasFDerivAt_symm_trans` is strict. -/
theorem exists_hasStrictFDerivAt_symm_trans (hn : n ≠ 0)
    (hq : q ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M) (hq' : q' ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M)
    {z : E} (hz : z ∈ (q.symm.trans q').source) :
    ∃ A : E ≃L[𝕜] E, HasStrictFDerivAt (q.symm.trans q') (A : E →L[𝕜] E) z := by
  obtain ⟨A, hA⟩ := exists_hasFDerivAt_symm_trans hn hq hq' hz
  exact ⟨A, (contDiffAt_symm_trans_of_mem_maximalAtlas hq hq' hz).hasStrictFDerivAt hA hn⟩

/-- In charts `q` and `q'` of the maximal atlas around `y`, the parametrization
`z ↦ q.symm (q y + z)` of a subspace `F` is strictly differentiable at `0` in the chart `q'`, with
derivative the derivative of the transition `q' ∘ q.symm` at `q y` restricted to `F`. -/
theorem hasStrictFDerivAt_comp_symm_add_subtypeL {y : M} (hn : n ≠ 0)
    (hq : q ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M)
    (hq' : q' ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M)
    (hyq : y ∈ q.source) (hyq' : y ∈ q'.source) (F : Submodule 𝕜 E) :
    HasStrictFDerivAt (fun z : F ↦ q' (q.symm (q y + (z : E))))
      (fderiv 𝕜 (q.symm.trans q') (q y) ∘L F.subtypeL) 0 := by
  have hyτ : q y ∈ (q.symm.trans q').source := by
    simp [q.map_source hyq, q.left_inv hyq, hyq']
  have hτ : HasStrictFDerivAt (q.symm.trans q') (fderiv 𝕜 (q.symm.trans q') (q y))
      (q y + ((0 : F) : E)) := by
    simpa using (contDiffAt_symm_trans_of_mem_maximalAtlas hq hq' hyτ).hasStrictFDerivAt_fderiv hn
  have hlin : HasStrictFDerivAt (fun z : F ↦ q y + (z : E)) F.subtypeL 0 :=
    F.subtypeL.hasStrictFDerivAt.const_add _
  exact HasStrictFDerivAt.comp (f := fun z : F ↦ q y + (z : E)) 0 hτ hlin

end StrictFDeriv

section Preferred

/-- On the source of the preferred chart at `p`, `f` agrees with its coordinate expression
`f ∘ (chartAt E p).symm` read through the chart. -/
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

/-- The points where the differential of a `C^1` function is nonzero form an open set. -/
theorem isOpen_setOf_mfderiv_ne_zero (hf : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, F) 1 f) :
    IsOpen {y : M | mfderiv 𝓘(𝕜, E) 𝓘(𝕜, F) f y ≠ 0} := by
  refine isOpen_iff_mem_nhds.2 fun y₀ hy₀ ↦ ?_
  set c := chartAt E y₀
  have hcont : ContinuousOn (fderiv 𝕜 (f ∘ c.symm)) c.target :=
    (contDiffOn_comp_chartAt_symm hf y₀).continuousOn_fderiv_of_isOpen c.open_target le_rfl
  have hmem : y₀ ∈ c.source := mem_chart_source E y₀
  have hiff : ∀ y ∈ c.source, mfderiv 𝓘(𝕜, E) 𝓘(𝕜, F) f y = 0 ↔ fderiv 𝕜 (f ∘ c.symm) (c y) = 0 :=
    fun y hy ↦ mfderiv_eq_zero_iff_of_eqOn (IsManifold.chart_mem_maximalAtlas y₀)
      (eqOn_comp_chartAt_symm y₀) hy
  have h0 : fderiv 𝕜 (f ∘ c.symm) (c y₀) ≠ 0 := fun h ↦ hy₀ ((hiff y₀ hmem).2 h)
  have hca : ContinuousAt (fderiv 𝕜 (f ∘ c.symm)) (c y₀) :=
    hcont.continuousAt (c.open_target.mem_nhds (c.map_source hmem))
  have hev : ∀ᶠ y in 𝓝 y₀, fderiv 𝕜 (f ∘ c.symm) (c y) ≠ 0 :=
    (hca.comp (c.continuousAt hmem)).eventually_ne h0
  filter_upwards [hev, c.open_source.mem_nhds hmem] with y hy hys
  exact fun h ↦ hy ((hiff y hys).1 h)

end Preferred

section Dual

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- **The transformation law of covectors under a change of chart.** The frequency in the chart
`e₂` of the covector `⟪η, ·⟫ ∘ de₁_x` is the image of `η` under the inverse adjoint of the
derivative of the transition `e₂ ∘ e₁⁻¹` at `e₁ x`. -/
theorem toDual_symm_comp_inverse_mvfderiv {e₁ e₂ : OpenPartialHomeomorph M E}
    (he₁ : e₁ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M)
    (he₂ : e₂ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M)
    {x : M} (hx₁ : x ∈ e₁.source) (hx₂ : x ∈ e₂.source) (η : E) :
    (InnerProductSpace.toDual ℝ E).symm
        (((innerSL ℝ η).comp (mvfderiv 𝓘(ℝ, E) e₁ x)).comp (mvfderiv 𝓘(ℝ, E) e₂ x).inverse) =
      ContinuousLinearMap.adjoint (Ring.inverse (fderiv ℝ (e₁.symm.trans e₂) (e₁ x))) η := by
  have hxκ : e₁ x ∈ (e₁.symm.trans e₂).source := by
    simp [e₁.map_source hx₁, e₁.left_inv hx₁, hx₂]
  obtain ⟨A, hA⟩ := exists_hasFDerivAt_symm_trans one_ne_zero he₁ he₂ hxκ
  -- The chain rule: `de₂_x = A ∘ de₁_x`.
  have hD : ∀ w, A (mvfderiv 𝓘(ℝ, E) e₁ x w) = mvfderiv 𝓘(ℝ, E) e₂ x w := fun w ↦ by
    have h := OpenPartialHomeomorph.mvfderiv_eq_fderiv_symm_trans_comp hxκ
      (by rw [e₁.left_inv hx₁]; exact mdifferentiableAt_of_mem_maximalAtlas he₁ hx₁)
      hA.differentiableAt
    rw [e₁.left_inv hx₁, hA.fderiv] at h
    exact (DFunLike.congr_fun h w).symm
  rw [hA.fderiv, ContinuousLinearMap.ringInverse_eq_inverse, ContinuousLinearMap.inverse_equiv,
    LinearIsometryEquiv.symm_apply_eq]
  ext v
  simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  congr 1
  refine A.injective ?_
  simpa using (hD _).trans ((isInvertible_mvfderiv_chart he₂ hx₂).self_apply_inverse v)

omit [ChartedSpace E M] in
/-- The inverse adjoint of the derivative of the transition `e ∘ e⁻¹` from a chart to itself is the
identity at every point of the chart target. -/
theorem adjoint_ringInverse_fderiv_comp_symm_eq_one {e : OpenPartialHomeomorph M E} {y : E}
    (hy : y ∈ e.target) :
    ContinuousLinearMap.adjoint (Ring.inverse (fderiv ℝ (e ∘ e.symm) y)) = 1 := by
  have hid : (e ∘ e.symm : E → E) =ᶠ[𝓝 y] id := e.eventually_right_inverse hy
  rw [hid.fderiv_eq, fderiv_id, ← ContinuousLinearMap.one_def, Ring.inverse_one,
    ContinuousLinearMap.adjoint_one]

omit [CompleteSpace E] in
/-- The covector `⟪η, ·⟫ ∘ de_x` read through a chart `e` at `x` vanishes exactly when `η = 0`,
since `de_x` is invertible. -/
theorem innerSL_comp_mvfderiv_eq_zero_iff {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M) {x : M} (hx : x ∈ e.source) {η : E} :
    (innerSL ℝ η).comp (mvfderiv 𝓘(ℝ, E) e x) = 0 ↔ η = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  have h' := DFunLike.congr_fun h ((mvfderiv 𝓘(ℝ, E) e x).inverse η)
  simpa [(isInvertible_mvfderiv_chart he hx).self_apply_inverse] using h'

/-- A covector `ξ ∈ T*ₓM` is `⟪η, ·⟫ ∘ de_x` for the frequency `η` dual to `ξ ∘ (de_x)⁻¹`. -/
theorem innerSL_toDual_symm_comp_inverse_mvfderiv {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M) {x : M} (hx : x ∈ e.source)
    (ξ : TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ) :
    (innerSL ℝ ((InnerProductSpace.toDual ℝ E).symm
      (ξ.comp (mvfderiv 𝓘(ℝ, E) e x).inverse))).comp (mvfderiv 𝓘(ℝ, E) e x) = ξ := by
  ext v
  simp [InnerProductSpace.toDual_symm_apply, (isInvertible_mvfderiv_chart he hx).inverse_apply_self]

/-- The frequency `η` dual to `ξ ∘ (de_x)⁻¹` of a nonzero covector `ξ ∈ T*ₓM` is nonzero, since
`⟪η, ·⟫ ∘ de_x = ξ`. -/
theorem toDual_symm_comp_inverse_mvfderiv_ne_zero {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M) {x : M} (hx : x ∈ e.source)
    {ξ : TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ} (hξ : ξ ≠ 0) :
    (InnerProductSpace.toDual ℝ E).symm (ξ.comp (mvfderiv 𝓘(ℝ, E) e x).inverse) ≠ 0 :=
  fun h ↦ hξ <| by
    rw [← innerSL_toDual_symm_comp_inverse_mvfderiv he hx ξ, h, map_zero,
      ContinuousLinearMap.zero_comp]

end Dual

end TauCeti

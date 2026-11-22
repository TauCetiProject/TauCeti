/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.ChangeOfVariables
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution
import Mathlib.Analysis.Calculus.Deriv.Abs
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.FDeriv.Det.Basic
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.VectorValued
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartLocalization
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Local Sobolev regularity of distributions on manifolds

Let `V → M` be a smooth real vector bundle over a smooth manifold modelled on a finite-dimensional
real inner product space `E`, and let `T` be a real continuous linear functional on the bundle tests
`TauCeti.BundleTest I F V`, for instance a distributional section of a bundle
(`TauCeti.BundleDistribution`). In a smooth chart `c` with smooth inverse and a bundle frame `t`
over its source, `T` has a local representative on the chart target
(`Bundle.Trivialization.chartDistributionCLM`), a distribution with values in the dual of the model
fibre `F`. Its component along `v : F` is the complex distribution `φ ↦ T (φ • v)` on the chart
target, the test function `φ • v` being extended to a bundle test through the chart and the frame.
The functional `T` is **`H^s` near `x`** (`TauCeti.BundleTest.IsLocallySobolevAt`) when, in some
such chart at `x` and frame, all these components are `H^s` near `c x`
(`Distribution.IsLocallySobolevAt`). This is the local Sobolev space `H^s_loc` of distributions
on a manifold with values in a bundle, defined pointwise; its complement is the **`H^s` singular
support** of `T` (`TauCeti.BundleTest.sobolevSingularSupport`).

The main result is that the chart and the frame do not matter: for two charts `c`, `c'` with
frames `t`, `t'` and a point `x` of both chart sources, all components in `(t', c')` are `H^s`
near `c' x` exactly when all components in `(t, c)` are `H^s` near `c x`
(`Bundle.Trivialization.forall_isLocallySobolevAt_chartDistributionCLM_iff`). Hence `T` is `H^s`
near `x` exactly when its components are `H^s` near `c x` in any chart `c` at `x` and any frame
(`TauCeti.BundleTest.isLocallySobolevAt_iff`).

## The argument

Near `c' x`, a test function `φ • v` read in the chart `c'` and the frame `t'` is the bundle test
`p ↦ φ(c' p) t'⁻¹(v)`. Over the overlap of the two charts this is `t⁻¹(φ(c' p) G(p) v)` for the
change of frame `G = t ∘ t'⁻¹`, that is, the test function `z ↦ φ(κ⁻¹ z) G(c⁻¹ z) v` read in the
chart `c` and the frame `t`, where `κ = c ∘ c'⁻¹` is the chart transition. Writing `G v` in a basis
`(bⱼ)` of `F`, and the composition with `κ⁻¹` as the pushforward of test densities along `κ`, which
carries the Jacobian `|det Dκ⁻¹|` (`TestFunction.pushforwardCLM`), gives near `c' x`

`S'_v = ∑ⱼ gⱼ κ^* S_{bⱼ}`, with `gⱼ = |det Dκ| · bⱼ*(G(c'⁻¹ ·) v)`,

where `S` and `S'` are the components in `(t, c)` and in `(t', c')` and `κ^*` is the pullback of
distributions (`Distribution.compCLMOfOpenPartialHomeomorph`). The pullback preserves local
Sobolev regularity (`Distribution.isLocallySobolevAt_compCLMOfOpenPartialHomeomorph_iff`), and so
do smooth multiples and finite sums. Exchanging the roles of the two charts gives the converse.

## Main declarations

* `Bundle.Trivialization.forall_isLocallySobolevAt_chartDistributionCLM_iff`: local Sobolev
  regularity of all components does not depend on the chart and the frame.
* `TauCeti.BundleTest.IsLocallySobolevAt`: the functional `T` is `H^s` near a point of `M`, and
  `TauCeti.BundleTest.isLocallySobolevAt_iff`, its characterization in every chart and frame.
* `TauCeti.BundleTest.sobolevSingularSupport`: the `H^s` singular support, a closed subset of `M`
  (`TauCeti.BundleTest.isClosed_sobolevSingularSupport`) growing with `s`, with the rules for
  sums, differences, negatives and scalar multiples.
* `TauCeti.BundleTest.exists_forall_isLocallySobolevAt`: on a manifold without boundary every
  functional on bundle tests has a finite Sobolev order near every compact set.
* `TauCeti.BundleTest.sobolevSingularSupport_delta`,
  `TauCeti.BundleTest.sobolevSingularSupport_delta_eq_empty`: in dimension `d > 0` the point mass
  `δ_x ℓ` with `ℓ ≠ 0` has `H^s` singular support `{x}` for `s ≥ -d / 2`, and it is `H^s`
  everywhere for `s < -d / 2`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  Appendix B.1 (the local Sobolev spaces `H^s_loc` on manifolds, defined chart by chart).
* M. Taylor, *Partial Differential Equations I*, second edition, Springer, 2011, Chapter 4, §3
  (Sobolev spaces on manifolds and their invariance under coordinate changes).
-/

public section

noncomputable section

open Set Filter Function TopologicalSpace Complex Distribution ContinuousLinearMap
open scoped Manifold ContDiff Distributions Topology CompactConvergenceCLM

namespace Bundle.Trivialization

open TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]
  {t t' : Trivialization F (π F V)} [MemTrivializationAtlas t] [MemTrivializationAtlas t']
  {c c' : OpenPartialHomeomorph M E}
  {hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source} {hct : c.source ⊆ t.baseSet}
  {hc' : ContMDiffOn I 𝓘(ℝ, E) ∞ c' c'.source} {hct' : c'.source ⊆ t'.baseSet}

omit [MeasurableSpace E] [BorelSpace E] in
/-- The local representative of `T` in `(t', c')`, tested against `φ • v`, is the sum over the
standard basis `(bⱼ)` of `F` of the local representatives in `(t, c)` tested against
`(κ_* (gⱼ φ)) • bⱼ`, where `κ = c ∘ c'⁻¹` is the chart transition, `φ` is supported in an open set
`B` of its source, and the smooth functions `gⱼ` equal `|det Dκ| bⱼ*(G(c'⁻¹ ·) v)` on `B` for the
change of frame `G = t ∘ t'⁻¹`. -/
private theorem chartTestCLM_eq_sum (v : F)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) (c'.symm.trans c) (c'.symm.trans c).source)
    (he' : ContDiffOn ℝ (⊤ : ℕ∞) (c'.symm.trans c).symm (c'.symm.trans c).target)
    {B : Opens E} (hB : (B : Set E) ⊆ (c'.symm.trans c).source)
    (hBc : MapsTo (c'.symm.trans c) B (⟨c.target, c.open_target⟩ : Opens E))
    {g : Fin (Module.finrank ℝ F) → E → ℝ} (hg : ∀ j, ContDiff ℝ ∞ (g j))
    (hgB : ∀ j, ∀ y ∈ B, g j y = |(fderiv ℝ (c'.symm.trans c) y).det| *
      (Module.finBasis ℝ F).coord j (t'.coordChangeL ℝ t (c'.symm y) v)) (φ : 𝓓(B, ℝ)) :
    t'.chartTestCLM c' hc' hct'
        (TestFunction.postcompCLM (toSpanSingleton ℝ v) (TestFunction.monoCLM ℝ φ)) =
      ∑ j, t.chartTestCLM c hc hct (TestFunction.postcompCLM
        (toSpanSingleton ℝ (Module.finBasis ℝ F j)) (TestFunction.pushforwardCLM
          (c'.symm.trans c) he he' hB hBc (TestFunction.smulLeftCLM (hg j) φ))) := by
  set b := Module.finBasis ℝ F
  have hφ (y : E) (hy : y ∉ (B : Set E)) : φ y = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hy (φ.tsupport_subset h)
  have hmono : ⇑(TestFunction.monoCLM ℝ φ : 𝓓(⟨c'.target, c'.open_target⟩, ℝ)) = φ := by
    simp [show B ≤ ⟨c'.target, c'.open_target⟩ from fun _ hy ↦ (hB hy).1]
  rw [← map_sum]
  refine BundleTest.ext fun x ↦ ?_
  by_cases hx' : x ∈ c'.source
  · rw [chartTestCLM_apply_of_mem _ _ _ _ _ hx']
    simp only [TestFunction.postcompCLM_apply, Function.comp_apply, toSpanSingleton_apply, hmono]
    by_cases hx : x ∈ c.source
    · rw [chartTestCLM_apply_of_mem _ _ _ _ _ hx, _root_.sum_apply]
      have hκs : c' x ∈ (c'.symm.trans c).source := by
        simpa [c'.left_inv hx'] using ⟨c'.map_source hx', hx⟩
      have hκx : (c'.symm.trans c) (c' x) = c x := by simp [c'.left_inv hx']
      have hκt : c x ∈ (c'.symm.trans c).target := hκx ▸ (c'.symm.trans c).map_source hκs
      have hκsx : (c'.symm.trans c).symm (c x) = c' x := by
        rw [← hκx, (c'.symm.trans c).left_inv hκs]
      simp only [TestFunction.postcompCLM_apply, Function.comp_apply, toSpanSingleton_apply,
        TestFunction.pushforwardCLM_apply_of_mem _ hκt, hκsx, TestFunction.smulLeftCLM_apply,
        smul_eq_mul]
      by_cases hB' : c' x ∈ B
      · have hdet := (c'.symm.trans c).det_fderiv_symm_apply_of_contDiffOn he he' (by simp) hκs
        have hne := (c'.symm.trans c).det_fderiv_ne_zero_of_contDiffOn he he' (by simp) hκs
        rw [hκx] at hdet
        -- The Jacobians cancel, and the coordinates of `G x v` reassemble `G x v`.
        have hsum : ∑ j, (|(fderiv ℝ (c'.symm.trans c) (c' x)).det|⁻¹ *
            (|(fderiv ℝ (c'.symm.trans c) (c' x)).det| *
            b.coord j (t'.coordChangeL ℝ t x v) * φ (c' x))) • b j =
            φ (c' x) • t'.coordChangeL ℝ t x v := by
          conv_rhs => rw [← b.sum_repr (t'.coordChangeL ℝ t x v), Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [smul_smul, Module.Basis.coord_apply]
          congr 1
          field_simp
        simp only [hgB _ _ hB', c'.left_inv hx', hdet, abs_inv, hsum, map_smul,
          t.symmL_coordChangeL ℝ t' ⟨hct' hx', hct hx⟩]
      · simp [hφ _ hB']
    · rw [chartTestCLM_apply_of_notMem _ _ _ _ _ hx]
      have hB' : c' x ∉ B := fun h ↦ hx (by simpa [c'.left_inv hx'] using (hB h).2)
      simp [hφ _ hB']
  · rw [chartTestCLM_apply_of_notMem _ _ _ _ _ hx']
    by_cases hx : x ∈ c.source
    · rw [chartTestCLM_apply_of_mem _ _ _ _ _ hx, _root_.sum_apply]
      have hκt : c x ∉ (c'.symm.trans c).target := fun h ↦
        hx' (by simpa [c.left_inv hx] using h.2)
      simp [TestFunction.pushforwardCLM_apply_of_notMem _ hκt]
    · rw [chartTestCLM_apply_of_notMem _ _ _ _ _ hx]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Near a point of the source of the chart transition `κ = c ∘ c'⁻¹`, the component along `v` of
the local representative in `(t', c')` is `∑ⱼ gⱼ κ^* S_{bⱼ}`, where `S_{bⱼ}` are the components in
`(t, c)` along the standard basis of `F` and `gⱼ` are the smooth coefficients of
`chartTestCLM_eq_sum`. -/
private theorem restrictCLM_mapCLM_chartDistributionCLM_eq_sum (T : BundleTest I F V →L_c[ℝ] ℝ)
    (v : F) (he : ContDiffOn ℝ (⊤ : ℕ∞) (c'.symm.trans c) (c'.symm.trans c).source)
    (he' : ContDiffOn ℝ (⊤ : ℕ∞) (c'.symm.trans c).symm (c'.symm.trans c).target)
    {B : Opens E} (hB : (B : Set E) ⊆ (c'.symm.trans c).source)
    (hBc : MapsTo (c'.symm.trans c) B (⟨c.target, c.open_target⟩ : Opens E))
    {g : Fin (Module.finrank ℝ F) → E → ℝ} (hg : ∀ j, ContDiff ℝ ∞ (g j))
    (hgB : ∀ j, ∀ y ∈ B, g j y = |(fderiv ℝ (c'.symm.trans c) y).det| *
      (Module.finBasis ℝ F).coord j (t'.coordChangeL ℝ t (c'.symm y) v)) :
    (restrictCLM (mapCLM (ofRealCLM ∘L ContinuousLinearMap.apply ℝ ℝ v)
        (t'.chartDistributionCLM c' hc' hct' T)) : 𝓓'(B, ℂ)) =
      ∑ j, Distribution.smulLeftCLM (hg j)
        (compCLMOfOpenPartialHomeomorph (c'.symm.trans c) he he' hB hBc
          (mapCLM (ofRealCLM ∘L ContinuousLinearMap.apply ℝ ℝ (Module.finBasis ℝ F j))
            (t.chartDistributionCLM c hc hct T))) := by
  ext φ
  simp only [restrictCLM_apply, mapCLM_apply, chartDistributionCLM_apply_apply, coe_comp,
    Function.comp_apply, ContinuousLinearMap.apply_apply, ofRealCLM_apply, _root_.sum_apply,
    Distribution.smulLeftCLM_apply, compCLMOfOpenPartialHomeomorph_apply]
  rw [← Complex.ofReal_sum, ← map_sum,
    chartTestCLM_eq_sum (hc := hc) (hct := hct) v he he' hB hBc hg hgB φ]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [T2Space M] [IsManifold I ∞ M] in
include hct hct' in
/-- The coefficient `z ↦ |det Dκ(z)| bⱼ*(G(c'⁻¹ z) v)` of the change of chart and frame is smooth
on the source of the transition `κ = c ∘ c'⁻¹`, where `G = t ∘ t'⁻¹` is the change of frame. -/
private theorem contDiffOn_transitionCoeff
    (he : ContDiffOn ℝ (⊤ : ℕ∞) (c'.symm.trans c) (c'.symm.trans c).source)
    (he' : ContDiffOn ℝ (⊤ : ℕ∞) (c'.symm.trans c).symm (c'.symm.trans c).target)
    (hcs' : ContMDiffOn 𝓘(ℝ, E) I ∞ c'.symm c'.target) (v : F) (j : Fin (Module.finrank ℝ F)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z ↦ |(fderiv ℝ (c'.symm.trans c) z).det| *
      (Module.finBasis ℝ F).coord j (t'.coordChangeL ℝ t (c'.symm z) v))
      (c'.symm.trans c).source := by
  set κ := c'.symm.trans c
  have hdet : ContDiffOn ℝ (⊤ : ℕ∞) (fun z ↦ |(fderiv ℝ κ z).det|) κ.source := fun z hz ↦
    (ContDiffAt.comp (g := fun r : ℝ ↦ |r|) z
      (contDiffAt_abs (κ.det_fderiv_ne_zero_of_contDiffOn he he' (by simp) hz))
      (ContinuousLinearMap.contDiff_det.contDiffAt.comp z
        ((he.fderiv_of_isOpen κ.open_source (by simp)).contDiffAt
          (κ.open_source.mem_nhds hz)))).contDiffWithinAt
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) (fun z ↦ (t'.coordChangeL ℝ t (c'.symm z) : F →L[ℝ] F))
      κ.source :=
    contMDiffOn_iff_contDiffOn.1 ((contMDiffOn_coordChangeL (IB := I) t' t).comp
      (hcs'.mono fun z hz ↦ hz.1) fun z hz ↦ ⟨hct' (c'.map_target hz.1), hct hz.2⟩)
  have hcoord := (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ F).coord j)).contDiff
    (n := (⊤ : ℕ∞))
  exact hdet.mul (hcoord.comp_contDiffOn (hG.clm_apply contDiffOn_const))

/-- If every component of the local representative in `(t, c)` is `H^s` near `κ y`, for the
transition `κ = c ∘ c'⁻¹`, then every component in `(t', c')` is `H^s` near `y`. -/
private theorem isLocallySobolevAt_mapCLM_chartDistributionCLM_of_forall
    (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hcs' : ContMDiffOn 𝓘(ℝ, E) I ∞ c'.symm c'.target) (T : BundleTest I F V →L_c[ℝ] ℝ) {s : ℝ}
    {y : E} (hy : y ∈ (c'.symm.trans c).source)
    (h : ∀ w, (mapCLM (ofRealCLM ∘L ContinuousLinearMap.apply ℝ ℝ w)
      (t.chartDistributionCLM c hc hct T)).IsLocallySobolevAt s (c'.symm.trans c y)) (v : F) :
    (mapCLM (ofRealCLM ∘L ContinuousLinearMap.apply ℝ ℝ v)
      (t'.chartDistributionCLM c' hc' hct' T)).IsLocallySobolevAt s y := by
  have he := OpenPartialHomeomorph.contDiffOn_symm_trans hc hcs'
  have he' : ContDiffOn ℝ ∞ (c'.symm.trans c).symm (c'.symm.trans c).target := by
    rw [← OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
    exact OpenPartialHomeomorph.contDiffOn_symm_trans hc' hcs
  -- A neighbourhood `B` of `y` with compact closure in the source of the transition.
  obtain ⟨W, hWo, hyW, hWs, hWc⟩ := exists_open_between_and_isCompact_closure isCompact_singleton
    (c'.symm.trans c).open_source (singleton_subset_iff.2 hy)
  let B : Opens E := ⟨W, hWo⟩
  have hB : (B : Set E) ⊆ (c'.symm.trans c).source := subset_closure.trans hWs
  have hBc : MapsTo (c'.symm.trans c) B (⟨c.target, c.open_target⟩ : Opens E) :=
    fun z hz ↦ ((c'.symm.trans c).map_source (hB hz)).1
  have hBt : B ≤ ⟨c'.target, c'.open_target⟩ := fun z hz ↦ (hB hz).1
  have hyB : y ∈ B := singleton_subset_iff.1 hyW
  -- Globally smooth coefficients agreeing with those of the change of chart and frame on `B`.
  choose g hg _ _ _ hgf using fun j ↦
    (contDiffOn_transitionCoeff (hct := hct) (hct' := hct') he he' hcs' v
      j).exists_contDiff_eventuallyEq_on_isCompact hWc (c'.symm.trans c).open_source hWs
  have hgB (j) (z) (hz : z ∈ B) := (hgf j z (subset_closure hz)).eq_of_nhds
  rw [← isLocallySobolevAt_restrictCLM_iff hBt hyB,
    restrictCLM_mapCLM_chartDistributionCLM_eq_sum (hc := hc) (hct := hct) T v he he' hB hBc hg
      hgB]
  exact Distribution.IsLocallySobolevAt.sum hyB fun j _ ↦
    ((isLocallySobolevAt_compCLMOfOpenPartialHomeomorph_iff hyB).2 (h _)).smulLeftCLM (hg j)

/-- **Independence of the chart and the frame.** Let `c` and `c'` be smooth charts with smooth
inverses, with frames `t` and `t'` over their sources, and let `x` be a point of both chart
sources. All components of the local representative of `T` in `(t', c')` are `H^s` near `c' x`
exactly when all components in `(t, c)` are `H^s` near `c x`. -/
theorem forall_isLocallySobolevAt_chartDistributionCLM_iff
    (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hcs' : ContMDiffOn 𝓘(ℝ, E) I ∞ c'.symm c'.target) (T : BundleTest I F V →L_c[ℝ] ℝ)
    {s : ℝ} {x : M} (hx : x ∈ c.source) (hx' : x ∈ c'.source) :
    (∀ v, (mapCLM (ofRealCLM ∘L ContinuousLinearMap.apply ℝ ℝ v)
      (t'.chartDistributionCLM c' hc' hct' T)).IsLocallySobolevAt s (c' x)) ↔
      ∀ v, (mapCLM (ofRealCLM ∘L ContinuousLinearMap.apply ℝ ℝ v)
        (t.chartDistributionCLM c hc hct T)).IsLocallySobolevAt s (c x) := by
  have key {t₁ t₂ : Trivialization F (π F V)} [MemTrivializationAtlas t₁]
      [MemTrivializationAtlas t₂] {c₁ c₂ : OpenPartialHomeomorph M E}
      (hc₁ : ContMDiffOn I 𝓘(ℝ, E) ∞ c₁ c₁.source) (hct₁ : c₁.source ⊆ t₁.baseSet)
      (hc₂ : ContMDiffOn I 𝓘(ℝ, E) ∞ c₂ c₂.source) (hct₂ : c₂.source ⊆ t₂.baseSet)
      (hcs₁ : ContMDiffOn 𝓘(ℝ, E) I ∞ c₁.symm c₁.target)
      (hcs₂ : ContMDiffOn 𝓘(ℝ, E) I ∞ c₂.symm c₂.target) (hx₁ : x ∈ c₁.source)
      (hx₂ : x ∈ c₂.source)
      (h : ∀ v, (mapCLM (ofRealCLM ∘L ContinuousLinearMap.apply ℝ ℝ v)
        (t₁.chartDistributionCLM c₁ hc₁ hct₁ T)).IsLocallySobolevAt s (c₁ x)) (v : F) :
      (mapCLM (ofRealCLM ∘L ContinuousLinearMap.apply ℝ ℝ v)
        (t₂.chartDistributionCLM c₂ hc₂ hct₂ T)).IsLocallySobolevAt s (c₂ x) := by
    have hy : c₂ x ∈ (c₂.symm.trans c₁).source := by
      simpa [c₂.left_inv hx₂] using ⟨c₂.map_source hx₂, hx₁⟩
    have hyx : c₂.symm.trans c₁ (c₂ x) = c₁ x := by simp [c₂.left_inv hx₂]
    exact isLocallySobolevAt_mapCLM_chartDistributionCLM_of_forall (t := t₁) (hc := hc₁)
      (hct := hct₁) (t' := t₂) (hc' := hc₂) (hct' := hct₂) hcs₁ hcs₂ T hy (hyx ▸ h) v
  exact ⟨key hc' hct' hc hct hcs' hcs hx' hx, key hc hct hc' hct' hcs hcs' hx hx'⟩

end Bundle.Trivialization

/-! ### Local Sobolev regularity on the manifold -/

namespace TauCeti.BundleTest

open Bundle Bundle.Trivialization

variable {E H M F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]

/-- A real functional `T` on bundle tests is **`H^s` near `x`** if, in some smooth chart `c` at `x`
with smooth inverse and some frame `t` over its source, the component `φ ↦ T (φ • v)` of the local
representative of `T` along every `v : F` is `H^s` near `c x`. The chart and the frame do not
matter (`TauCeti.BundleTest.isLocallySobolevAt_iff`).

The notion is meant for a boundaryless model `I`, where such charts exist at every point. At a
boundary point of a manifold with boundary there is no chart into `E`, and `T` is never `H^s`
there. -/
def IsLocallySobolevAt (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) (x : M) : Prop :=
  ∃ (t : Trivialization F (π F V)) (_ : MemTrivializationAtlas t) (c : OpenPartialHomeomorph M E)
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (_ : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hct : c.source ⊆ t.baseSet), x ∈ c.source ∧
    ∀ v, (mapCLM (ofRealCLM ∘L ContinuousLinearMap.apply ℝ ℝ v)
      (t.chartDistributionCLM c hc hct T)).IsLocallySobolevAt s (c x)

/-- **Local Sobolev regularity in any chart and frame.** For a smooth chart `c` at `x` with smooth
inverse and a frame `t` over its source, `T` is `H^s` near `x` exactly when every component of
its local representative in `(t, c)` is `H^s` near `c x`. -/
theorem isLocallySobolevAt_iff {s : ℝ} (T : BundleTest I F V →L_c[ℝ] ℝ)
    {t : Trivialization F (π F V)} [MemTrivializationAtlas t] {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hct : c.source ⊆ t.baseSet) {x : M} (hx : x ∈ c.source) :
    IsLocallySobolevAt s T x ↔
      ∀ v, (mapCLM (ofRealCLM ∘L ContinuousLinearMap.apply ℝ ℝ v)
        (t.chartDistributionCLM c hc hct T)).IsLocallySobolevAt s (c x) :=
  ⟨fun ⟨t₀, _, _, hc₀, hcs₀, hct₀, hx₀, h⟩ ↦
    (forall_isLocallySobolevAt_chartDistributionCLM_iff (t' := t₀) (hc' := hc₀) (hct' := hct₀)
      (hc := hc) (hct := hct) hcs hcs₀ T hx hx₀).1 h,
    fun h ↦ ⟨t, inferInstance, c, hc, hcs, hct, hx, h⟩⟩

/-- Being `H^s` near `x` gets weaker as `s` decreases. -/
theorem IsLocallySobolevAt.mono {s s' : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    (h : IsLocallySobolevAt s T x) (hs : s' ≤ s) : IsLocallySobolevAt s' T x :=
  let ⟨t, ht, c, hc, hcs, hct, hx, h⟩ := h
  ⟨t, ht, c, hc, hcs, hct, hx, fun v ↦ (h v).mono hs⟩

/-- The points near which `T` is `H^s` form an open set. -/
theorem isOpen_setOf_isLocallySobolevAt (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    IsOpen {x : M | IsLocallySobolevAt s T x} := by
  refine isOpen_iff_mem_nhds.2 fun x ⟨t, ht, c, hc, hcs, hct, hx, h⟩ ↦ ?_
  -- Finitely many components, along a basis of `F`, determine all of them.
  set b := Module.finBasis ℝ F
  have hopen : IsOpen (c.source ∩ c ⁻¹' ⋂ j, {y | (mapCLM (ofRealCLM ∘L
      ContinuousLinearMap.apply ℝ ℝ (b j)) (t.chartDistributionCLM c hc hct T)).IsLocallySobolevAt
        s y}) :=
    c.isOpen_inter_preimage (isOpen_iInter_of_finite fun j ↦
      Distribution.isOpen_setOf_isLocallySobolevAt _ _)
  exact Filter.mem_of_superset (hopen.mem_nhds ⟨hx, mem_iInter.2 fun j ↦ h (b j)⟩)
    fun y ⟨hy, hyj⟩ ↦ ⟨t, ht, c, hc, hcs, hct, hy,
      isLocallySobolevAt_mapCLM_apply_of_basis b (c.map_source hy) (mem_iInter.1 hyj)⟩

/-- A sum of functionals `H^s` near `x` is `H^s` near `x`. -/
theorem IsLocallySobolevAt.add {s : ℝ} {T T' : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    (h : IsLocallySobolevAt s T x) (h' : IsLocallySobolevAt s T' x) :
    IsLocallySobolevAt s (T + T') x := by
  obtain ⟨t, _, c, hc, hcs, hct, hx, hT⟩ := h
  refine ⟨t, inferInstance, c, hc, hcs, hct, hx, fun v ↦ ?_⟩
  rw [map_add, map_add]
  exact (hT v).add ((isLocallySobolevAt_iff T' hc hcs hct hx).1 h' v)

/-- A real multiple of a functional `H^s` near `x` is `H^s` near `x`. -/
theorem IsLocallySobolevAt.smul {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    (h : IsLocallySobolevAt s T x) (a : ℝ) : IsLocallySobolevAt s (a • T) x := by
  obtain ⟨t, _, c, hc, hcs, hct, hx, hT⟩ := h
  refine ⟨t, inferInstance, c, hc, hcs, hct, hx, fun v ↦ ?_⟩
  have hsmul : mapCLM (ofRealCLM ∘L ContinuousLinearMap.apply ℝ ℝ v)
      (t.chartDistributionCLM c hc hct (a • T)) = (a : ℂ) •
        mapCLM (ofRealCLM ∘L ContinuousLinearMap.apply ℝ ℝ v)
          (t.chartDistributionCLM c hc hct T) := by
    ext φ
    simp
  rw [hsmul]
  exact (hT v).smul _

/-- The negative of a functional `H^s` near `x` is `H^s` near `x`. -/
theorem IsLocallySobolevAt.neg {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    (h : IsLocallySobolevAt s T x) : IsLocallySobolevAt s (-T) x := by
  simpa using h.smul (-1)

/-- A difference of functionals `H^s` near `x` is `H^s` near `x`. -/
theorem IsLocallySobolevAt.sub {s : ℝ} {T T' : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    (h : IsLocallySobolevAt s T x) (h' : IsLocallySobolevAt s T' x) :
    IsLocallySobolevAt s (T - T') x := by
  simpa [sub_eq_add_neg] using h.add h'.neg

/-! ### The `H^s` singular support -/

variable (I) in
/-- The **`H^s` singular support** of a real functional `T` on bundle tests: the points of `M` near
which `T` is not `H^s`. -/
def sobolevSingularSupport (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) : Set M :=
  {x | ¬ IsLocallySobolevAt s T x}

@[simp]
theorem mem_sobolevSingularSupport_iff {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M} :
    x ∈ sobolevSingularSupport I s T ↔ ¬ IsLocallySobolevAt s T x :=
  Iff.rfl

/-- The `H^s` singular support is closed. -/
theorem isClosed_sobolevSingularSupport (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    IsClosed (sobolevSingularSupport I s T) :=
  (isOpen_setOf_isLocallySobolevAt s T).isClosed_compl

/-- The `H^s` singular support grows with `s`. -/
theorem sobolevSingularSupport_mono {s s' : ℝ} (hs : s' ≤ s) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevSingularSupport I s' T ⊆ sobolevSingularSupport I s T :=
  fun _ hx h ↦ hx (h.mono hs)

/-- The `H^s` singular support of a sum lies in the union of the `H^s` singular supports. -/
theorem sobolevSingularSupport_add_subset (s : ℝ) (T T' : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevSingularSupport I s (T + T') ⊆
      sobolevSingularSupport I s T ∪ sobolevSingularSupport I s T' := by
  intro x hx
  by_contra h
  simp only [mem_union, mem_sobolevSingularSupport_iff, not_or, not_not] at h
  exact hx (h.1.add h.2)

/-- The `H^s` singular support of a real multiple lies in the `H^s` singular support. -/
theorem sobolevSingularSupport_smul_subset (s : ℝ) (a : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevSingularSupport I s (a • T) ⊆ sobolevSingularSupport I s T :=
  fun _ hx h ↦ hx (h.smul a)

/-- The negative of `T` has the same `H^s` singular support as `T`. -/
@[simp]
theorem sobolevSingularSupport_neg (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevSingularSupport I s (-T) = sobolevSingularSupport I s T :=
  Subset.antisymm (by simpa using sobolevSingularSupport_smul_subset s (-1) T)
    (by simpa using sobolevSingularSupport_smul_subset s (-1) (-T))

/-- The `H^s` singular support of a difference lies in the union of the `H^s` singular
supports. -/
theorem sobolevSingularSupport_sub_subset (s : ℝ) (T T' : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevSingularSupport I s (T - T') ⊆
      sobolevSingularSupport I s T ∪ sobolevSingularSupport I s T' := by
  simpa [sub_eq_add_neg] using sobolevSingularSupport_add_subset s T (-T')

/-! ### Manifolds without boundary -/

section Boundaryless

variable [I.Boundaryless]

/-- On a manifold without boundary, the zero functional is `H^s` near every point. -/
theorem isLocallySobolevAt_zero (s : ℝ) (x : M) :
    IsLocallySobolevAt s (0 : BundleTest I F V →L_c[ℝ] ℝ) x := by
  obtain ⟨c, hc, hcs, hct, hx⟩ := exists_chart_source_subset_baseSet F I V (n := ∞) x
  refine ⟨trivializationAt F V x, inferInstance, c, hc, hcs, hct, hx, fun v ↦ ?_⟩
  rw [map_zero, map_zero]
  exact isLocallySobolevAt_zero_iff.2 (c.map_source hx)

/-- On a manifold without boundary, the zero functional has empty `H^s` singular support. -/
@[simp]
theorem sobolevSingularSupport_zero (s : ℝ) :
    sobolevSingularSupport I s (0 : BundleTest I F V →L_c[ℝ] ℝ) = ∅ :=
  eq_empty_iff_forall_notMem.2 fun x hx ↦ hx (isLocallySobolevAt_zero s x)

/-- **Functionals on bundle tests have finite Sobolev order locally.** On a manifold without
boundary, for every compact set `K ⊆ M` there is an order `s` such that `T` is `H^s` near every
point of `K`. -/
theorem exists_forall_isLocallySobolevAt (T : BundleTest I F V →L_c[ℝ] ℝ) {K : Set M}
    (hK : IsCompact K) : ∃ s : ℝ, ∀ x ∈ K, IsLocallySobolevAt s T x := by
  -- At each point, the finitely many basis components have a common finite order.
  have hpt (x : M) : ∃ s : ℝ, IsLocallySobolevAt s T x := by
    obtain ⟨c, hc, hcs, hct, hx⟩ := exists_chart_source_subset_baseSet F I V (n := ∞) x
    set b := Module.finBasis ℝ F
    choose s hs using fun j ↦ Distribution.exists_forall_isLocallySobolevAt
      (mapCLM (ofRealCLM ∘L ContinuousLinearMap.apply ℝ ℝ (b j))
        ((trivializationAt F V x).chartDistributionCLM c hc hct T))
      (isCompact_singleton (x := c x)) (singleton_subset_iff.2 (c.map_source hx))
    refine ⟨-∑ j, |s j|, trivializationAt F V x, inferInstance, c, hc, hcs, hct, hx,
      isLocallySobolevAt_mapCLM_apply_of_basis b (c.map_source hx) fun j ↦
        (hs j (c x) rfl).mono ?_⟩
    have := Finset.single_le_sum (f := fun j ↦ |s j|) (fun j _ ↦ abs_nonneg _)
      (Finset.mem_univ j)
    linarith [neg_abs_le (s j)]
  -- Patch the orders over a finite cover of `K`, using that each order holds on an open set.
  refine hK.induction_on (p := fun S ↦ ∃ s : ℝ, ∀ x ∈ S, IsLocallySobolevAt s T x)
    ⟨0, by simp⟩ (fun S S' hS ⟨s, hs⟩ ↦ ⟨s, fun x hx ↦ hs x (hS hx)⟩)
    (fun S S' ⟨s, hs⟩ ⟨s', hs'⟩ ↦ ⟨min s s', fun x hx ↦ hx.elim
      (fun hx ↦ (hs x hx).mono (min_le_left _ _)) fun hx ↦ (hs' x hx).mono (min_le_right _ _)⟩)
    fun x _ ↦ ?_
  obtain ⟨s, hs⟩ := hpt x
  exact ⟨_, mem_nhdsWithin_of_mem_nhds ((isOpen_setOf_isLocallySobolevAt s T).mem_nhds hs),
    s, fun _ hy ↦ hy⟩

/-! ### Point masses -/

omit [MeasurableSpace E] [BorelSpace E] [I.Boundaryless] in
/-- The component along `v` of the local representative of the point mass `δ_x ℓ`, in a chart
whose source contains `x`, is the Euclidean point mass at `c x` times `ℓ (t⁻¹ v)`. -/
private theorem mapCLM_chartDistributionCLM_delta_of_mem {t : Trivialization F (π F V)}
    [MemTrivializationAtlas t] {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hct : c.source ⊆ t.baseSet) {x : M}
    (hx : x ∈ c.source) (ℓ : V x →L[ℝ] ℝ) (v : F) :
    mapCLM (ofRealCLM ∘L ContinuousLinearMap.apply ℝ ℝ v)
        (t.chartDistributionCLM c hc hct (BundleTest.delta x ℓ)) =
      ((ℓ (t.symmL ℝ x v) : ℝ) : ℂ) •
        mapCLM ofRealCLM (Distribution.delta (c x) : 𝓓'(⟨c.target, c.open_target⟩, ℝ)) := by
  rw [chartDistributionCLM_delta_of_mem _ _ _ _ hx]
  ext φ
  simp [mul_comm]

/-- **Point masses are `H^s` below the critical order.** On a manifold without boundary of
dimension `d`, the point mass `δ_x ℓ` has empty `H^s` singular support for `s < -d / 2`. -/
theorem sobolevSingularSupport_delta_eq_empty {s : ℝ}
    (hs : (Module.finrank ℝ E : ℝ) < -2 * s) (x : M) (ℓ : V x →L[ℝ] ℝ) :
    sobolevSingularSupport I s (BundleTest.delta x ℓ : BundleTest I F V →L_c[ℝ] ℝ) = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun p hp ↦ hp ?_
  obtain ⟨c, hc, hcs, hct, hp⟩ := exists_chart_source_subset_baseSet F I V (n := ∞) p
  refine ⟨trivializationAt F V p, inferInstance, c, hc, hcs, hct, hp, fun v ↦ ?_⟩
  by_cases hx : x ∈ c.source
  · rw [mapCLM_chartDistributionCLM_delta_of_mem hc hct hx]
    exact ((notMem_sobolevSingularSupport_iff (c.map_source hp)).1
      (by simp [Distribution.sobolevSingularSupport_delta_eq_empty hs])).smul _
  · rw [chartDistributionCLM_delta_of_notMem _ _ _ _ hx, map_zero]
    exact isLocallySobolevAt_zero_iff.2 (c.map_source hp)

/-- **The `H^s` singular support of a point mass.** On a manifold without boundary of positive
dimension `d`, the point mass `δ_x ℓ` with `ℓ ≠ 0` has `H^s` singular support `{x}` for
`s ≥ -d / 2`. -/
theorem sobolevSingularSupport_delta [Nontrivial E] {s : ℝ}
    (hs : -2 * s ≤ Module.finrank ℝ E) {x : M} {ℓ : V x →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    sobolevSingularSupport I s (BundleTest.delta x ℓ : BundleTest I F V →L_c[ℝ] ℝ) = {x} := by
  ext p
  obtain ⟨c, hc, hcs, hct, hp⟩ := exists_chart_source_subset_baseSet F I V (n := ∞) p
  rw [mem_sobolevSingularSupport_iff, isLocallySobolevAt_iff _ hc hcs hct hp, mem_singleton_iff]
  have hdelta (y : E) (hy : y ∈ c.target) := Distribution.sobolevSingularSupport_delta
    (Ω := ⟨c.target, c.open_target⟩) (x₀ := y) hs hy
  constructor
  · -- Away from `x`, the local representative is a multiple of a point mass elsewhere, or zero.
    intro h
    by_contra hpx
    refine h fun v ↦ ?_
    by_cases hx : x ∈ c.source
    · rw [mapCLM_chartDistributionCLM_delta_of_mem hc hct hx]
      refine ((notMem_sobolevSingularSupport_iff (c.map_source hp)).1 ?_).smul _
      rw [hdelta _ (c.map_source hx), mem_singleton_iff]
      exact fun h' ↦ hpx (c.injOn hp hx h')
    · rw [chartDistributionCLM_delta_of_notMem _ _ _ _ hx, map_zero]
      exact isLocallySobolevAt_zero_iff.2 (c.map_source hp)
  · -- At `x`, some component is a nonzero multiple of the point mass at `c x`.
    rintro rfl h
    obtain ⟨u, hu⟩ : ∃ u, ℓ u ≠ 0 := by
      by_contra! h0
      exact hℓ (ContinuousLinearMap.ext h0)
    have hv := h ((trivializationAt F V p).continuousLinearMapAt ℝ p u)
    rw [mapCLM_chartDistributionCLM_delta_of_mem hc hct hp,
      (trivializationAt F V p).symmL_continuousLinearMapAt (hct hp),
      isLocallySobolevAt_smul_iff (Complex.ofReal_ne_zero.2 hu)] at hv
    exact (notMem_sobolevSingularSupport_iff (c.map_source hp)).2 hv
      (by simp [hdelta _ (c.map_source hp)])

end Boundaryless

end TauCeti.BundleTest

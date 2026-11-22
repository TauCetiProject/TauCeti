/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.ChangeOfVariables
public import TauCeti.Analysis.Distribution.SmulLeft
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Components of a functional on bundle tests in a chart and a frame

Let `V → M` be a smooth real vector bundle over a smooth manifold modelled on a
finite-dimensional real inner product space `E`, and let `T` be a real continuous linear functional
on the bundle tests `TauCeti.BundleTest I F V`. In a smooth chart `c` and a bundle frame `t` over
its source, `T` has a local representative on the chart target
(`Bundle.Trivialization.chartDistributionCLM`). Its **component along** `v : F`
(`Bundle.Trivialization.chartComponent`) is the complex distribution `φ ↦ T (φ • v)` on the chart
target, the test function `φ • v` being extended to a bundle test through the chart and the frame.

This file computes how the components change with the chart and the frame. For two charts `c`,
`c'` with smooth inverses and frames `t`, `t'`, near a point of the source of the chart transition
`κ = c ∘ c'⁻¹`, the component along `v` in `(t', c')` is

`S'_v = ∑ⱼ gⱼ κ^* S_{bⱼ}`, with `gⱼ = |det Dκ| · bⱼ*(G(c'⁻¹ ·) v)`,

where `S_{bⱼ}` are the components in `(t, c)` along the standard basis `(bⱼ)` of `F`,
`G = t ∘ t'⁻¹` is the change of frame and `κ^*` is the pullback of distributions
(`Distribution.compCLMOfOpenPartialHomeomorph`)
(`Bundle.Trivialization.restrictCLM_chartComponent_eq_sum`). The coefficients `gⱼ` are smooth on
the source of `κ` (`Bundle.Trivialization.contDiffOn_transitionCoeff`). Any local regularity
property of distributions preserved by pullback, smooth multiples and finite sums, such as local
Sobolev regularity or microlocal smoothness, is therefore independent of the chart and the frame.

## The argument

Near `y`, a test function `φ • v` read in the chart `c'` and the frame `t'` is the bundle test
`x ↦ φ(c' x) t'⁻¹(v)`. Over the overlap of the two charts this is `t⁻¹(φ(c' x) G(x) v)`, that is,
the test function `z ↦ φ(κ⁻¹ z) G(c⁻¹ z) v` read in the chart `c` and the frame `t`. Writing `G v`
in the basis `(bⱼ)` and the composition with `κ⁻¹` as the pushforward of test densities along `κ`,
which carries the Jacobian `|det Dκ⁻¹|` (`TestFunction.pushforwardCLM`), gives the formula above.

## Main declarations

* `Bundle.Trivialization.chartComponent`: the component along `v` of the local representative of
  `T` in a chart and a frame, as a complex distribution on the chart target.
* `Bundle.Trivialization.restrictCLM_chartComponent_eq_sum`: the change of chart and frame for the
  components.
* `Bundle.Trivialization.contDiffOn_transitionCoeff`: the smoothness of its coefficients.
-/

public section

noncomputable section

open Set Filter Function TopologicalSpace Complex Distribution ContinuousLinearMap
open scoped Manifold ContDiff Distributions Topology CompactConvergenceCLM

namespace Bundle.Trivialization

open TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]
  (t : Trivialization F (π F V)) [MemTrivializationAtlas t]
  (c : OpenPartialHomeomorph M E)
  (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hct : c.source ⊆ t.baseSet)

/-- The **component along `v`** of the local representative of a real functional `T` on bundle
tests in the chart `c` and the frame `t`: the complex distribution `φ ↦ T (φ • v)` on the chart
target, the test function `φ • v` being extended to a bundle test through the chart and the
frame. -/
def chartComponent (T : BundleTest I F V →L_c[ℝ] ℝ) (v : F) :
    𝓓'(⟨c.target, c.open_target⟩, ℂ) :=
  mapCLM (ofRealCLM ∘L ContinuousLinearMap.apply ℝ ℝ v) (t.chartDistributionCLM c hc hct T)

theorem chartComponent_def (T : BundleTest I F V →L_c[ℝ] ℝ) (v : F) :
    t.chartComponent c hc hct T v =
      mapCLM (ofRealCLM ∘L ContinuousLinearMap.apply ℝ ℝ v)
        (t.chartDistributionCLM c hc hct T) := by
  rfl

@[simp]
theorem chartComponent_apply (T : BundleTest I F V →L_c[ℝ] ℝ) (v : F)
    (φ : 𝓓(⟨c.target, c.open_target⟩, ℝ)) :
    t.chartComponent c hc hct T v φ =
      (T (t.chartTestCLM c hc hct (TestFunction.postcompCLM (toSpanSingleton ℝ v) φ)) : ℂ) := by
  simp [chartComponent]

@[simp]
theorem chartComponent_zero (v : F) :
    t.chartComponent c hc hct (0 : BundleTest I F V →L_c[ℝ] ℝ) v = 0 := by
  ext φ
  simp

/-! ### Changes of chart and frame -/

section Transition

variable {t c hc hct}
variable {t' : Trivialization F (π F V)} [MemTrivializationAtlas t']
  {c' : OpenPartialHomeomorph M E}
  {hc' : ContMDiffOn I 𝓘(ℝ, E) ∞ c' c'.source} {hct' : c'.source ⊆ t'.baseSet}

/-- **Change of chart and frame for test functions.** Let `φ` be a test function supported in an
open set `B` of the source of the chart transition `κ = c ∘ c'⁻¹`, and `gⱼ` smooth functions equal
on `B` to `|det Dκ| bⱼ*(G(c'⁻¹ ·) v)`, where `G = t ∘ t'⁻¹` is the change of frame and `(bⱼ)` the
standard basis of `F`. Then the bundle test `φ • v` read in `(t', c')` is the sum of the bundle
tests `(κ_* (gⱼ φ)) • bⱼ` read in `(t, c)`. -/
private theorem chartTestCLM_eq_sum_chartTestCLM (v : F)
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

/-- **Change of chart and frame for the components.** Near a point of the source of the chart
transition `κ = c ∘ c'⁻¹`, the component along `v` in `(t', c')` is `∑ⱼ gⱼ κ^* S_{bⱼ}`, where
`S_{bⱼ}` are the components in `(t, c)` along the standard basis of `F` and `gⱼ` are the smooth
coefficients of `chartTestCLM_eq_sum_chartTestCLM`. -/
theorem restrictCLM_chartComponent_eq_sum (T : BundleTest I F V →L_c[ℝ] ℝ) (v : F)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) (c'.symm.trans c) (c'.symm.trans c).source)
    (he' : ContDiffOn ℝ (⊤ : ℕ∞) (c'.symm.trans c).symm (c'.symm.trans c).target)
    {B : Opens E} (hB : (B : Set E) ⊆ (c'.symm.trans c).source)
    (hBc : MapsTo (c'.symm.trans c) B (⟨c.target, c.open_target⟩ : Opens E))
    {g : Fin (Module.finrank ℝ F) → E → ℝ} (hg : ∀ j, ContDiff ℝ ∞ (g j))
    (hgB : ∀ j, ∀ y ∈ B, g j y = |(fderiv ℝ (c'.symm.trans c) y).det| *
      (Module.finBasis ℝ F).coord j (t'.coordChangeL ℝ t (c'.symm y) v)) :
    (restrictCLM (t'.chartComponent c' hc' hct' T v) : 𝓓'(B, ℂ)) =
      ∑ j, smulLeftCLM (hg j) (compCLMOfOpenPartialHomeomorph (c'.symm.trans c) he he' hB hBc
        (t.chartComponent c hc hct T (Module.finBasis ℝ F j))) := by
  ext φ
  simp only [restrictCLM_apply, chartComponent_apply, _root_.sum_apply, smulLeftCLM_apply,
    compCLMOfOpenPartialHomeomorph_apply]
  rw [← Complex.ofReal_sum, ← map_sum,
    chartTestCLM_eq_sum_chartTestCLM (hc := hc) (hct := hct) v he he' hB hBc hg hgB φ]

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] in
include hct hct' in
/-- The coefficient `z ↦ |det Dκ(z)| bⱼ*(G(c'⁻¹ z) v)` of the change of chart and frame is smooth
on the source of the transition `κ = c ∘ c'⁻¹`, where `G = t ∘ t'⁻¹` is the change of frame. -/
theorem contDiffOn_transitionCoeff
    (he : ContDiffOn ℝ (⊤ : ℕ∞) (c'.symm.trans c) (c'.symm.trans c).source)
    (he' : ContDiffOn ℝ (⊤ : ℕ∞) (c'.symm.trans c).symm (c'.symm.trans c).target)
    (hcs' : ContMDiffOn 𝓘(ℝ, E) I ∞ c'.symm c'.target) (v : F) (j : Fin (Module.finrank ℝ F)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z ↦ |(fderiv ℝ (c'.symm.trans c) z).det| *
      (Module.finBasis ℝ F).coord j (t'.coordChangeL ℝ t (c'.symm z) v))
      (c'.symm.trans c).source := by
  set κ := c'.symm.trans c
  have hdet := κ.contDiffOn_abs_det_fderiv_of_contDiffOn (m := ⊤) (by simp) he he'
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) (fun z ↦ (t'.coordChangeL ℝ t (c'.symm z) : F →L[ℝ] F))
      κ.source :=
    contMDiffOn_iff_contDiffOn.1 ((contMDiffOn_coordChangeL (IB := I) t' t).comp
      (hcs'.mono fun z hz ↦ hz.1) fun z hz ↦
        ⟨hct' (c'.map_target hz.1), hct hz.2⟩)
  have hcoord := (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ F).coord j)).contDiff
    (n := (⊤ : ℕ∞))
  exact hdet.mul (hcoord.comp_contDiffOn (hG.clm_apply contDiffOn_const))

end Transition

end Bundle.Trivialization

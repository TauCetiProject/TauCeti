/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.ChangeOfVariables
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution
import Mathlib.Analysis.Calculus.Deriv.Abs
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.FDeriv.Det.Basic
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# The wave front set of a functional on bundle tests

Let `V → M` be a smooth real vector bundle over a smooth manifold modelled on a
finite-dimensional real inner product space `E`, and let `T` be a real continuous linear functional
on the bundle tests `TauCeti.BundleTest I F V`, for instance a distributional section of a bundle
(`TauCeti.BundleDistribution`). In a smooth chart `c` with smooth inverse and a bundle frame `t`
over its source, `T` has a local representative on the chart target
(`Bundle.Trivialization.chartDistributionCLM`). Its **component along** `v : F`
(`Bundle.Trivialization.chartComponent`) is the complex distribution `φ ↦ T (φ • v)` on the chart
target, the test function `φ • v` being extended to a bundle test through the chart and the frame.
As for vector-valued distributions (`Distribution.vectorWaveFrontSet`), `T` is microlocally smooth
in the chart at `(y, η)` when all these components are.

This file proves that this notion does not depend on the chart or the frame: for two charts
`c`, `c'` with frames `t`, `t'`, and a point `y = c' x` with `x` in both chart sources,

`S'_v` is microlocally smooth at `(y, Dκ(y)ᵀ η)` for all `v` if and only if
`S_v` is microlocally smooth at `(κ y, η)` for all `v`,

where `S_v` and `S'_v` are the components in `(t, c)` and in `(t', c')`, and `κ = c ∘ c'⁻¹` is the
chart transition (`Bundle.Trivialization.forall_isMicrolocallySmoothAt_chartComponent_iff`). For
one chart and two frames the transition is the identity
(`Bundle.Trivialization.forall_isMicrolocallySmoothAt_chartComponent_iff_of_chart`).

So covectors transform by the transpose of the derivative of the transition, and microlocal
smoothness of `T` at a covector `ξ ∈ T*ₓM` is well defined: it is microlocal smoothness of the
components in any chart `c` at `x`, at `c x` in the direction of the covector `ξ ∘ D(c⁻¹)(c x)`
read in the chart (`TauCeti.BundleTest.IsMicrolocallySmoothAt`,
`TauCeti.BundleTest.isMicrolocallySmoothAt_iff`). The **wave front set** of `T`
(`TauCeti.BundleTest.waveFrontSet`) is the set of nonzero covectors of the cotangent bundle
`TauCeti.CotangentBundle I M` at which `T` is not microlocally smooth.

## The argument

Near `y`, a test function `φ • v` read in the chart `c'` and the frame `t'` is the bundle test
`x ↦ φ(c' x) t'⁻¹(v)`. Over the overlap of the two charts this is
`t⁻¹(φ(c' x) G(x) v)` for the change of frame `G = t ∘ t'⁻¹`, that is, the test function
`z ↦ φ(κ⁻¹ z) G(c⁻¹ z) v` read in the chart `c` and the frame `t`. Writing `G v` in a basis `(bⱼ)`
of `F` and the composition with `κ⁻¹` as the pushforward of test densities along `κ`, which carries
the Jacobian `|det Dκ⁻¹|` (`TestFunction.pushforwardCLM`), gives near `y`

`S'_v = ∑ⱼ gⱼ κ^* S_{bⱼ}`, with `gⱼ = |det Dκ| · bⱼ*(G(c'⁻¹ ·) v)`,

where `κ^*` is the pullback of distributions (`Distribution.compCLMOfOpenPartialHomeomorph`). The
pullback transforms microlocal smoothness by the transpose of `Dκ`
(`Distribution.isMicrolocallySmoothAt_compCLMOfOpenPartialHomeomorph_iff`), and smooth multiples
and finite sums preserve it. Exchanging the roles of the two charts gives the converse. On the
manifold, the chain rule `D(c⁻¹)(c x) = D(c₀⁻¹)(c₀ x) ∘ Dκ(c x)` for `κ = c₀ ∘ c⁻¹`
(`OpenPartialHomeomorph.mfderiv_symm_eq_mfderiv_symm_comp_fderiv_symm_trans`) identifies the
covectors read in two charts.

## Main declarations

* `Bundle.Trivialization.chartComponent`: the component along `v` of the local representative of
  `T` in a chart and a frame, as a complex distribution on the chart target.
* `Bundle.Trivialization.forall_isMicrolocallySmoothAt_chartComponent_iff`: microlocal smoothness
  of all components does not depend on the chart and the frame, covectors transforming by the
  transpose of the derivative of the chart transition.
* `Bundle.Trivialization.forall_isMicrolocallySmoothAt_chartComponent_iff_of_chart`: in one chart,
  it does not depend on the frame.
* `TauCeti.BundleTest.IsMicrolocallySmoothAt`: microlocal smoothness of `T` at a covector of `M`,
  and `TauCeti.BundleTest.isMicrolocallySmoothAt_iff`, its characterization in every chart and
  frame.
* `TauCeti.BundleTest.waveFrontSet`: the wave front set of `T`, a subset of the cotangent bundle.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.2 (the wave front set on a manifold, after Theorem 8.2.4) and §8.1 (the
  wave front set of a vector-valued distribution).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, Lecture I, §7.
-/

public section

noncomputable section

open Set Filter Function TopologicalSpace Complex Distribution ContinuousLinearMap
open scoped Manifold ContDiff Distributions Topology InnerProduct CompactConvergenceCLM

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

@[simp]
theorem chartComponent_apply (T : BundleTest I F V →L_c[ℝ] ℝ) (v : F)
    (φ : 𝓓(⟨c.target, c.open_target⟩, ℝ)) :
    t.chartComponent c hc hct T v φ =
      (T (t.chartTestCLM c hc hct (TestFunction.postcompCLM (toSpanSingleton ℝ v) φ)) : ℂ) := by
  simp [chartComponent]

/-! ### Changes of chart and frame -/

section Transition

variable {t c hc hct}
variable {t' : Trivialization F (π F V)} [MemTrivializationAtlas t']
  {c' : OpenPartialHomeomorph M E}
  {hc' : ContMDiffOn I 𝓘(ℝ, E) ∞ c' c'.source} {hct' : c'.source ⊆ t'.baseSet}

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] in
/-- The transition `c ∘ c'⁻¹` between two smooth charts with smooth inverses is smooth on its
source. -/
private theorem contDiffOn_trans (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source)
    (hcs' : ContMDiffOn 𝓘(ℝ, E) I ∞ c'.symm c'.target) :
    ContDiffOn ℝ (⊤ : ℕ∞) (c'.symm.trans c) (c'.symm.trans c).source := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.coe_trans]
  exact contMDiffOn_iff_contDiffOn.1 (hc.comp (hcs'.mono inter_subset_left) fun y hy ↦ hy.2)

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
private theorem restrictCLM_chartComponent_eq_sum (T : BundleTest I F V →L_c[ℝ] ℝ) (v : F)
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

/-- A finite sum of distributions microlocally smooth at `(x, ξ)`, for `x ∈ Ω`, is microlocally
smooth there. -/
private theorem isMicrolocallySmoothAt_sum {Ω : Opens E} {ι : Type*} (s : Finset ι)
    {S : ι → 𝓓'(Ω, ℂ)} {x ξ : E} (hx : x ∈ Ω) (h : ∀ i ∈ s, (S i).IsMicrolocallySmoothAt x ξ) :
    (∑ i ∈ s, S i).IsMicrolocallySmoothAt x ξ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨φ, -, hφx⟩ := TestFunction.exists_tsupport_subset_apply_eq (n := ⊤) (Ω := Ω)
      (Ω.isOpen.mem_nhds hx) subset_rfl (1 : ℂ)
    exact isMicrolocallySmoothAt_iff.2 ⟨φ, by simp [hφx], univ, isOpen_univ, mem_univ _,
      fun _ _ _ _ ↦ mem_univ _, fun _ ↦ ⟨0, fun η _ ↦ by simp⟩⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] in
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
      (hcs'.mono fun z hz ↦ hz.1) fun z hz ↦
        ⟨hct' (c'.map_target hz.1), hct hz.2⟩)
  have hcoord := (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ F).coord j)).contDiff
    (n := (⊤ : ℕ∞))
  exact hdet.mul (hcoord.comp_contDiffOn (hG.clm_apply contDiffOn_const))

/-- If every component in `(t, c)` is microlocally smooth at `(κ y, (Dκ⁻¹(κ y))ᵀ ξ)`, for the
transition `κ = c ∘ c'⁻¹`, then every component in `(t', c')` is microlocally smooth at
`(y, ξ)`. -/
private theorem isMicrolocallySmoothAt_chartComponent_of_forall
    (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hcs' : ContMDiffOn 𝓘(ℝ, E) I ∞ c'.symm c'.target) (T : BundleTest I F V →L_c[ℝ] ℝ)
    {y : E} (hy : y ∈ (c'.symm.trans c).source) {ξ : E}
    (h : ∀ w, (t.chartComponent c hc hct T w).IsMicrolocallySmoothAt (c'.symm.trans c y)
      (((fderiv ℝ (c'.symm.trans c).symm (c'.symm.trans c y))†) ξ)) (v : F) :
    (t'.chartComponent c' hc' hct' T v).IsMicrolocallySmoothAt y ξ := by
  have he := contDiffOn_trans hc hcs'
  have he' : ContDiffOn ℝ (⊤ : ℕ∞) (c'.symm.trans c).symm (c'.symm.trans c).target := by
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm]
    exact contDiffOn_trans hc' hcs
  -- A neighbourhood `B` of `y` with compact closure in the source of the transition.
  obtain ⟨W, hWo, hyW, hWs, hWc⟩ := exists_open_between_and_isCompact_closure isCompact_singleton
    (c'.symm.trans c).open_source (singleton_subset_iff.2 hy)
  let B : Opens E := ⟨W, hWo⟩
  have hB : (B : Set E) ⊆ (c'.symm.trans c).source := subset_closure.trans hWs
  have hBc : MapsTo (c'.symm.trans c) B (⟨c.target, c.open_target⟩ : Opens E) :=
    fun z hz ↦ ((c'.symm.trans c).map_source (hB hz)).1
  have hBt : B ≤ ⟨c'.target, c'.open_target⟩ := fun z hz ↦ (hB hz).1
  -- Globally smooth coefficients agreeing with those of the change of chart and frame on `B`.
  choose g hg _ _ _ hgf using fun j ↦
    (contDiffOn_transitionCoeff (hct := hct) (hct' := hct') he he' hcs' v
      j).exists_contDiff_eventuallyEq_on_isCompact hWc (c'.symm.trans c).open_source hWs
  have hgB (j) (z) (hz : z ∈ B) := (hgf j z (subset_closure hz)).eq_of_nhds
  rw [← isMicrolocallySmoothAt_restrictCLM_iff hBt (singleton_subset_iff.1 hyW),
    restrictCLM_chartComponent_eq_sum (hc := hc) (hct := hct) T v he he' hB hBc hg hgB]
  exact isMicrolocallySmoothAt_sum _ (singleton_subset_iff.1 hyW) fun j _ ↦
    ((h _).compCLMOfOpenPartialHomeomorph (c'.symm.trans c) he he' hB hBc
      (singleton_subset_iff.1 hyW)).smulLeftCLM (hg j)

/-- **Independence of the chart and the frame.** Let `c` and `c'` be smooth charts with smooth
inverses, with frames `t` and `t'` over their sources, and let `y = c' x` for a point `x` of both
chart sources. All components of the local representative of `T` in `(t', c')` are microlocally
smooth at `(y, Dκ(y)ᵀ η)`, for the chart transition `κ = c ∘ c'⁻¹`, exactly when all components
in `(t, c)` are microlocally smooth at `(κ y, η)`. -/
theorem forall_isMicrolocallySmoothAt_chartComponent_iff
    (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hcs' : ContMDiffOn 𝓘(ℝ, E) I ∞ c'.symm c'.target) (T : BundleTest I F V →L_c[ℝ] ℝ)
    {y : E} (hy : y ∈ c'.target) (hyc : c'.symm y ∈ c.source) (η : E) :
    (∀ v, (t'.chartComponent c' hc' hct' T v).IsMicrolocallySmoothAt y
      (((fderiv ℝ (c ∘ c'.symm) y)†) η)) ↔
      ∀ v, (t.chartComponent c hc hct T v).IsMicrolocallySmoothAt (c (c'.symm y)) η := by
  have hys : y ∈ (c'.symm.trans c).source := ⟨hy, hyc⟩
  constructor
  · -- Exchange the roles of the two charts: the transition from `c` to `c'` is `κ⁻¹`.
    intro h v
    have hz : c (c'.symm y) ∈ (c.symm.trans c').source :=
      ⟨c.map_source hyc, by simpa [c.left_inv hyc] using c'.map_target hy⟩
    refine isMicrolocallySmoothAt_chartComponent_of_forall (t := t') (hc := hc') (hct := hct')
      (t' := t) (hc' := hc) (hct' := hct) hcs' hcs T hz (fun w ↦ ?_) v
    have hzy : c.symm.trans c' (c (c'.symm y)) = y := by simp [c.left_inv hyc, c'.right_inv hy]
    rw [hzy]
    exact h w
  · intro h v
    have he := contDiffOn_trans hc hcs'
    have he' : ContDiffOn ℝ (⊤ : ℕ∞) (c'.symm.trans c).symm (c'.symm.trans c).target := by
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm]
      exact contDiffOn_trans hc' hcs
    refine isMicrolocallySmoothAt_chartComponent_of_forall (t := t) (hc := hc) (hct := hct)
      (t' := t') (hc' := hc') (hct' := hct') hcs hcs' T hys (fun w ↦ ?_) v
    have hη := (c'.symm.trans c).adjoint_fderiv_symm_apply_adjoint_fderiv_apply_of_contDiffOn he
      he' (by simp) hys η
    rw [OpenPartialHomeomorph.coe_trans] at hη ⊢
    rw [hη]
    exact h w

/-- **Independence of the frame.** In a smooth chart `c` with smooth inverse, all components of
the local representative of `T` in the frame `t'` are microlocally smooth at `(y, η)` exactly when
all components in the frame `t` are. -/
theorem forall_isMicrolocallySmoothAt_chartComponent_iff_of_chart
    (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target) (hct' : c.source ⊆ t'.baseSet)
    (T : BundleTest I F V →L_c[ℝ] ℝ) {y : E} (hy : y ∈ c.target) (η : E) :
    (∀ v, (t'.chartComponent c hc hct' T v).IsMicrolocallySmoothAt y η) ↔
      ∀ v, (t.chartComponent c hc hct T v).IsMicrolocallySmoothAt y η := by
  have hid : fderiv ℝ (c ∘ c.symm) y = ContinuousLinearMap.id ℝ E := by
    have hc_id : c ∘ c.symm =ᶠ[𝓝 y] id := c.eventually_right_inverse hy
    rw [hc_id.fderiv_eq, fderiv_id]
  have h := forall_isMicrolocallySmoothAt_chartComponent_iff (t := t) (t' := t') (hc := hc)
    (hct := hct) (hc' := hc) (hct' := hct') hcs hcs T hy (c.map_target hy) η
  rwa [hid, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply, c.right_inv hy] at h

end Transition

end Bundle.Trivialization

/-! ### Microlocal smoothness on the manifold -/

namespace TauCeti.BundleTest

open Bundle Bundle.Trivialization InnerProductSpace

variable {E H M F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]

/-- A real functional `T` on bundle tests is **microlocally smooth** at a covector `ξ` at `x` if,
in some smooth chart `c` at `x` with smooth inverse and some frame `t` over its source, every
component of the local representative of `T` is microlocally smooth at `c x` in the direction of
the covector `ξ ∘ D(c⁻¹)(c x)` read in the chart, identified with a vector of `E` through the inner
product. The chart and the frame do not matter (`TauCeti.BundleTest.isMicrolocallySmoothAt_iff`). -/
def IsMicrolocallySmoothAt (T : BundleTest I F V →L_c[ℝ] ℝ) (x : M)
    (ξ : TangentSpace I x →L[ℝ] ℝ) : Prop :=
  ∃ (t : Trivialization F (π F V)) (_ : MemTrivializationAtlas t) (c : OpenPartialHomeomorph M E)
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (_ : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hct : c.source ⊆ t.baseSet), x ∈ c.source ∧
    ∀ v, (t.chartComponent c hc hct T v).IsMicrolocallySmoothAt (c x)
      ((toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) I c.symm (c x)))

/-- The dual vector of a covector precomposed with `B` is the adjoint of `B` applied to the dual
vector of the covector. -/
private theorem toDual_symm_comp (ℓ : E →L[ℝ] ℝ) (B : E →L[ℝ] E) :
    (toDual ℝ E).symm (ℓ ∘L B) = (B†) ((toDual ℝ E).symm ℓ) := by
  apply (toDual ℝ E).injective
  ext u
  simp [toDual_apply_apply, adjoint_inner_left]

/-- **Microlocal smoothness in any chart and frame.** For a smooth chart `c` at `x` with smooth
inverse and a frame `t` over its source, `T` is microlocally smooth at the covector `ξ` at `x`
exactly when every component of its local representative in `(t, c)` is microlocally smooth at
`c x` in the direction of `ξ` read in the chart. -/
theorem isMicrolocallySmoothAt_iff (T : BundleTest I F V →L_c[ℝ] ℝ)
    {t : Trivialization F (π F V)} [MemTrivializationAtlas t] {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hct : c.source ⊆ t.baseSet) {x : M} (hx : x ∈ c.source) (ξ : TangentSpace I x →L[ℝ] ℝ) :
    IsMicrolocallySmoothAt T x ξ ↔
      ∀ v, (t.chartComponent c hc hct T v).IsMicrolocallySmoothAt (c x)
        ((toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) I c.symm (c x))) := by
  refine ⟨fun ⟨t₀, _, c₀, hc₀, hcs₀, hct₀, hx₀, h⟩ ↦ ?_, fun h ↦ ⟨t, inferInstance, c, hc, hcs,
    hct, hx, h⟩⟩
  -- Transfer from the chart `c₀` of the definition to `c`, through the transition `c₀ ∘ c⁻¹`.
  have hiff := forall_isMicrolocallySmoothAt_chartComponent_iff (t := t₀) (hc := hc₀)
    (hct := hct₀) (t' := t) (hc' := hc) (hct' := hct) hcs₀ hcs T (c.map_source hx)
    (by simpa [c.left_inv hx] using hx₀) ((toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) I c₀.symm (c₀ x)))
  -- The chain rule `D(c⁻¹)(c x) = D(c₀⁻¹)(c₀ x) ∘ D(c₀ ∘ c⁻¹)(c x)` identifies the covectors.
  have hw : c x ∈ (c.symm.trans c₀).source :=
    ⟨c.map_source hx, by simpa [c.left_inv hx] using hx₀⟩
  have hwx : c.symm.trans c₀ (c x) = c₀ x := by simp [c.left_inv hx]
  have hΘ : DifferentiableAt ℝ (c.symm.trans c₀) (c x) :=
    ((contDiffOn_trans hc₀ hcs).differentiableOn (by simp)).differentiableAt
      ((c.symm.trans c₀).open_source.mem_nhds hw)
  have hψ : MDifferentiableAt 𝓘(ℝ, E) I c₀.symm (c.symm.trans c₀ (c x)) := by
    rw [hwx]
    exact (hcs₀.contMDiffAt (c₀.open_target.mem_nhds (c₀.map_source hx₀))).mdifferentiableAt
      (by simp)
  have hD := c.mfderiv_symm_eq_mfderiv_symm_comp_fderiv_symm_trans hw hψ hΘ
  rw [c.left_inv hx] at hiff
  intro v
  convert hiff.2 h v using 2
  rw [← toDual_symm_comp]
  congr 1
  ext u
  simp only [ContinuousLinearMap.comp_apply]
  rw [hD, hwx]
  -- The transition `c.symm.trans c₀` is `c₀ ∘ c.symm` by definition.
  rfl

variable (I) in
/-- The **wave front set** of a real functional `T` on bundle tests, for instance a distributional
section of a bundle: the nonzero covectors of `M` at which `T` is not microlocally smooth. -/
def waveFrontSet (T : BundleTest I F V →L_c[ℝ] ℝ) : Set (CotangentBundle I M) :=
  {p | p.snd ≠ 0 ∧ ¬ IsMicrolocallySmoothAt T p.proj p.snd}

@[simp]
theorem mem_waveFrontSet_iff {T : BundleTest I F V →L_c[ℝ] ℝ} {p : CotangentBundle I M} :
    p ∈ waveFrontSet I T ↔ p.snd ≠ 0 ∧ ¬ IsMicrolocallySmoothAt T p.proj p.snd :=
  Iff.rfl

end TauCeti.BundleTest

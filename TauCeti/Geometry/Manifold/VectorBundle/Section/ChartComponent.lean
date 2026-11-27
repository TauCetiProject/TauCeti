/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.ChangeOfVariables
public import TauCeti.Analysis.Distribution.SmulLeft
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution.Support
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
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

where `S_{bⱼ}` are the components in `(t, c)` along the basis `(bⱼ) = Module.finBasis ℝ F`,
`G = t ∘ t'⁻¹` is the change of frame and `κ^*` is the pullback of distributions
(`Distribution.compCLMOfOpenPartialHomeomorph`)
(`Bundle.Trivialization.restrictCLM_chartComponent_eq_sum`). The transition `κ` is smooth with
smooth inverse (`OpenPartialHomeomorph.contDiffOn_symm_trans_and_symm_of_contMDiffOn`), and the
coefficients `gⱼ` are smooth on the source of `κ`
(`Bundle.Trivialization.contDiffOn_abs_det_fderiv_mul_coord_coordChangeL`), so near every point
of the source of `κ` the formula holds with globally smooth coefficients
(`Bundle.Trivialization.exists_restrictCLM_chartComponent_eq_sum`). Any property of distributions
at a point that is preserved by pullback, smooth multiples and finite sums, such as local Sobolev
regularity, is therefore independent of the chart and the frame. Microlocal smoothness transfers
in the same way once covectors are transformed by the transpose of `Dκ`.

## The argument

Near `y`, a test function `φ • v` read in the chart `c'` and the frame `t'` is the bundle test
`x ↦ φ(c' x) t'⁻¹(v)`. Over the overlap of the two charts this is `t⁻¹(φ(c' x) G(x) v)`, that is,
the test function `z ↦ φ(κ⁻¹ z) G(c⁻¹ z) v` read in the chart `c` and the frame `t`. Writing `G v`
in the basis `(bⱼ)` and the composition with `κ⁻¹` as the pushforward of test densities along `κ`,
which carries the Jacobian `|det Dκ⁻¹|` (`TestFunction.pushforwardCLM`), gives the formula above.

## Main declarations

* `Bundle.Trivialization.chartComponent`: the component along `v` of the local representative of
  `T` in a chart and a frame, as a complex distribution on the chart target. It is a real
  distribution, fixed by complex conjugation (`Bundle.Trivialization.mapCLM_conj_chartComponent`).
* `Bundle.Trivialization.isVanishingOn_chartComponent`,
  `Bundle.Trivialization.dsupport_chartComponent_inter_target_subset`: the components of `T`
  vanish where `T` does, so over the chart target they are supported in the chart image of the
  support of the functional.
* `Bundle.Trivialization.restrictCLM_chartComponent_eq_sum`: the change of chart and frame for the
  components.
* `Bundle.Trivialization.contDiffOn_abs_det_fderiv_mul_coord_coordChangeL`: the smoothness of the
  coefficients.
* `Bundle.Trivialization.exists_restrictCLM_chartComponent_eq_sum`: the change of chart and frame
  near a point, with globally smooth coefficients.
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

@[simp]
theorem chartComponent_add (T T' : BundleTest I F V →L_c[ℝ] ℝ) (v : F) :
    t.chartComponent c hc hct (T + T') v =
      t.chartComponent c hc hct T v + t.chartComponent c hc hct T' v := by
  ext φ
  simp

@[simp]
theorem chartComponent_smul (a : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) (v : F) :
    t.chartComponent c hc hct (a • T) v = (a : ℂ) • t.chartComponent c hc hct T v := by
  ext φ
  simp

@[simp]
theorem chartComponent_neg (T : BundleTest I F V →L_c[ℝ] ℝ) (v : F) :
    t.chartComponent c hc hct (-T) v = -t.chartComponent c hc hct T v := by
  ext φ
  simp

@[simp]
theorem chartComponent_sub (T T' : BundleTest I F V →L_c[ℝ] ℝ) (v : F) :
    t.chartComponent c hc hct (T - T') v =
      t.chartComponent c hc hct T v - t.chartComponent c hc hct T' v := by
  ext φ
  simp

/-- The components of a real functional are real distributions: complex conjugation fixes
them. -/
@[simp]
theorem mapCLM_conj_chartComponent (T : BundleTest I F V →L_c[ℝ] ℝ) (v : F) :
    mapCLM conjCLE.toContinuousLinearMap (t.chartComponent c hc hct T v) =
      t.chartComponent c hc hct T v := by
  ext φ
  simp

/-- The component along `v` of the local representative of the point mass `δ_x ℓ`, in a chart
whose source contains `x`, is the Euclidean point mass at `c x` times `ℓ (t⁻¹ v)`. -/
theorem chartComponent_delta_of_mem {x : M} (hx : x ∈ c.source) (ℓ : V x →L[ℝ] ℝ) (v : F) :
    t.chartComponent c hc hct (BundleTest.delta x ℓ) v =
      ((ℓ (t.symmL ℝ x v) : ℝ) : ℂ) •
        mapCLM ofRealCLM (Distribution.delta (c x) : 𝓓'(⟨c.target, c.open_target⟩, ℝ)) := by
  rw [chartComponent_def, chartDistributionCLM_delta_of_mem _ _ _ _ hx]
  ext φ
  simp [mul_comm]

/-- In a chart whose source does not contain `x`, every component of the local representative of a
point mass at `x` vanishes. -/
theorem chartComponent_delta_of_notMem {x : M} (hx : x ∉ c.source) (ℓ : V x →L[ℝ] ℝ) (v : F) :
    t.chartComponent c hc hct (BundleTest.delta x ℓ) v = 0 := by
  rw [chartComponent_def, chartDistributionCLM_delta_of_notMem _ _ _ _ hx, map_zero]

/-- The components along a basis of the model fibre determine all components: the component along
`v` is the combination of those along `b i` with the coordinates of `v`. -/
theorem chartComponent_eq_sum {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ F)
    (T : BundleTest I F V →L_c[ℝ] ℝ) (v : F) :
    t.chartComponent c hc hct T v = ∑ i, (b.repr v i : ℂ) • t.chartComponent c hc hct T (b i) := by
  ext φ
  simp only [chartComponent_apply, sum_apply, smul_apply, smul_eq_mul,
    ← chartDistributionCLM_apply_apply]
  conv_lhs => rw [← b.sum_repr v]
  simp only [map_sum, map_smul, smul_eq_mul, ofReal_sum, ofReal_mul]

variable {t c hc hct} in
/-- If over an open set `B` the local representative of `S` is `g` times that of `T`, then so are
its components. -/
theorem restrictCLM_chartComponent_eq_smulLeftCLM {S T : BundleTest I F V →L_c[ℝ] ℝ} {B : Opens E}
    {g : E → ℝ} (hg : ContDiff ℝ ∞ g)
    (h : (restrictCLM (t.chartDistributionCLM c hc hct S) : 𝓓'(B, F →L[ℝ] ℝ)) =
      Distribution.smulLeftCLM hg (restrictCLM (t.chartDistributionCLM c hc hct T))) (v : F) :
    (restrictCLM (t.chartComponent c hc hct S v) : 𝓓'(B, ℂ)) =
      Distribution.smulLeftCLM hg (restrictCLM (t.chartComponent c hc hct T v)) := by
  ext φ
  have h := congr($h φ v)
  simp only [restrictCLM_apply, chartDistributionCLM_apply_apply,
    Distribution.smulLeftCLM_apply] at h
  simp [h]

/-- If a functional `T` on bundle tests vanishes on a set `U`, then its components in a chart `c`
and a frame `t` vanish on the part `c.target ∩ c⁻¹ ⁻¹' U` of the chart target read from `U`. -/
theorem isVanishingOn_chartComponent {T : BundleTest I F V →L_c[ℝ] ℝ} {U : Set M}
    (hTU : BundleTest.IsVanishingOn ⇑T U) (v : F) :
    IsVanishingOn (t.chartComponent c hc hct T v) (c.target ∩ c.symm ⁻¹' U) := by
  intro φ hφ
  rw [chartComponent_apply, BundleTest.isVanishingOn_iff.1 hTU _ ?_, Complex.ofReal_zero]
  have h := tsupport_chartTestSection (n := ⊤) t c hc hct
    (TestFunction.postcompCLM (toSpanSingleton ℝ v) φ)
  rw [ContMDiffSection.tsupport_def] at h
  rw [coe_chartTestCLM, h]
  rintro _ ⟨z, hz, rfl⟩
  rw [TestFunction.postcompCLM_apply] at hz
  exact (hφ (tsupport_comp_subset (map_zero _) φ hz)).2

/-- Over the chart target, the support of a component of `T` lies in the image under the chart of
the support of `T`. -/
theorem dsupport_chartComponent_inter_target_subset (T : BundleTest I F V →L_c[ℝ] ℝ) (v : F) :
    Distribution.dsupport (t.chartComponent c hc hct T v) ∩ c.target ⊆
      c.symm ⁻¹' BundleTest.dsupport T := by
  rintro z ⟨hzT, hzc⟩
  by_contra hx
  obtain ⟨U, hU, hxU, hTU⟩ := BundleTest.notMem_dsupport_iff.1 hx
  exact (Distribution.notMem_dsupport_iff z).2 ⟨_, isVanishingOn_chartComponent t c hc hct hTU v,
    c.isOpen_inter_preimage_symm hU, hzc, hxU⟩ hzT

/-! ### Changes of chart and frame -/

section Transition

variable {t c hc hct}
variable {t' : Trivialization F (π F V)} [MemTrivializationAtlas t']
  {c' : OpenPartialHomeomorph M E}
  {hc' : ContMDiffOn I 𝓘(ℝ, E) ∞ c' c'.source} {hct' : c'.source ⊆ t'.baseSet}

/-- **Change of chart and frame for test functions.** Let `φ` be a test function supported in an
open set `B` of the source of the chart transition `κ = c ∘ c'⁻¹`, and `gⱼ` smooth functions equal
on `B` to `|det Dκ| bⱼ*(G(c'⁻¹ ·) v)`, where `G = t ∘ t'⁻¹` is the change of frame and `(bⱼ)` the
basis `Module.finBasis ℝ F`. Then the bundle test `φ • v` read in `(t', c')` is the sum of the
bundle tests `(κ_* (gⱼ φ)) • bⱼ` read in `(t, c)`. -/
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

/-- **Change of chart and frame for the components.** Let `B` be an open set in the source of the
chart transition `κ = c ∘ c'⁻¹`, and `gⱼ` smooth functions equal on `B` to
`|det Dκ| · bⱼ*(G(c'⁻¹ ·) v)`, where `G = t ∘ t'⁻¹` is the change of frame and `(bⱼ)` the basis
`Module.finBasis ℝ F`. Then on `B` the component along `v` in `(t', c')` is `∑ⱼ gⱼ κ^* S_{bⱼ}`,
where `S_{bⱼ}` are the components in `(t, c)` and `κ^*` is the pullback of distributions. -/
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
theorem contDiffOn_abs_det_fderiv_mul_coord_coordChangeL
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

/-- **Change of chart and frame near a point.** Every point `y` of the source of the chart
transition `κ = c ∘ c'⁻¹` has an open neighbourhood `B` in the source of `κ` and smooth functions
`gⱼ` on `E` such that on `B` the component along `v` in `(t', c')` is `∑ⱼ gⱼ κ^* S_{bⱼ}`, where
`S_{bⱼ}` are the components in `(t, c)` along the basis `(bⱼ) = Module.finBasis ℝ F` and `κ^*` is
the pullback of distributions. On `B`, `gⱼ = |det Dκ| · bⱼ*(G(c'⁻¹ ·) v)` for the change of frame
`G = t ∘ t'⁻¹` (`Bundle.Trivialization.restrictCLM_chartComponent_eq_sum`). -/
theorem exists_restrictCLM_chartComponent_eq_sum
    (hcs' : ContMDiffOn 𝓘(ℝ, E) I ∞ c'.symm c'.target)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) (c'.symm.trans c) (c'.symm.trans c).source)
    (he' : ContDiffOn ℝ (⊤ : ℕ∞) (c'.symm.trans c).symm (c'.symm.trans c).target)
    (T : BundleTest I F V →L_c[ℝ] ℝ) (v : F) {y : E} (hy : y ∈ (c'.symm.trans c).source) :
    ∃ (B : Opens E) (hB : (B : Set E) ⊆ (c'.symm.trans c).source)
      (hBc : MapsTo (c'.symm.trans c) B (⟨c.target, c.open_target⟩ : Opens E))
      (g : Fin (Module.finrank ℝ F) → E → ℝ) (hg : ∀ j, ContDiff ℝ ∞ (g j)), y ∈ B ∧
      (restrictCLM (t'.chartComponent c' hc' hct' T v) : 𝓓'(B, ℂ)) =
        ∑ j, smulLeftCLM (hg j) (compCLMOfOpenPartialHomeomorph (c'.symm.trans c) he he' hB hBc
          (t.chartComponent c hc hct T (Module.finBasis ℝ F j))) := by
  -- A neighbourhood `B` of `y` with compact closure in the source of the transition.
  obtain ⟨W, hWo, hyW, hWs, hWc⟩ := exists_open_between_and_isCompact_closure isCompact_singleton
    (c'.symm.trans c).open_source (singleton_subset_iff.2 hy)
  have hB : W ⊆ (c'.symm.trans c).source := subset_closure.trans hWs
  -- Globally smooth coefficients agreeing with those of the change of chart and frame on `B`.
  choose g hg _ _ _ hgf using fun j ↦
    (contDiffOn_abs_det_fderiv_mul_coord_coordChangeL (hct := hct) (hct' := hct') he he' hcs' v
      j).exists_contDiff_eventuallyEq_on_isCompact hWc (c'.symm.trans c).open_source hWs
  exact ⟨⟨W, hWo⟩, hB, fun z hz ↦ ((c'.symm.trans c).map_source (hB hz)).1, g, hg,
    singleton_subset_iff.1 hyW, restrictCLM_chartComponent_eq_sum T v he he' hB _ hg
      fun j z hz ↦ (hgf j z (subset_closure hz)).eq_of_nhds⟩

end Transition

end Bundle.Trivialization

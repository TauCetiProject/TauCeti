/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.Green.Directional
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Calculus.FDeriv.Const
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Calculus.Deriv.Complex
import TauCeti.Analysis.Calculus.TangentCone.Basic
import TauCeti.Analysis.Normed.Group.CompactSupport

/-!
# Directional Green identities on the half-plane

For a compactly supported `C¹` map `g : ℂ → G` into a real normed space, write `z = s + i t`.
Over the half-plane `{0 < t}` the integral of `∂_s g` vanishes, and the integral of `∂_t g` is
minus the integral of the boundary values of `g` on `ℝ`. Both follow from the directional Green
identities on a rectangle containing the support of `g` in the closed half-plane. For a
noncomplete target both sides vanish by the convention for the Bochner integral.

## Main results

* `TauCeti.setIntegral_im_pos_fderiv_one_eq_zero`: `∫_{0 < t} ∂_s g = 0`.
* `TauCeti.setIntegral_im_pos_fderiv_I_eq_neg_integral`: `∫_{0 < t} ∂_t g = -∫_ℝ g`.
* `TauCeti.setIntegral_im_pos_fderiv_one_eq_zero_of_contDiffOn` and
  `TauCeti.setIntegral_im_pos_fderiv_I_eq_neg_integral_of_contDiffOn`: the same identities for `g`
  only `C¹` up to the real axis on the closed half-plane `{0 ≤ t}`, as for the product of a test
  function with a map that is `C¹` up to the axis. The derivative on the open half-plane is
  the derivative at the point, and the boundary values enter only through `g` on `ℝ`.
* `TauCeti.integrableOn_im_pos_fderiv_apply_of_contDiffOn`: the directional derivatives of such a
  `g` are integrable on the open half-plane.
* `TauCeti.setIntegral_inter_im_pos_eq_setIntegral_im_pos`: for a function vanishing at the
  points of the half-plane outside `s`, the integral over `s ∩ {0 < t}` is that over the
  half-plane.
* `TauCeti.setIntegral_Ioo_eq_integral_of_ofReal_notMem_ball`: for a function vanishing at the
  real points outside the disc of radius `r`, the integral over `(-r, r)` is that over `ℝ`.
-/

public section

open Complex MeasureTheory Metric Set

namespace TauCeti

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Over the half-plane, the integral of a function vanishing outside the disc of radius `R`
is its integral over the closed rectangle `[-R, R] × [0, R]`. -/
private theorem setIntegral_im_pos_eq_verticalRegion {f : ℂ → G} {R : ℝ}
    (hf : ∀ z, R ≤ ‖z‖ → f z = 0) :
    ∫ z in {z : ℂ | 0 < z.im}, f z =
      ∫ z in Green.verticalRegion (-R) R (fun _ ↦ 0) (fun _ ↦ R), f z := by
  set S := {z : ℂ | 0 < z.im}
  set K := Green.verticalRegion (-R) R (fun _ ↦ 0) (fun _ ↦ R)
  have hS : MeasurableSet S := measurableSet_lt measurable_const Complex.measurable_im
  have hK : MeasurableSet K :=
    Green.measurableSet_verticalRegion continuousOn_const continuousOn_const
  have hline : volume {z : ℂ | z.im = 0} = 0 := by
    have hker : (LinearMap.ker (Complex.imLm : ℂ →ₗ[ℝ] ℝ) : Set ℂ) = {z : ℂ | z.im = 0} := by
      ext z
      simp
    rw [← hker]
    refine Measure.addHaar_submodule volume _ fun h ↦ ?_
    have hI : Complex.I ∈ LinearMap.ker (Complex.imLm : ℂ →ₗ[ℝ] ℝ) := h ▸ Submodule.mem_top
    simp at hI
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hS (s := S ∩ K) inter_subset_left ?_,
    setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hK.nullMeasurableSet (s := S ∩ K)
      inter_subset_right ?_]
  · refine (measure_eq_zero_iff_ae_notMem.1 hline).mono fun z hz hzK ↦ ?_
    obtain ⟨hzK, hzS⟩ := hzK
    exact absurd (le_antisymm (not_lt.1 fun h ↦ hzS ⟨h, hzK⟩)
      (Green.mem_verticalRegion.1 hzK).2.1) hz
  · rintro z ⟨hzS, hzK⟩
    refine hf z ?_
    by_contra hlt
    rw [not_le] at hlt
    have hre := Complex.abs_re_le_norm z
    have him := Complex.abs_im_le_norm z
    rw [abs_le] at hre him
    exact hzK ⟨hzS, Green.mem_verticalRegion.2
      ⟨⟨by linarith, by linarith⟩, le_of_lt hzS, by linarith⟩⟩

/-- A function vanishing at the points of the half-plane outside `s` has the same integral over
`s ∩ {0 < t}` as over the half-plane, for any measure. -/
theorem setIntegral_inter_im_pos_eq_setIntegral_im_pos {μ : Measure ℂ} {f : ℂ → G} {s : Set ℂ}
    (hf : ∀ z : ℂ, 0 < z.im → z ∉ s → f z = 0) :
    ∫ z in s ∩ {z : ℂ | 0 < z.im}, f z ∂μ = ∫ z in {z : ℂ | 0 < z.im}, f z ∂μ :=
  (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (measurableSet_lt measurable_const Complex.measurable_im) inter_subset_right
    fun z hz ↦ hf z hz.1 fun h ↦ hz.2 ⟨h, hz.1⟩).symm

/-- A function on `ℝ` vanishing at the real points outside the disc of radius `r` has the same
integral over `(-r, r)` as over `ℝ`, for any measure. -/
theorem setIntegral_Ioo_eq_integral_of_ofReal_notMem_ball {μ : Measure ℝ} {f : ℝ → G} {r : ℝ}
    (hf : ∀ s : ℝ, (s : ℂ) ∉ ball 0 r → f s = 0) :
    ∫ s in Ioo (-r) r, f s ∂μ = ∫ s : ℝ, f s ∂μ :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs ↦ hf s fun h ↦ hs (by
    rwa [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_lt] at h)

/-! ### Maps that are `C¹` up to the real axis -/

section ClosedHalfPlane

variable {g : ℂ → G} (hg : ContDiffOn ℝ 1 g {z : ℂ | 0 ≤ z.im}) (hgc : HasCompactSupport g)

include hg in
/-- The derivative within the closed half-plane is the derivative at points of the open one. -/
private theorem hasFDerivAt_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    HasFDerivAt g (fderivWithin ℝ g {z : ℂ | 0 ≤ z.im} z) z := by
  have hmem : {z : ℂ | 0 ≤ z.im} ∈ nhds z :=
    Filter.mem_of_superset ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)
      fun w (hw : 0 < w.im) ↦ hw.le
  rw [fderivWithin_of_mem_nhds hmem]
  exact ((hg.differentiableOn one_ne_zero).differentiableAt hmem).hasFDerivAt

include hg in
/-- Slices of `g` parallel to the real axis in the closed half-plane are differentiable, with the
derivative within the closed half-plane in the direction `1`. -/
private theorem hasDerivAt_re_slice_of_im_nonneg {x y : ℝ} (hy : 0 ≤ y) :
    HasDerivAt (fun x : ℝ ↦ g ⟨x, y⟩) (fderivWithin ℝ g {z : ℂ | 0 ≤ z.im} ⟨x, y⟩ 1) x := by
  have hl : HasDerivAt (fun x : ℝ ↦ (⟨x, y⟩ : ℂ)) 1 x :=
    (hasFDerivAt_id (𝕜 := ℝ) (⟨x, y⟩ : ℂ)).hasDerivAt_re_slice
  have hd := (hg.differentiableOn one_ne_zero ⟨x, y⟩ hy).hasFDerivWithinAt
  rw [← hasDerivWithinAt_univ]
  exact hd.comp_hasDerivWithinAt x hl.hasDerivWithinAt fun _ _ ↦ hy

include hg in
/-- The derivative within the closed half-plane, in a fixed direction, is integrable on every
compact set of the closed half-plane. -/
private theorem integrableOn_fderivWithin_apply {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ {z : ℂ | 0 ≤ z.im}) (v : ℂ) :
    IntegrableOn (fun z ↦ fderivWithin ℝ g {z : ℂ | 0 ≤ z.im} z v) K :=
  (((hg.continuousOn_fderivWithin (uniqueDiffOn_setOfPred_le_im 0) le_rfl).mono hKH).clm_apply
    continuousOn_const).integrableOn_compact hK

include hg hgc

/-- For a compactly supported map `g` that is `C¹` up to the real axis on the closed half-plane,
each directional derivative of `g` is integrable on the open half-plane. -/
theorem integrableOn_im_pos_fderiv_apply_of_contDiffOn (v : ℂ) :
    IntegrableOn (fun z ↦ fderiv ℝ g z v) {z : ℂ | 0 < z.im} := by
  have hm : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  have hK : IsCompact (tsupport g ∩ {z : ℂ | 0 ≤ z.im}) :=
    hgc.isCompact.inter_right (isClosed_le continuous_const Complex.continuous_im)
  have h := (integrableOn_fderivWithin_apply hg hK inter_subset_right v).of_forall_sdiff_eq_zero
    hm fun z hz ↦ by
      have hz' : 0 ≤ z.im := le_of_lt hz.1
      rw [fderivWithin_of_notMem_tsupport ℝ fun h ↦ hz.2 ⟨h, hz'⟩]
      rfl
  exact h.congr_fun (fun z (hz : 0 < z.im) ↦ by rw [(hasFDerivAt_of_im_pos hg hz).fderiv]) hm

/-- The half-plane integral of `∂_s g` vanishes for a compactly supported map `g` that is `C¹` up
to the real axis on the closed half-plane. -/
theorem setIntegral_im_pos_fderiv_one_eq_zero_of_contDiffOn :
    ∫ z in {z : ℂ | 0 < z.im}, fderiv ℝ g z 1 = 0 := by
  by_cases hG : CompleteSpace G
  swap
  · exact integral_of_not_completeSpace hG
  obtain ⟨R, hR, hgR⟩ := hgc.exists_pos_le_norm_notMem_tsupport
  set D := fderivWithin ℝ g {z : ℂ | 0 ≤ z.im}
  have hreg : Green.verticalRegion (-R) R (fun _ ↦ 0) (fun _ ↦ R) ⊆ {z : ℂ | 0 ≤ z.im} :=
    fun z hz ↦ (Green.mem_verticalRegion.1 hz).2.1
  have hint := integrableOn_fderivWithin_apply hg
    (Green.isCompact_verticalRegion continuousOn_const continuousOn_const) hreg 1
  have hset : Green.verticalRegion (-R) R (fun _ ↦ 0) (fun _ ↦ R) =
      Green.horizontalRegion 0 R (fun _ ↦ -R) (fun _ ↦ R) := by
    ext z
    simp only [Green.mem_verticalRegion, Green.mem_horizontalRegion]
    tauto
  have hside : ∀ y : ℝ, g ⟨R, y⟩ - g ⟨-R, y⟩ = 0 := fun y ↦ by
    rw [image_eq_zero_of_notMem_tsupport (hgR _ ?_), image_eq_zero_of_notMem_tsupport (hgR _ ?_),
      sub_zero]
    · simpa [abs_of_pos hR] using Complex.abs_re_le_norm ⟨-R, y⟩
    · simpa [abs_of_pos hR] using Complex.abs_re_le_norm ⟨R, y⟩
  rw [setIntegral_congr_fun (measurableSet_lt measurable_const Complex.measurable_im)
      fun z (hz : 0 < z.im) ↦ by rw [(hasFDerivAt_of_im_pos hg hz).fderiv],
    setIntegral_im_pos_eq_verticalRegion (R := R) fun z hz ↦ by
      rw [fderivWithin_of_notMem_tsupport ℝ (hgR z hz)]; rfl,
    hset, ← Green.integral_graphs_sub_eq_integral_horizontalRegion hR.le continuousOn_const
      continuousOn_const (fun _ _ ↦ by linarith)
      (fun y hy x _ ↦ (hasDerivAt_re_slice_of_im_nonneg hg hy.1).continuousAt.continuousWithinAt)
      (R := fun z ↦ D z 1)
      (fun y hy x _ ↦ hasDerivAt_re_slice_of_im_nonneg hg hy.1)
      (hset ▸ hint)]
  simp [hside]

/-- The half-plane integral of `∂_t g`, for a compactly supported map `g` that is `C¹` up to the
real axis on the closed half-plane, is minus the integral of its boundary values on `ℝ`. -/
theorem setIntegral_im_pos_fderiv_I_eq_neg_integral_of_contDiffOn :
    ∫ z in {z : ℂ | 0 < z.im}, fderiv ℝ g z I = -∫ s : ℝ, g s := by
  by_cases hG : CompleteSpace G
  swap
  · rw [integral_of_not_completeSpace hG, integral_of_not_completeSpace hG, neg_zero]
  obtain ⟨R, hR, hgR⟩ := hgc.exists_pos_le_norm_notMem_tsupport
  set D := fderivWithin ℝ g {z : ℂ | 0 ≤ z.im}
  have hreg : Green.verticalRegion (-R) R (fun _ ↦ 0) (fun _ ↦ R) ⊆ {z : ℂ | 0 ≤ z.im} :=
    fun z hz ↦ (Green.mem_verticalRegion.1 hz).2.1
  have hint := integrableOn_fderivWithin_apply hg
    (Green.isCompact_verticalRegion continuousOn_const continuousOn_const) hreg I
  have hslice : ∀ x : ℝ, ContinuousOn (fun y : ℝ ↦ g ⟨x, y⟩) (Icc 0 R) := fun x ↦
    hg.continuousOn.comp (Complex.equivRealProdCLM.symm.continuous.comp
      (continuous_const.prodMk continuous_id)).continuousOn fun y hy ↦ hy.1
  have hgreen := Green.integral_graphs_sub_eq_neg_integral_verticalRegion (P := g)
    (by linarith : -R ≤ R) continuousOn_const continuousOn_const (fun _ _ ↦ hR.le)
    (fun x _ ↦ hslice x)
    (R := fun z ↦ D z I)
    (fun x _ y hy ↦ (hasFDerivAt_of_im_pos hg (z := ⟨x, y⟩) hy.1).hasDerivAt_im_slice)
    hint
  have htop : ∀ x : ℝ, g ⟨x, R⟩ = 0 := fun x ↦ image_eq_zero_of_notMem_tsupport (hgR _ (by
    simpa [abs_of_pos hR] using Complex.abs_im_le_norm ⟨x, R⟩))
  have hbottom : ∫ x in -R..R, g ⟨x, 0⟩ = ∫ s : ℝ, g s := by
    simp_rw [Complex.mk_eq_add_mul_I, Complex.ofReal_zero, zero_mul, add_zero]
    rw [intervalIntegral.integral_of_le (by linarith)]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs ↦
      image_eq_zero_of_notMem_tsupport (hgR _ ?_)
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hs
    rw [Complex.norm_real, Real.norm_eq_abs]
    rcases hs with hs | hs
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      exact hs.le
  simp only [htop, sub_zero] at hgreen
  rw [setIntegral_congr_fun (measurableSet_lt measurable_const Complex.measurable_im)
      fun z (hz : 0 < z.im) ↦ by rw [(hasFDerivAt_of_im_pos hg hz).fderiv],
    setIntegral_im_pos_eq_verticalRegion (R := R) fun z hz ↦ by
      rw [fderivWithin_of_notMem_tsupport ℝ (hgR z hz)]; rfl, ← hbottom, hgreen, neg_neg]

end ClosedHalfPlane

variable {g : ℂ → G} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
include hg hgc

/-- The half-plane integral of `∂_s g` vanishes for a compactly supported `C¹` map `g`. -/
theorem setIntegral_im_pos_fderiv_one_eq_zero :
    ∫ z in {z : ℂ | 0 < z.im}, fderiv ℝ g z 1 = 0 :=
  setIntegral_im_pos_fderiv_one_eq_zero_of_contDiffOn hg.contDiffOn hgc

/-- The half-plane integral of `∂_t g` for a compactly supported `C¹` map `g` is minus the
integral of its boundary values on `ℝ`. -/
theorem setIntegral_im_pos_fderiv_I_eq_neg_integral :
    ∫ z in {z : ℂ | 0 < z.im}, fderiv ℝ g z I = -∫ s : ℝ, g s :=
  setIntegral_im_pos_fderiv_I_eq_neg_integral_of_contDiffOn hg.contDiffOn hgc

end TauCeti

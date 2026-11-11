/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.Green.Directional
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Calculus.Deriv.Complex
import TauCeti.Analysis.Normed.Group.CompactSupport

/-!
# Directional Green identities on the half-plane

For a compactly supported `C¹` map `g : ℂ → G` into a real Banach space, write `z = s + i t`.
Over the half-plane `{0 < t}` the integral of `∂_s g` vanishes, and the integral of `∂_t g` is
minus the integral of the boundary values of `g` on `ℝ`. Both follow from the directional Green
identities on a rectangle containing the support of `g` in the closed half-plane.

## Main results

* `TauCeti.setIntegral_im_pos_fderiv_one_eq_zero`: `∫_{0 < t} ∂_s g = 0`.
* `TauCeti.setIntegral_im_pos_fderiv_I_eq_neg_integral`: `∫_{0 < t} ∂_t g = -∫_ℝ g`.
-/

public section

open Complex MeasureTheory Metric Set

namespace TauCeti

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

omit [CompleteSpace G] in
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

variable {g : ℂ → G} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
include hg hgc

/-- The half-plane integral of `∂_s g` vanishes for a compactly supported `C¹` map `g`. -/
theorem setIntegral_im_pos_fderiv_one_eq_zero :
    ∫ z in {z : ℂ | 0 < z.im}, fderiv ℝ g z 1 = 0 := by
  obtain ⟨R, hR, hgR⟩ := hgc.exists_pos_le_norm_notMem_tsupport
  have hd := hg.differentiable one_ne_zero
  have hint : Integrable fun z ↦ fderiv ℝ g z 1 :=
    ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hgc.fderiv_apply (𝕜 := ℝ) 1)
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
  rw [setIntegral_im_pos_eq_verticalRegion (R := R) fun z hz ↦ by
      rw [fderiv_of_notMem_tsupport ℝ (hgR z hz)]; rfl,
    hset, ← Green.integral_graphs_sub_eq_integral_horizontalRegion hR.le continuousOn_const
      continuousOn_const (fun _ _ ↦ by linarith)
      (fun y _ x _ ↦ (hd ⟨x, y⟩).hasFDerivAt.hasDerivAt_re_slice.continuousAt.continuousWithinAt)
      (R := fun z ↦ fderiv ℝ g z 1)
      (fun y _ x _ ↦ (hd ⟨x, y⟩).hasFDerivAt.hasDerivAt_re_slice)
      hint.integrableOn]
  simp [hside]

/-- The half-plane integral of `∂_t g` for a compactly supported `C¹` map `g` is minus the
integral of its boundary values on `ℝ`. -/
theorem setIntegral_im_pos_fderiv_I_eq_neg_integral :
    ∫ z in {z : ℂ | 0 < z.im}, fderiv ℝ g z I = -∫ s : ℝ, g s := by
  obtain ⟨R, hR, hgR⟩ := hgc.exists_pos_le_norm_notMem_tsupport
  have hd := hg.differentiable one_ne_zero
  have hint : Integrable fun z ↦ fderiv ℝ g z I :=
    ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hgc.fderiv_apply (𝕜 := ℝ) I)
  have hgreen := Green.integral_graphs_sub_eq_neg_integral_verticalRegion (P := g)
    (by linarith : -R ≤ R) continuousOn_const continuousOn_const (fun _ _ ↦ hR.le)
    (fun x _ y _ ↦ (hd ⟨x, y⟩).hasFDerivAt.hasDerivAt_im_slice.continuousAt.continuousWithinAt)
    (R := fun z ↦ fderiv ℝ g z I)
    (fun x _ y _ ↦ (hd ⟨x, y⟩).hasFDerivAt.hasDerivAt_im_slice)
    hint.integrableOn
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
  rw [setIntegral_im_pos_eq_verticalRegion (R := R) fun z hz ↦ by
      rw [fderiv_of_notMem_tsupport ℝ (hgR z hz)]; rfl, ← hbottom, hgreen, neg_neg]

end TauCeti

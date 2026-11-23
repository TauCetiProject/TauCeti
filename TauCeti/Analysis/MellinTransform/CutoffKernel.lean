/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinInversion
import TauCeti.Analysis.MellinTransform.Convolution
import TauCeti.Analysis.MellinTransform.Decay

/-!
# The Mellin cutoff kernel

For a cutoff `φ : ℝ → E` with values in a real normed space this file defines the *Mellin cutoff
kernel* `F₁(φ, x) = ∫_{(x,∞)} φ(y) dy/y`, the upper tail of `φ` for the multiplicative measure
`dy/y`. A smoothed approximate functional equation weights the terms of a Dirichlet series with
it.

By Fubini, for `φ : ℝ → ℂ` the kernel `F₁(φ, ·)` has Mellin transform `mellin φ s / s` on
`Re s > 0`; it is the Mellin convolution of the sharp cutoff `1_(0,1]`, whose transform is `1 / s`,
with `φ`. When `φ` is Mellin convergent at `σ > 0` and `mellin φ s / s` is integrable on the line
`Re s = σ` (as for `φ` of class `C¹` on `(0, ∞)` with compact positive support), Mellin inversion
then gives `F₁(φ, x) = (2π)⁻¹ ∫_ℝ x^{-s} mellin φ s / s dt` on that line. This is the form in
which the kernel enters contour shifts. When `φ` vanishes on `(0, x)` the kernel equals the
multiplicative mass `mellin φ 0`, and when `φ` vanishes on `(x, ∞)` it is zero, so a cutoff
supported in `[a, b] ⊆ (0, ∞)` and normalized by `mellin φ 0 = 1` has kernel `1` on `(0, a]` and
`0` on `[b, ∞)`.

## Main definitions

* `TauCeti.mellinCutoffKernel φ x`: the kernel `F₁(φ, x) = ∫_{(x,∞)} y⁻¹ • φ(y) dy`.

## Main results

* `TauCeti.mellinCutoffKernel_eq_integral_mul_div`: `F₁(φ, ·)` is the Mellin convolution of the
  sharp cutoff `1_(0,1]` with `φ`.
* `MellinConvergent.hasMellin_mellinCutoffKernel`: `mellin F₁(φ, ·) s = mellin φ s / s` for
  `Re s > 0`, with absolute convergence.
* `MellinConvergent.mellinCutoffKernel_eq_mellinInv`: Mellin inversion of the kernel on
  `Re s = σ > 0`, and `ContDiffOn.mellinCutoffKernel_eq_mellinInv` for a `C¹` cutoff with compact
  positive support.
* `Filter.EventuallyEq.mellinCutoffKernel_eq_mellin_zero`,
  `Filter.EventuallyEq.mellinCutoffKernel_eq_zero`: the kernel below and above the support of `φ`.
* `TauCeti.mellinCutoffKernel_comp_div`: scaling the cutoff scales the kernel.
* `MeasureTheory.IntegrableOn.continuousOn_mellinCutoffKernel`: continuity of the kernel.
* `TauCeti.mellinCutoffKernel_ofReal`: the kernel commutes with the coercion `ℝ → ℂ`.

## References

* W. Luo, Z. Rudnick and P. Sarnak, *On Selberg's eigenvalue conjecture*, Geom. Funct. Anal. 5
  (1995), 387–401, equation (3.6) and Lemma 3.1.
-/

public section

open Set MeasureTheory Complex

namespace TauCeti

section RealNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The *Mellin cutoff kernel* `F₁(φ, x) = ∫_{(x,∞)} φ(y) dy/y` of a cutoff `φ : ℝ → E`: the
upper tail of `φ` for the multiplicative measure `dy/y`. -/
noncomputable def mellinCutoffKernel (φ : ℝ → E) (x : ℝ) : E :=
  ∫ y in Ioi x, y⁻¹ • φ y

theorem mellinCutoffKernel_def (φ : ℝ → E) (x : ℝ) :
    mellinCutoffKernel φ x = ∫ y in Ioi x, y⁻¹ • φ y := (rfl)

/-- The cutoff kernel of the zero cutoff vanishes. -/
@[simp]
theorem mellinCutoffKernel_zero (x : ℝ) : mellinCutoffKernel (0 : ℝ → E) x = 0 := by
  simp [mellinCutoffKernel_def]

variable {φ : ℝ → E} {x : ℝ}

/-- If `φ` vanishes almost everywhere on `(x, ∞)`, its cutoff kernel vanishes at `x`. -/
theorem _root_.Filter.EventuallyEq.mellinCutoffKernel_eq_zero
    (h : φ =ᵐ[volume.restrict (Ioi x)] 0) : mellinCutoffKernel φ x = 0 := by
  rw [mellinCutoffKernel_def]
  exact integral_eq_zero_of_ae (h.mono fun y hy ↦ by simp [hy])

/-- Scaling the cutoff by `c > 0` scales the argument of its kernel:
`F₁(φ(· / c), x) = F₁(φ, x / c)`, since the measure `dy/y` is dilation invariant. -/
theorem mellinCutoffKernel_comp_div (φ : ℝ → E) {c : ℝ} (hc : 0 < c) (x : ℝ) :
    mellinCutoffKernel (fun y ↦ φ (y / c)) x = mellinCutoffKernel φ (x / c) := by
  have h := integral_comp_mul_left_Ioi (fun y ↦ y⁻¹ • φ (y / c)) (x / c) hc
  rw [mul_div_cancel₀ x hc.ne'] at h
  have h2 : (∫ y in Ioi (x / c), y⁻¹ • φ y) =
      c • ∫ t in Ioi (x / c), (c * t)⁻¹ • φ (c * t / c) := by
    rw [← integral_smul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
    rw [mul_div_cancel_left₀ t hc.ne', smul_smul, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ hc.ne', one_mul]
  rw [mellinCutoffKernel_def, mellinCutoffKernel_def, h2, h, smul_inv_smul₀ hc.ne']

/-- If `y ↦ y⁻¹ • φ y` is integrable on `(a, ∞)`, the cutoff kernel is continuous on `[a, ∞)`. -/
theorem _root_.MeasureTheory.IntegrableOn.continuousOn_mellinCutoffKernel {a : ℝ}
    (h : IntegrableOn (fun y ↦ y⁻¹ • φ y) (Ioi a)) :
    ContinuousOn (mellinCutoffKernel φ) (Ici a) :=
  h.continuousOn_Ici_primitive_Ioi

end RealNormedSpace

/-- The cutoff kernel of a real cutoff, read in `ℂ`, is the real kernel read in `ℂ`. -/
@[simp, norm_cast]
theorem mellinCutoffKernel_ofReal (φ : ℝ → ℝ) (x : ℝ) :
    mellinCutoffKernel (fun y ↦ (φ y : ℂ)) x = mellinCutoffKernel φ x := by
  rw [mellinCutoffKernel_def, mellinCutoffKernel_def, ← integral_complex_ofReal]
  simp [real_smul]

section ComplexNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {φ : ℝ → E} {x : ℝ}

/-- If `φ` vanishes almost everywhere on `(0, x)`, its cutoff kernel at `x ≥ 0` is the
multiplicative mass `mellin φ 0 = ∫_{(0,∞)} φ(y) dy/y`. In particular a cutoff normalized by
`mellin φ 0 = 1` has kernel `1` below its support. -/
theorem _root_.Filter.EventuallyEq.mellinCutoffKernel_eq_mellin_zero
    (h : φ =ᵐ[volume.restrict (Ioo 0 x)] 0) (hx : 0 ≤ x) :
    mellinCutoffKernel φ x = mellin φ 0 := by
  have hm : mellin φ 0 = ∫ y in Ioi 0, y⁻¹ • φ y := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
    simp [cpow_neg_one, ← ofReal_inv, Complex.coe_smul]
  rw [hm, mellinCutoffKernel_def]
  symm
  refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet
    (Ioi_subset_Ioi hx) ?_
  filter_upwards [Measure.ae_ne volume x, (ae_restrict_iff' measurableSet_Ioo).mp h]
    with y hyx hφ hy
  simp [hφ ⟨hy.1, lt_of_le_of_ne (not_lt.mp hy.2) hyx⟩]

end ComplexNormedSpace

variable {φ : ℝ → ℂ} {x : ℝ}

/-- For `x > 0` the cutoff kernel is the Mellin convolution
`(1_(0,1] ⋆ φ)(x) = ∫_{(0,∞)} 1_(0,1](y) φ(x/y) dy/y`, by the substitution `z = x/y`. -/
theorem mellinCutoffKernel_eq_integral_mul_div (φ : ℝ → ℂ) (hx : 0 < x) :
    mellinCutoffKernel φ x =
      ∫ y in Ioi 0, (Ioc 0 1).indicator (fun _ ↦ (1 : ℂ)) y * φ (x / y) / y := by
  have hcongr : (∫ y in Ioi 0, (Ioc 0 1).indicator (fun _ ↦ (1 : ℂ)) y * φ (x / y) / y) =
      mellin (fun y ↦ (Ici x).indicator φ (x * y⁻¹)) 0 := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
    have hy0 : 0 < y := hy
    have hiff : x ≤ x * y⁻¹ ↔ y ≤ 1 := by
      rw [← div_eq_mul_inv, le_div_iff₀ hy0, mul_le_iff_le_one_right hx]
    by_cases hy1 : y ≤ 1
    · simp [indicator, hy0, hy1, hiff.mpr hy1, cpow_neg_one, div_eq_mul_inv, mul_comm]
    · simp [indicator, hy1, mt hiff.mp hy1]
  rw [hcongr, mellin_comp_inv (fun u ↦ (Ici x).indicator φ (x * u)),
    mellin_comp_mul_left _ _ hx, mellin_indicator_Ici φ hx.le, mellinCutoffKernel_def]
  simp only [neg_zero, cpow_zero, one_smul]
  refine setIntegral_congr_fun measurableSet_Ioi fun z _ ↦ ?_
  simp [cpow_neg_one]

/-- If `φ` is Mellin convergent at `s` with `Re s > 0`, its cutoff kernel is Mellin convergent at
`s` with transform `mellin φ s / s`. -/
theorem _root_.MellinConvergent.hasMellin_mellinCutoffKernel {s : ℂ} (hφ : MellinConvergent φ s)
    (hs : 0 < s.re) :
    HasMellin (mellinCutoffKernel φ) s (mellin φ s / s) := by
  have h1 := hasMellin_one_Ioc hs
  have h := hasMellin_integral_mul_div h1.1 hφ
  rw [h1.2, one_div_mul_eq_div] at h
  exact (hasMellin_congr fun x hx ↦ mellinCutoffKernel_eq_integral_mul_div φ hx).mpr h

/-- **Mellin inversion of the cutoff kernel.** If `φ` is Mellin convergent at `σ > 0` and
`s ↦ mellin φ s / s` is integrable on the line `Re s = σ`, then for `x > 0`
`F₁(φ, x) = (2π)⁻¹ ∫_ℝ x^{-(σ+it)} mellin φ (σ+it) / (σ+it) dt`. -/
theorem _root_.MellinConvergent.mellinCutoffKernel_eq_mellinInv {σ : ℝ} (hφ : MellinConvergent φ σ)
    (hV : VerticalIntegrable (fun s ↦ mellin φ s / s) σ) (hσ : 0 < σ) (hx : 0 < x) :
    mellinCutoffKernel φ x = mellinInv σ (fun s ↦ mellin φ s / s) x := by
  -- `y ↦ y ^ (s - 1) • φ y` is integrable on `(a, ∞)` when `y ↦ ‖y ^ (s - σ)‖` is bounded there
  have hmono (s : ℂ) {a : ℝ} (ha : 0 ≤ a) (C : ℝ)
      (hC : ∀ y ∈ Ioi a, ‖(y : ℂ) ^ (s - σ)‖ ≤ C) :
      IntegrableOn (fun y : ℝ ↦ (y : ℂ) ^ (s - 1) • φ y) (Ioi a) := by
    refine (integrableOn_congr_fun (fun y hy ↦ ?_) measurableSet_Ioi).mp
      (Integrable.bdd_smul (hφ.mono_set (Ioi_subset_Ioi ha)) C
        ((ContinuousOn.cpow_const (by fun_prop) fun y hy ↦
          ofReal_mem_slitPlane.mpr (ha.trans_lt hy)).aestronglyMeasurable measurableSet_Ioi)
        (ae_restrict_of_forall_mem measurableSet_Ioi hC))
    have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ha.trans_lt hy).ne'
    simp only [Pi.smul_apply', smul_smul, ← cpow_add _ _ hy0, sub_add_sub_cancel]
  have hline (t : ℝ) : HasMellin (mellinCutoffKernel φ) (σ + t * I)
      (mellin φ (σ + t * I) / (σ + t * I)) := by
    refine MellinConvergent.hasMellin_mellinCutoffKernel (hmono _ le_rfl 1 fun y hy ↦ ?_)
      (by simpa using hσ)
    rw [norm_cpow_eq_rpow_re_of_pos hy]
    simp
  have hint : IntegrableOn (fun y ↦ y⁻¹ • φ y) (Ioi (x / 2)) := by
    refine (integrableOn_congr_fun (fun y _ ↦ ?_) measurableSet_Ioi).mp
      (hmono 0 (by positivity) ((x / 2) ^ (-σ)) fun y hy ↦ ?_)
    · simp [cpow_neg_one, real_smul]
    · rw [norm_cpow_eq_rpow_re_of_pos ((half_pos hx).trans hy)]
      simpa using Real.rpow_le_rpow_of_nonpos (half_pos hx) (le_of_lt hy) (by linarith)
  have hV' : VerticalIntegrable (mellin (mellinCutoffKernel φ)) σ := by
    unfold VerticalIntegrable at hV ⊢
    simp_rw [fun t : ℝ ↦ (hline t).2]
    exact hV
  have hcont : ContinuousAt (mellinCutoffKernel φ) x :=
    hint.continuousOn_mellinCutoffKernel.continuousAt (Ici_mem_nhds (by linarith))
  rw [← mellinInv_mellin_eq σ _ hx (by simpa using (hline 0).1) hV' hcont]
  unfold mellinInv
  simp_rw [fun t : ℝ ↦ (hline t).2]

/-- **Mellin inversion of the cutoff kernel** for `φ` of class `C¹` on `(0, ∞)` with compact
positive closed support: for `σ > 0` and `x > 0`,
`F₁(φ, x) = (2π)⁻¹ ∫_ℝ x^{-(σ+it)} mellin φ (σ+it) / (σ+it) dt`. -/
theorem _root_.ContDiffOn.mellinCutoffKernel_eq_mellinInv (hφ : ContDiffOn ℝ 1 φ (Ioi 0))
    (hc : IsCompact (tsupport φ ∩ Ioi 0)) {σ : ℝ} (hσ : 0 < σ) (hx : 0 < x) :
    mellinCutoffKernel φ x = mellinInv σ (fun s ↦ mellin φ s / s) x := by
  have hm := (hφ.continuousOn.locallyIntegrableOn
    measurableSet_Ioi).mellinConvergent_of_isCompact_tsupport_inter_Ioi hc σ
  exact hm.mellinCutoffKernel_eq_mellinInv (hφ.verticalIntegrable_mellin_div hc hσ.ne') hσ hx

end TauCeti

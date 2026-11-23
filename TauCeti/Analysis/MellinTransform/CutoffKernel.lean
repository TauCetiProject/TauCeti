/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinInversion
import TauCeti.Analysis.MellinTransform
import TauCeti.Analysis.MellinTransform.Basic
import TauCeti.Analysis.MellinTransform.Convolution
import TauCeti.Analysis.MellinTransform.Decay
import TauCeti.Topology.Instances.Real.TSupport

/-!
# The Mellin cutoff kernels of an approximate functional equation

For a cutoff `φ : ℝ → ℂ` this file defines the two kernels with which a smoothed approximate
functional equation weights the terms of a Dirichlet series and of its dual:

* the *Mellin cutoff kernel* `F₁(φ, x) = ∫_{(x,∞)} φ(y) dy/y`, the upper tail of `φ` for the
  multiplicative measure `dy/y`;
* the *dual Mellin cutoff kernel*
  `F₂(φ, G, β, x) = (2π)⁻¹ ∫_ℝ x^{-s} mellin φ (-s) G(β - s) / s dt` along the line
  `s = 2 + it`, for a function `G` (in applications a ratio of gamma factors).

By Fubini, `F₁(φ, ·)` has Mellin transform `mellin φ s / s` on `Re s > 0`; it is the Mellin
convolution of the sharp cutoff `1_(0,1]`, whose transform is `1 / s`, with `φ`. For `φ` of class
`C¹` on `(0, ∞)` with compact positive support, Mellin inversion then gives
`F₁(φ, x) = (2π)⁻¹ ∫_ℝ x^{-s} mellin φ s / s dt` on every line `Re s = σ > 0`. This is the form in
which the kernel enters contour shifts. When `φ` vanishes on `(0, x)` the kernel equals the
multiplicative mass `mellin φ 0`, and when `φ` vanishes on `(x, ∞)` it is zero, so a cutoff
supported in `[a, b] ⊆ (0, ∞)` and normalized by `mellin φ 0 = 1` has kernel `1` on `(0, a]` and
`0` on `[b, ∞)`. For `G = 1` the dual kernel is the cutoff kernel of the reflected cutoff
`y ↦ φ (1 / y)`, by `mellin_comp_inv`.

## Main definitions

* `TauCeti.mellinCutoffKernel φ x`: the kernel `F₁(φ, x) = ∫_{(x,∞)} φ(y) dy/y`.
* `TauCeti.dualMellinCutoffKernel φ G β x`: the kernel `F₂(φ, G, β, x)`.

## Main results

* `TauCeti.mellinCutoffKernel_eq_integral_mul_div`: `F₁(φ, ·)` is the Mellin convolution of the
  sharp cutoff `1_(0,1]` with `φ`.
* `TauCeti.hasMellin_mellinCutoffKernel`: `mellin F₁(φ, ·) s = mellin φ s / s` for `Re s > 0`,
  with absolute convergence.
* `TauCeti.mellinCutoffKernel_eq_mellinInv`: Mellin inversion of the kernel on `Re s = σ > 0`.
* `TauCeti.mellinCutoffKernel_eq_mellin_zero`, `TauCeti.mellinCutoffKernel_eq_zero`: the kernel
  below and above the support of `φ`.
* `TauCeti.mellinCutoffKernel_comp_div`: scaling the cutoff scales the kernel.
* `TauCeti.dualMellinCutoffKernel_one`: for `G = 1` the dual kernel is the cutoff kernel of
  `y ↦ φ (1 / y)`.

## References

* W. Luo, Z. Rudnick and P. Sarnak, *On Selberg's eigenvalue conjecture*, Geom. Funct. Anal. 5
  (1995), 387–401, equations (3.6)–(3.7) and Lemma 3.1.
-/

public section

open Set MeasureTheory Complex

namespace TauCeti

/-! ### The Mellin cutoff kernel -/

/-- The *Mellin cutoff kernel* `F₁(φ, x) = ∫_{(x,∞)} φ(y) dy/y` of a cutoff `φ : ℝ → ℂ`: the
upper tail of `φ` for the multiplicative measure `dy/y`. -/
noncomputable def mellinCutoffKernel (φ : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y in Ioi x, φ y / y

theorem mellinCutoffKernel_def (φ : ℝ → ℂ) (x : ℝ) :
    mellinCutoffKernel φ x = ∫ y in Ioi x, φ y / y := (rfl)

/-- The cutoff kernel of the zero cutoff vanishes. -/
@[simp]
theorem mellinCutoffKernel_zero (x : ℝ) : mellinCutoffKernel 0 x = 0 := by
  simp [mellinCutoffKernel_def]

variable {φ : ℝ → ℂ} {x : ℝ}

/-- If `φ` vanishes on `(x, ∞)`, its cutoff kernel vanishes at `x`. -/
theorem mellinCutoffKernel_eq_zero (h : ∀ y ∈ Ioi x, φ y = 0) : mellinCutoffKernel φ x = 0 := by
  rw [mellinCutoffKernel_def]
  exact setIntegral_eq_zero_of_forall_eq_zero fun y hy ↦ by rw [h y hy, zero_div]

/-- If `φ` vanishes on `(0, x)`, its cutoff kernel at `x ≥ 0` is the multiplicative mass
`mellin φ 0 = ∫_{(0,∞)} φ(y) dy/y`. In particular a cutoff normalized by `mellin φ 0 = 1` has
kernel `1` below its support. -/
theorem mellinCutoffKernel_eq_mellin_zero (hx : 0 ≤ x) (h : ∀ y ∈ Ioo 0 x, φ y = 0) :
    mellinCutoffKernel φ x = mellin φ 0 := by
  have hm : mellin φ 0 = ∫ y in Ioi 0, φ y / y := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
    simp [cpow_neg_one, div_eq_inv_mul]
  rw [hm, mellinCutoffKernel_def]
  symm
  refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet
    (Ioi_subset_Ioi hx) ?_
  filter_upwards [Measure.ae_ne volume x] with y hyx hy
  rw [h y ⟨hy.1, lt_of_le_of_ne (not_lt.mp hy.2) hyx⟩, zero_div]

/-- Scaling the cutoff by `c > 0` scales the argument of its kernel:
`F₁(φ(· / c), x) = F₁(φ, x / c)`, since the measure `dy/y` is dilation invariant. -/
theorem mellinCutoffKernel_comp_div (φ : ℝ → ℂ) {c : ℝ} (hc : 0 < c) (x : ℝ) :
    mellinCutoffKernel (fun y ↦ φ (y / c)) x = mellinCutoffKernel φ (x / c) := by
  have h := integral_comp_mul_left_Ioi (fun y ↦ φ (y / c) / y) (x / c) hc
  rw [mul_div_cancel₀ x hc.ne'] at h
  have h2 : (∫ y in Ioi (x / c), φ y / y) =
      c • ∫ t in Ioi (x / c), φ (c * t / c) / ((c * t : ℝ) : ℂ) := by
    rw [← integral_smul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
    have hc' : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
    rw [mul_div_cancel_left₀ t hc.ne', Complex.real_smul]
    push_cast
    field_simp
  rw [mellinCutoffKernel_def, mellinCutoffKernel_def, h2, h, smul_inv_smul₀ hc.ne']

/-- If `y ↦ φ y / y` is integrable on `(a, ∞)`, the cutoff kernel is continuous on `[a, ∞)`. -/
theorem continuousOn_mellinCutoffKernel {a : ℝ} (h : IntegrableOn (fun y ↦ φ y / y) (Ioi a)) :
    ContinuousOn (mellinCutoffKernel φ) (Ici a) :=
  h.continuousOn_Ici_primitive_Ioi

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
  simp [cpow_neg_one, div_eq_inv_mul]

/-- If `φ` is Mellin convergent at `s` with `Re s > 0`, its cutoff kernel is Mellin convergent at
`s` with transform `mellin φ s / s`. -/
theorem hasMellin_mellinCutoffKernel {s : ℂ} (hφ : MellinConvergent φ s) (hs : 0 < s.re) :
    HasMellin (mellinCutoffKernel φ) s (mellin φ s / s) := by
  have h1 := hasMellin_one_Ioc hs
  have h := hasMellin_integral_mul_div h1.1 hφ
  rw [h1.2, one_div_mul_eq_div] at h
  exact (hasMellin_congr fun x hx ↦ mellinCutoffKernel_eq_integral_mul_div φ hx).mpr h

/-- **Mellin inversion of the cutoff kernel.** For `φ` of class `C¹` on `(0, ∞)` with compact
positive closed support, `σ > 0` and `x > 0`,
`F₁(φ, x) = (2π)⁻¹ ∫_ℝ x^{-(σ+it)} mellin φ (σ+it) / (σ+it) dt`. -/
theorem mellinCutoffKernel_eq_mellinInv (hφ : ContDiffOn ℝ 1 φ (Ioi 0))
    (hc : IsCompact (tsupport φ ∩ Ioi 0)) {σ : ℝ} (hσ : 0 < σ) (hx : 0 < x) :
    mellinCutoffKernel φ x = mellinInv σ (fun s ↦ mellin φ s / s) x := by
  have hconv := mellinConvergent_of_isCompact_tsupport
    (hφ.continuousOn.locallyIntegrableOn measurableSet_Ioi) hc
  have hM (s : ℂ) (hs : 0 < s.re) := hasMellin_mellinCutoffKernel (hconv s) hs
  have hline (t : ℝ) : mellin (mellinCutoffKernel φ) (σ + t * I) =
      mellin φ (σ + t * I) / (σ + t * I) := (hM _ (by simpa using hσ)).2
  have hV : VerticalIntegrable (mellin (mellinCutoffKernel φ)) σ := by
    unfold VerticalIntegrable
    simp_rw [hline]
    exact verticalIntegrable_mellin_div hφ hc hσ.ne'
  have hint : IntegrableOn (fun y ↦ φ y / y) (Ioi (x / 2)) := by
    refine ((integrableOn_congr_fun (fun y _ ↦ ?_) measurableSet_Ioi).mp (hconv 0)).mono_set
      (Ioi_subset_Ioi (by positivity))
    simp [cpow_neg_one, div_eq_inv_mul]
  have hcont : ContinuousAt (mellinCutoffKernel φ) x :=
    (continuousOn_mellinCutoffKernel hint).continuousAt (Ici_mem_nhds (by linarith))
  rw [← mellinInv_mellin_eq σ _ hx (hM σ (by simpa using hσ)).1 hV hcont]
  unfold mellinInv
  simp_rw [hline]

/-! ### The dual Mellin cutoff kernel -/

/-- The *dual Mellin cutoff kernel*
`F₂(φ, G, β, x) = (2π)⁻¹ ∫_ℝ x^{-s} mellin φ (-s) G(β - s) / s dt`, `s = 2 + it`, of a cutoff
`φ`, a function `G` and a parameter `β`. No growth condition on `G` is imposed: when the integrand
is not integrable the Bochner integral is `0`. -/
noncomputable def dualMellinCutoffKernel (φ : ℝ → ℂ) (G : ℂ → ℂ) (β : ℂ) (x : ℝ) : ℂ :=
  mellinInv 2 (fun s ↦ mellin φ (-s) * G (β - s) / s) x

theorem dualMellinCutoffKernel_def (φ : ℝ → ℂ) (G : ℂ → ℂ) (β : ℂ) (x : ℝ) :
    dualMellinCutoffKernel φ G β x = mellinInv 2 (fun s ↦ mellin φ (-s) * G (β - s) / s) x :=
  (rfl)

/-- The dual kernel of the zero function `G = 0` vanishes. -/
@[simp]
theorem dualMellinCutoffKernel_zero (φ : ℝ → ℂ) (β : ℂ) (x : ℝ) :
    dualMellinCutoffKernel φ 0 β x = 0 := by
  simp [dualMellinCutoffKernel_def, mellinInv]

/-- The dual kernel of the zero cutoff `φ = 0` vanishes. -/
@[simp]
theorem dualMellinCutoffKernel_zero_left (G : ℂ → ℂ) (β : ℂ) (x : ℝ) :
    dualMellinCutoffKernel 0 G β x = 0 := by
  simp [dualMellinCutoffKernel_def, mellinInv, mellin]

/-- For `G = 1` the dual kernel is the cutoff kernel of the reflected cutoff `y ↦ φ (1 / y)`:
`F₂(φ, 1, β, x) = F₁(φ ∘ inv, x)` for `φ` of class `C¹` on `(0, ∞)` with compact positive
closed support and `x > 0`. -/
theorem dualMellinCutoffKernel_one (hφ : ContDiffOn ℝ 1 φ (Ioi 0))
    (hc : IsCompact (tsupport φ ∩ Ioi 0)) (β : ℂ) (hx : 0 < x) :
    dualMellinCutoffKernel φ 1 β x = mellinCutoffKernel (fun y ↦ φ y⁻¹) x := by
  have hφ' : ContDiffOn ℝ 1 (fun y ↦ φ y⁻¹) (Ioi 0) :=
    hφ.comp ((contDiffOn_inv ℝ).mono fun y hy ↦ ne_of_gt hy) fun y hy ↦ inv_pos.mpr hy
  rw [mellinCutoffKernel_eq_mellinInv hφ' (isCompact_tsupport_comp_inv_inter_Ioi hc) two_pos hx,
    dualMellinCutoffKernel_def]
  simp only [Pi.one_apply, mul_one, mellin_comp_inv]

end TauCeti

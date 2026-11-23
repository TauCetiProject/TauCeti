/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LConvolution
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Prod
import TauCeti.Analysis.Convolution.Young
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import TauCeti.MeasureTheory.Integral.Prod

/-!
# Lower integrals over sliding windows

Let `μ` be a left-invariant and negation-invariant s-finite measure on a measurable commutative
additive group `G`, for instance Lebesgue measure on `ℝ`, and let `W ⊆ G` be measurable. For each
`t` the translated window `{s | s - t ∈ W}` has measure `μ W`, and every point `s` lies in the
windows of exactly the `t` with `s - t ∈ W`, again a set of measure `μ W`. By Tonelli's theorem,
integrating a nonnegative function over the sliding windows multiplies its integral by `μ W`:

`∫ (∫_{s - t ∈ W} f(s) ds) dt = μ W ∫ f`.

Combined with the Cauchy–Schwarz inequality this bounds the bilinear form of the window kernel
`1_W(s - t)` on `L²`:

`∫ (∫_{s - t ∈ W} f(s) ds) g(t) dt ≤ μ W ‖f‖₂ ‖g‖₂`,

and the square-function form
`∫ (∫_{s - t ∈ W} f(s)² ds)^{1/2} g(t) dt ≤ (μ W)^{1/2} ‖f‖₂ ‖g‖₂`. On `ℝ` with `W` an interval
of length `L`, these are the estimates for a time pairing localized to `|s - t| ≈ L`.

The window integral `t ↦ ∫_{s - t ∈ W} f(s) ds` is the convolution `f ⋆ₗ 1_{-W}`
(`MeasureTheory.lconvolution`), and the window-kernel bound is proved from the case
`L² ⋆ L¹ ⊆ L²` of Young's inequality (`MeasureTheory.eLpNorm_lconvolution_le`) combined with
Cauchy–Schwarz; the statements here keep the windows explicit, which is the form in which
time-localized pairings arise.

## Main declarations

* `MeasureTheory.lintegral_setLIntegral_sub_preimage`: the sliding-window identity.
* `MeasureTheory.setLIntegral_sub_preimage_eq_lconvolution`: the window integral as a
  convolution.
* `MeasureTheory.lintegral_rpow_setLIntegral_sub_preimage_mul_le`: the square-function bound.
* `MeasureTheory.lintegral_setLIntegral_sub_preimage_mul_le`: the bound for the window kernel.
-/

public section

open MeasureTheory Set Function
open scoped ENNReal Pointwise

namespace MeasureTheory

variable {G : Type*} [MeasurableSpace G] [AddCommGroup G] [MeasurableAdd₂ G] [MeasurableNeg G]
  {μ : Measure G} [SFinite μ] [μ.IsAddLeftInvariant] [μ.IsNegInvariant] {W : Set G}

/-- **Sliding windows.** Integrating a nonnegative function over the translated windows
`{s | s - t ∈ W}` and then over `t` multiplies its integral by `μ W`. -/
theorem lintegral_setLIntegral_sub_preimage (hW : MeasurableSet W) {f : G → ℝ≥0∞}
    (hf : AEMeasurable f μ) :
    ∫⁻ t, ∫⁻ s in (fun s ↦ s - t) ⁻¹' W, f s ∂μ ∂μ = μ W * ∫⁻ s, f s ∂μ := by
  have hS : MeasurableSet {p : G × G | p.2 - p.1 ∈ W} :=
    (measurable_snd.sub measurable_fst) hW
  calc ∫⁻ t, ∫⁻ s in (fun s ↦ s - t) ⁻¹' W, f s ∂μ ∂μ
      = ∫⁻ t, ∫⁻ s, {p : G × G | p.2 - p.1 ∈ W}.indicator (fun p ↦ f p.2) (t, s) ∂μ ∂μ := by
        refine lintegral_congr fun t ↦ ?_
        rw [← lintegral_indicator (measurable_sub_const t hW)]
        rfl
    _ = ∫⁻ s, ∫⁻ t, {p : G × G | p.2 - p.1 ∈ W}.indicator (fun p ↦ f p.2) (t, s) ∂μ ∂μ :=
        lintegral_lintegral_swap (hf.comp_snd.indicator hS)
    _ = ∫⁻ s, μ W * f s ∂μ := by
        refine lintegral_congr fun s ↦ ?_
        have h : (fun t ↦ {p : G × G | p.2 - p.1 ∈ W}.indicator (fun p ↦ f p.2) (t, s)) =
            ((fun t ↦ s - t) ⁻¹' W).indicator fun _ ↦ f s :=
          funext fun t ↦ indicator_eq_indicator (by simp only [mem_preimage, mem_ofPred_eq]) rfl
        have hmp : μ ((fun t ↦ s - t) ⁻¹' W) = μ W :=
          (μ.measurePreserving_sub_left s).measure_preimage (hW.nullMeasurableSet (μ := μ))
        rw [h, lintegral_indicator_const (measurable_const_sub s hW), hmp, mul_comm]
    _ = μ W * ∫⁻ s, f s ∂μ := lintegral_const_mul'' _ hf

omit [SFinite μ] [μ.IsAddLeftInvariant] [μ.IsNegInvariant] in
/-- The integral of `f` over the window `{s | s - t ∈ W}` is the convolution of `f` with the
indicator of `-W`, evaluated at `t`. -/
theorem setLIntegral_sub_preimage_eq_lconvolution (hW : MeasurableSet W) (f : G → ℝ≥0∞) (t : G) :
    ∫⁻ s in (fun s ↦ s - t) ⁻¹' W, f s ∂μ = (f ⋆ₗ[μ] (-W).indicator fun _ ↦ 1) t := by
  rw [lconvolution_def, ← lintegral_indicator (measurable_sub_const t hW)]
  refine lintegral_congr fun s ↦ ?_
  have h : -s + t ∈ -W ↔ s ∈ (fun s ↦ s - t) ⁻¹' W := by simp [neg_add_eq_sub]
  rw [indicator_eq_indicator (g := fun _ ↦ (1 : ℝ≥0∞)) h rfl, ← indicator_mul_right]
  simp only [mul_one]

/-- **The square-function bound over sliding windows.** The `L²` norms of `f` over the windows
`{s | s - t ∈ W}`, integrated against `g`, are at most `(μ W)^{1/2} ‖f‖₂ ‖g‖₂`. -/
theorem lintegral_rpow_setLIntegral_sub_preimage_mul_le (hW : MeasurableSet W) {f g : G → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ t, (∫⁻ s in (fun s ↦ s - t) ⁻¹' W, f s ^ (2 : ℝ) ∂μ) ^ (2⁻¹ : ℝ) * g t ∂μ ≤
      μ W ^ (2⁻¹ : ℝ) * eLpNorm f 2 μ * eLpNorm g 2 μ := by
  set φ := fun t ↦ (∫⁻ s in (fun s ↦ s - t) ⁻¹' W, f s ^ (2 : ℝ) ∂μ) ^ (2⁻¹ : ℝ)
  have hφ : Measurable φ :=
    (TauCeti.measurable_setLIntegral_of_measurableSet ((measurable_snd.sub measurable_fst) hW)
      (hf.pow_const _)).pow_const _
  have h2 : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hφ2 : ∫⁻ t, φ t ^ (2 : ℝ) ∂μ = μ W * ∫⁻ s, f s ^ (2 : ℝ) ∂μ := by
    simp only [φ, ENNReal.rpow_inv_rpow (two_ne_zero : (2 : ℝ) ≠ 0)]
    exact lintegral_setLIntegral_sub_preimage hW (hf.pow_const _)
  calc ∫⁻ t, φ t * g t ∂μ
      ≤ (∫⁻ t, φ t ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ t, g t ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq μ h2 hφ.aemeasurable hg
    _ = μ W ^ (2⁻¹ : ℝ) * eLpNorm f 2 μ * eLpNorm g 2 μ := by
        rw [hφ2, TauCeti.eLpNorm_eq_lintegral_rpow two_ne_zero ENNReal.ofNat_ne_top hf,
          TauCeti.eLpNorm_eq_lintegral_rpow two_ne_zero ENNReal.ofNat_ne_top hg,
          ENNReal.toReal_ofNat, one_div,
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2⁻¹)]

/-- **The window kernel on `L²`.** The integrals of `f` over the windows `{s | s - t ∈ W}`,
integrated against `g`, are at most `μ W ‖f‖₂ ‖g‖₂`. -/
theorem lintegral_setLIntegral_sub_preimage_mul_le (hW : MeasurableSet W) {f g : G → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ t, (∫⁻ s in (fun s ↦ s - t) ⁻¹' W, f s ∂μ) * g t ∂μ ≤
      μ W * eLpNorm f 2 μ * eLpNorm g 2 μ := by
  -- The window integrals are the convolution of `f` with the indicator of `-W`, so Young's
  -- inequality `L² ⋆ L¹ ⊆ L²` and Cauchy–Schwarz give the bound.
  set k : G → ℝ≥0∞ := (-W).indicator fun _ ↦ 1
  have hk : AEMeasurable k μ := (measurable_const.indicator hW.neg).aemeasurable
  have hkW : eLpNorm k 1 μ = μ W := by
    rw [eLpNorm_indicator_const hW.neg.nullMeasurableSet one_ne_zero ENNReal.one_ne_top,
      Measure.measure_neg]
    simp
  have hfk := aemeasurable_lconvolution hf hk
  calc ∫⁻ t, (∫⁻ s in (fun s ↦ s - t) ⁻¹' W, f s ∂μ) * g t ∂μ
      = ∫⁻ t, (f ⋆ₗ[μ] k) t * g t ∂μ := by
        simp only [setLIntegral_sub_preimage_eq_lconvolution hW, k]
    _ ≤ eLpNorm (f ⋆ₗ[μ] k) 2 μ * eLpNorm g 2 μ := by
        rw [TauCeti.eLpNorm_eq_lintegral_rpow two_ne_zero ENNReal.ofNat_ne_top hfk,
          TauCeti.eLpNorm_eq_lintegral_rpow two_ne_zero ENNReal.ofNat_ne_top hg,
          ENNReal.toReal_ofNat]
        exact ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hfk hg
    _ ≤ eLpNorm f 2 μ * eLpNorm k 1 μ * eLpNorm g 2 μ := by
        gcongr
        exact eLpNorm_lconvolution_le one_le_two le_rfl (by rw [inv_one, add_comm]) hf hk
    _ = μ W * eLpNorm f 2 μ * eLpNorm g 2 μ := by rw [hkW, mul_comm (eLpNorm f 2 μ)]

end MeasureTheory

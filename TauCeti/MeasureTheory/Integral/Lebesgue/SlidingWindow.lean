/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Prod

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

The window integral `t ↦ ∫_{s - t ∈ W} f(s) ds` is the convolution `1_{-W} ⋆ₗ f`
(`MeasureTheory.lconvolution`), and the window-kernel bound is the case `L¹ ⋆ L² ⊆ L²` of Young's
inequality combined with Cauchy–Schwarz; the statements here keep the windows explicit, which is
the form in which time-localized pairings arise.

## Main declarations

* `MeasureTheory.lintegral_setLIntegral_sub_preimage`: the sliding-window identity.
* `MeasureTheory.measurable_setLIntegral_sub_preimage`: the window integrals are measurable.
* `MeasureTheory.lintegral_rpow_setLIntegral_sub_preimage_mul_le`: the square-function bound.
* `MeasureTheory.lintegral_setLIntegral_sub_preimage_mul_le`: the bound for the window kernel.
-/

public section

open MeasureTheory Set Function
open scoped ENNReal

namespace MeasureTheory

variable {G : Type*} [MeasurableSpace G] [AddCommGroup G] [MeasurableAdd₂ G] [MeasurableNeg G]
  {μ : Measure G} [SFinite μ] [μ.IsAddLeftInvariant] [μ.IsNegInvariant] {W : Set G}

/-- **Sliding windows.** Integrating a nonnegative function over the translated windows
`{s | s - t ∈ W}` and then over `t` multiplies its integral by `μ W`. -/
theorem lintegral_setLIntegral_sub_preimage (hW : MeasurableSet W) {f : G → ℝ≥0∞}
    (hf : AEMeasurable f μ) :
    ∫⁻ t, ∫⁻ s in (fun s ↦ s - t) ⁻¹' W, f s ∂μ ∂μ = μ W * ∫⁻ s, f s ∂μ := by
  set g := hf.mk f
  have hg : Measurable g := hf.measurable_mk
  -- Replace `f` by its measurable modification `g` inside every window.
  have hfg (t : G) : ∫⁻ s in (fun s ↦ s - t) ⁻¹' W, f s ∂μ =
      ∫⁻ s in (fun s ↦ s - t) ⁻¹' W, g s ∂μ :=
    lintegral_congr_ae (ae_restrict_of_ae hf.ae_eq_mk)
  have hS : MeasurableSet {p : G × G | p.2 - p.1 ∈ W} :=
    (measurable_snd.sub measurable_fst) hW
  have hind (t s : G) : ((fun s ↦ s - t) ⁻¹' W).indicator g s =
      {p : G × G | p.2 - p.1 ∈ W}.indicator (fun p ↦ g p.2) (t, s) :=
    indicator_eq_indicator (by simp only [mem_preimage, mem_ofPred_eq]) rfl
  have hmeas : Measurable (uncurry fun t s ↦
      {p : G × G | p.2 - p.1 ∈ W}.indicator (fun p ↦ g p.2) (t, s)) :=
    (hg.comp measurable_snd).indicator hS
  calc ∫⁻ t, ∫⁻ s in (fun s ↦ s - t) ⁻¹' W, f s ∂μ ∂μ
      = ∫⁻ t, ∫⁻ s, {p : G × G | p.2 - p.1 ∈ W}.indicator (fun p ↦ g p.2) (t, s) ∂μ ∂μ := by
        refine lintegral_congr fun t ↦ ?_
        rw [hfg, ← lintegral_indicator (measurable_sub_const t hW)]
        exact lintegral_congr fun s ↦ hind t s
    _ = ∫⁻ s, ∫⁻ t, {p : G × G | p.2 - p.1 ∈ W}.indicator (fun p ↦ g p.2) (t, s) ∂μ ∂μ :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ s, μ W * g s ∂μ := by
        refine lintegral_congr fun s ↦ ?_
        have h : (fun t ↦ {p : G × G | p.2 - p.1 ∈ W}.indicator (fun p ↦ g p.2) (t, s)) =
            ((fun t ↦ s - t) ⁻¹' W).indicator fun _ ↦ g s :=
          funext fun t ↦ indicator_eq_indicator (by simp only [mem_preimage, mem_ofPred_eq]) rfl
        have hmp : μ ((fun t ↦ s - t) ⁻¹' W) = μ W :=
          (μ.measurePreserving_sub_left s).measure_preimage (hW.nullMeasurableSet (μ := μ))
        rw [h, lintegral_indicator_const (measurable_const_sub s hW), hmp, mul_comm]
    _ = μ W * ∫⁻ s, f s ∂μ := by
        rw [lintegral_const_mul _ hg, lintegral_congr_ae hf.ae_eq_mk.symm]

omit [μ.IsAddLeftInvariant] [μ.IsNegInvariant] in
/-- The integrals of `f` over the windows `{s | s - t ∈ W}` depend measurably on `t`. -/
theorem measurable_setLIntegral_sub_preimage (hW : MeasurableSet W) {f : G → ℝ≥0∞}
    (hf : AEMeasurable f μ) :
    Measurable fun t ↦ ∫⁻ s in (fun s ↦ s - t) ⁻¹' W, f s ∂μ := by
  have h (t : G) : ∫⁻ s in (fun s ↦ s - t) ⁻¹' W, f s ∂μ =
      ∫⁻ s, {p : G × G | p.2 - p.1 ∈ W}.indicator (fun p ↦ hf.mk f p.2) (t, s) ∂μ := by
    rw [← lintegral_indicator (measurable_sub_const t hW)]
    refine lintegral_congr_ae ?_
    filter_upwards [hf.ae_eq_mk] with s hs
    exact indicator_eq_indicator (by simp only [mem_preimage, mem_ofPred_eq]) hs
  simp only [h]
  exact Measurable.lintegral_prod_right'
    ((hf.measurable_mk.comp measurable_snd).indicator ((measurable_snd.sub measurable_fst) hW))

/-- **The square-function bound over sliding windows.** The `L²` norms of `f` over the windows
`{s | s - t ∈ W}`, integrated against `g`, are at most `(μ W)^{1/2} ‖f‖₂ ‖g‖₂`. -/
theorem lintegral_rpow_setLIntegral_sub_preimage_mul_le (hW : MeasurableSet W) {f g : G → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ t, (∫⁻ s in (fun s ↦ s - t) ⁻¹' W, f s ^ (2 : ℝ) ∂μ) ^ (2⁻¹ : ℝ) * g t ∂μ ≤
      μ W ^ (2⁻¹ : ℝ) * eLpNorm f 2 μ * eLpNorm g 2 μ := by
  set φ := fun t ↦ (∫⁻ s in (fun s ↦ s - t) ⁻¹' W, f s ^ (2 : ℝ) ∂μ) ^ (2⁻¹ : ℝ)
  have hφ : Measurable φ := (measurable_setLIntegral_sub_preimage hW (hf.pow_const _)).pow_const _
  have h2 : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hφ2 : ∫⁻ t, φ t ^ (2 : ℝ) ∂μ = μ W * ∫⁻ s, f s ^ (2 : ℝ) ∂μ := by
    simp only [φ, ENNReal.rpow_inv_rpow (two_ne_zero : (2 : ℝ) ≠ 0)]
    exact lintegral_setLIntegral_sub_preimage hW (hf.pow_const _)
  have hnorm (h : G → ℝ≥0∞) (hh : AEMeasurable h μ) :
      eLpNorm h 2 μ = (∫⁻ s, h s ^ (2 : ℝ) ∂μ) ^ (2⁻¹ : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      hh.aestronglyMeasurable]
    simp only [enorm_eq_self, ENNReal.toReal_ofNat, one_div]
  calc ∫⁻ t, φ t * g t ∂μ
      ≤ (∫⁻ t, φ t ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ t, g t ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq μ h2 hφ.aemeasurable hg
    _ = μ W ^ (2⁻¹ : ℝ) * eLpNorm f 2 μ * eLpNorm g 2 μ := by
        rw [hφ2, hnorm f hf, hnorm g hg, one_div,
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2⁻¹)]

/-- **The window kernel on `L²`.** The integrals of `f` over the windows `{s | s - t ∈ W}`,
integrated against `g`, are at most `μ W ‖f‖₂ ‖g‖₂`. -/
theorem lintegral_setLIntegral_sub_preimage_mul_le (hW : MeasurableSet W) {f g : G → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ t, (∫⁻ s in (fun s ↦ s - t) ⁻¹' W, f s ∂μ) * g t ∂μ ≤
      μ W * eLpNorm f 2 μ * eLpNorm g 2 μ := by
  -- On each window, Cauchy–Schwarz bounds the integral of `f` by `(μ W)^{1/2}` times its `L²`
  -- norm there.
  have hwin (t : G) : ∫⁻ s in (fun s ↦ s - t) ⁻¹' W, f s ∂μ ≤
      μ W ^ (2⁻¹ : ℝ) * (∫⁻ s in (fun s ↦ s - t) ⁻¹' W, f s ^ (2 : ℝ) ∂μ) ^ (2⁻¹ : ℝ) := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
      (μ := μ.restrict ((fun s ↦ s - t) ⁻¹' W)) one_le_two hf.restrict.aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_enorm hf.restrict.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
        hf.restrict.aestronglyMeasurable, Measure.restrict_apply_univ,
      (measurePreserving_sub_right μ t).measure_preimage hW.nullMeasurableSet] at h
    simp only [enorm_eq_self, ENNReal.toReal_one, ENNReal.toReal_ofNat] at h
    have hexp : (1 / 1 - 1 / 2 : ℝ) = 2⁻¹ := by norm_num
    rw [hexp, one_div, mul_comm] at h
    exact h
  calc ∫⁻ t, (∫⁻ s in (fun s ↦ s - t) ⁻¹' W, f s ∂μ) * g t ∂μ
      ≤ ∫⁻ t, μ W ^ (2⁻¹ : ℝ) *
          ((∫⁻ s in (fun s ↦ s - t) ⁻¹' W, f s ^ (2 : ℝ) ∂μ) ^ (2⁻¹ : ℝ) * g t) ∂μ :=
        lintegral_mono fun t ↦ by rw [← mul_assoc]; gcongr; exact hwin t
    _ = μ W ^ (2⁻¹ : ℝ) *
          ∫⁻ t, (∫⁻ s in (fun s ↦ s - t) ⁻¹' W, f s ^ (2 : ℝ) ∂μ) ^ (2⁻¹ : ℝ) * g t ∂μ :=
        lintegral_const_mul'' _
          (((measurable_setLIntegral_sub_preimage hW (hf.pow_const _)).pow_const _).aemeasurable.mul
            hg)
    _ ≤ μ W ^ (2⁻¹ : ℝ) * (μ W ^ (2⁻¹ : ℝ) * eLpNorm f 2 μ * eLpNorm g 2 μ) := by
        gcongr
        exact lintegral_rpow_setLIntegral_sub_preimage_mul_le hW hf hg
    _ = μ W * eLpNorm f 2 μ * eLpNorm g 2 μ := by
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num)
          (by norm_num)]
        norm_num

end MeasureTheory

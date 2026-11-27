/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Analysis.InnerProductSpace.Harmonic.MeanValue.Basic
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.Lebesgue.ReProdIm

/-!
# Hardy spaces of the upper half-plane

For `0 < p < ∞`, the **Hardy space** `H^p(ℂ₊)` consists of the holomorphic functions `F` on the
upper half-plane `ℂ₊` with
`‖F‖_p = sup_{y > 0} ‖F(· + iy)‖_{L^p(ℝ)} < ∞`
(`TauCeti.upperHalfPlaneHardyNorm`, `TauCeti.MemUpperHalfPlaneHardy`); `H²(ℂ₊)` is the case
`p = 2`.

## Main results

* `TauCeti.lintegral_rpow_eNorm_le_upperHalfPlaneHardyNorm_rpow`: on every horizontal line
  `Im z = y > 0`, `∫ |F(x + iy)|^p dx ≤ ‖F‖_p^p`.
* `TauCeti.MemUpperHalfPlaneHardy.rpow_norm_le`: the **point bound**
  `|F(z)|^p ≤ 2 ‖F‖_p^p / (π Im z)` for `F ∈ H^p(ℂ₊)`, `1 ≤ p < ∞` and `z ∈ ℂ₊`.
* `TauCeti.not_memUpperHalfPlaneHardy_const`: a nonzero constant is in no `H^p(ℂ₊)`, `0 < p < ∞`.

The point bound: for `0 < r < Im z`, the mean-value property of the harmonic function `F` on the
disc `D(z, r)` (`InnerProductSpace.HarmonicOnNhd.setAverage_ball_eq`) and Hölder's bound on an
average (`TauCeti.enorm_setAverage_rpow_le`) bound `|F(z)|^p` by the mean of `|F|^p` over the
disc. The disc lies in the strip `|Im w - Im z| < r`, on which Tonelli's theorem bounds the
integral of `|F|^p` by `2r ‖F‖_p^p` (`TauCeti.setLIntegral_reProdIm_le`). So
`|F(z)|^p ≤ 2 ‖F‖_p^p / (π r)`; let `r → Im z`.

## References

* L. Mauth, *On pointwise convergence of the non-linear Fourier transform*, arXiv:2210.12286,
  Lemma 2.
-/

public section

noncomputable section

open Complex MeasureTheory Filter Metric Set Topology
open scoped Real ENNReal
open UpperHalfPlane (upperHalfPlaneSet)

namespace TauCeti

/-! ### The Hardy norm -/

/-- The **Hardy norm** `‖F‖_p = sup_{y > 0} ‖F(· + iy)‖_{L^p(ℝ)}` of `F : ℂ → ℂ` on the upper
half-plane, with values in `[0, ∞]`. -/
def upperHalfPlaneHardyNorm (p : ℝ≥0∞) (F : ℂ → ℂ) : ℝ≥0∞ :=
  ⨆ (y : ℝ) (_ : 0 < y), eLpNorm (fun x : ℝ ↦ F (x + y * I)) p

/-- The defining formula of `TauCeti.upperHalfPlaneHardyNorm`. -/
theorem upperHalfPlaneHardyNorm_def (p : ℝ≥0∞) (F : ℂ → ℂ) :
    upperHalfPlaneHardyNorm p F = ⨆ (y : ℝ) (_ : 0 < y), eLpNorm (fun x : ℝ ↦ F (x + y * I)) p :=
  (rfl)

/-- The **Hardy space** `H^p(ℂ₊)`: `F` is holomorphic on the upper half-plane and its Hardy norm
`sup_{y > 0} ‖F(· + iy)‖_{L^p(ℝ)}` is finite. -/
def MemUpperHalfPlaneHardy (p : ℝ≥0∞) (F : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ F upperHalfPlaneSet ∧ upperHalfPlaneHardyNorm p F < ∞

/-- The defining formula of `TauCeti.MemUpperHalfPlaneHardy`. -/
theorem memUpperHalfPlaneHardy_iff (p : ℝ≥0∞) (F : ℂ → ℂ) :
    MemUpperHalfPlaneHardy p F ↔
      DifferentiableOn ℂ F upperHalfPlaneSet ∧ upperHalfPlaneHardyNorm p F < ∞ :=
  Iff.rfl

variable {p : ℝ≥0∞} {F : ℂ → ℂ}

/-- A function in `H^p(ℂ₊)` is holomorphic on the upper half-plane. -/
theorem MemUpperHalfPlaneHardy.differentiableOn (hF : MemUpperHalfPlaneHardy p F) :
    DifferentiableOn ℂ F upperHalfPlaneSet :=
  hF.1

/-- A function in `H^p(ℂ₊)` has finite Hardy norm. -/
theorem MemUpperHalfPlaneHardy.upperHalfPlaneHardyNorm_lt_top (hF : MemUpperHalfPlaneHardy p F) :
    upperHalfPlaneHardyNorm p F < ∞ :=
  hF.2

/-- The `L^p` norm of `F` on each horizontal line in `ℂ₊` is at most the Hardy norm. -/
theorem eLpNorm_le_upperHalfPlaneHardyNorm (p : ℝ≥0∞) {y : ℝ} (hy : 0 < y) :
    eLpNorm (fun x : ℝ ↦ F (x + y * I)) p ≤ upperHalfPlaneHardyNorm p F :=
  le_iSup₂ (f := fun (y : ℝ) (_ : 0 < y) ↦ eLpNorm (fun x : ℝ ↦ F (x + y * I)) p) y hy

/-- The Hardy norm is at most `C` iff the `L^p` norm of `F` on every horizontal line in `ℂ₊` is. -/
theorem upperHalfPlaneHardyNorm_le_iff {C : ℝ≥0∞} :
    upperHalfPlaneHardyNorm p F ≤ C ↔ ∀ y : ℝ, 0 < y → eLpNorm (fun x : ℝ ↦ F (x + y * I)) p ≤ C :=
  iSup₂_le_iff

/-- A function holomorphic on `ℂ₊` whose `L^p` norms on the horizontal lines in `ℂ₊` are bounded
by a finite `C` is in `H^p(ℂ₊)`. -/
theorem MemUpperHalfPlaneHardy.of_eLpNorm_le (hF : DifferentiableOn ℂ F upperHalfPlaneSet)
    {C : ℝ≥0∞} (hC : C < ∞) (h : ∀ y : ℝ, 0 < y → eLpNorm (fun x : ℝ ↦ F (x + y * I)) p ≤ C) :
    MemUpperHalfPlaneHardy p F :=
  ⟨hF, (upperHalfPlaneHardyNorm_le_iff.2 h).trans_lt hC⟩

/-- The Hardy norm depends only on the values of `F` on the upper half-plane. -/
theorem upperHalfPlaneHardyNorm_congr {G : ℂ → ℂ} (h : EqOn F G upperHalfPlaneSet) :
    upperHalfPlaneHardyNorm p F = upperHalfPlaneHardyNorm p G := by
  simp only [upperHalfPlaneHardyNorm_def]
  refine iSup_congr fun y ↦ iSup_congr fun hy ↦
    congrArg (fun g : ℝ → ℂ ↦ eLpNorm g p) (funext fun x ↦ h ?_)
  simpa using hy

/-- Membership in `H^p(ℂ₊)` depends only on the values of `F` on the upper half-plane. -/
theorem MemUpperHalfPlaneHardy.congr {G : ℂ → ℂ} (hF : MemUpperHalfPlaneHardy p F)
    (h : EqOn F G upperHalfPlaneSet) : MemUpperHalfPlaneHardy p G :=
  ⟨hF.differentiableOn.congr fun _ hz ↦ (h hz).symm,
    upperHalfPlaneHardyNorm_congr h ▸ hF.upperHalfPlaneHardyNorm_lt_top⟩

/-- Functions agreeing on the upper half-plane are in `H^p(ℂ₊)` together. -/
theorem memUpperHalfPlaneHardy_congr {G : ℂ → ℂ} (h : EqOn F G upperHalfPlaneSet) :
    MemUpperHalfPlaneHardy p F ↔ MemUpperHalfPlaneHardy p G :=
  ⟨fun hF ↦ hF.congr h, fun hG ↦ hG.congr h.symm⟩

/-- The Hardy norm of the zero function is zero. -/
@[simp]
theorem upperHalfPlaneHardyNorm_zero (p : ℝ≥0∞) : upperHalfPlaneHardyNorm p 0 = 0 :=
  le_antisymm (upperHalfPlaneHardyNorm_le_iff.2 fun _ _ ↦ by simp) bot_le

/-- The zero function is in `H^p(ℂ₊)`. -/
theorem memUpperHalfPlaneHardy_zero (p : ℝ≥0∞) : MemUpperHalfPlaneHardy p 0 :=
  ⟨differentiableOn_const 0, by simp⟩

/-- On every horizontal line `Im z = y > 0`, `∫ |F(x + iy)|^p dx ≤ ‖F‖_p^p`. -/
theorem lintegral_rpow_eNorm_le_upperHalfPlaneHardyNorm_rpow {p : ℝ} (hp : 0 < p) {y : ℝ}
    (hy : 0 < y) :
    ∫⁻ x : ℝ, ‖F (x + y * I)‖ₑ ^ p ≤ upperHalfPlaneHardyNorm (ENNReal.ofReal p) F ^ p := by
  have h := eLpNorm_le_upperHalfPlaneHardyNorm (F := F) (ENNReal.ofReal p) hy
  by_cases hm : AEStronglyMeasurable fun x : ℝ ↦ F (x + y * I)
  · rw [eLpNorm_eq_eLpNorm' (by simpa using hp) ENNReal.ofReal_ne_top hm,
      ENNReal.toReal_ofReal hp.le] at h
    rw [lintegral_rpow_eNorm_eq_rpow_eLpNorm' hp]
    exact ENNReal.rpow_le_rpow h hp.le
  · -- off the measurable functions, the `L^p` norm and hence the Hardy norm are infinite
    rw [eLpNorm_of_not_aestronglyMeasurable hm, top_le_iff] at h
    simp [h, ENNReal.top_rpow_of_pos hp]

/-! ### The point bound -/

/-- The point bound at a radius: for `0 < r < Im z`, `|F(z)|^p ≤ 2 ‖F‖_p^p / (π r)`. -/
private theorem rpow_norm_le_of_lt {p : ℝ} (hp : 1 ≤ p)
    (hF : MemUpperHalfPlaneHardy (ENNReal.ofReal p) F) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hrz : r < z.im) :
    ‖F z‖ ^ p ≤
      2 * (upperHalfPlaneHardyNorm (ENNReal.ofReal p) F).toReal ^ p / (π * r) := by
  have hp0 : 0 < p := by linarith
  set H := upperHalfPlaneHardyNorm (ENNReal.ofReal p) F
  -- the closed disc lies in the half-plane, and the open disc in the strip `|Im w - Im z| < r`
  have hball : closedBall z r ⊆ upperHalfPlaneSet := fun w hw ↦ by
    have : |w.im - z.im| ≤ r := (abs_im_le_norm (w - z)).trans (by simpa [dist_eq_norm] using hw)
    rw [UpperHalfPlane.upperHalfPlaneSet, mem_ofPred_eq]
    linarith [abs_le.1 this]
  have hballS : ball z r ⊆ univ ×ℂ Ioo (z.im - r) (z.im + r) := fun w hw ↦ by
    have : |w.im - z.im| < r := (abs_im_le_norm (w - z)).trans_lt (by simpa [dist_eq_norm] using hw)
    exact ⟨trivial, by linarith [abs_lt.1 this], by linarith [abs_lt.1 this]⟩
  -- the mean-value property
  have hharm : InnerProductSpace.HarmonicOnNhd F (closedBall z r) := fun w hw ↦
    (hF.differentiableOn.analyticAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (hball hw))).harmonicAt
  -- Hölder on the disc, then Tonelli on the strip
  have h : ‖F z‖ₑ ^ p ≤ (volume (ball z r))⁻¹ * (ENNReal.ofReal (2 * r) * H ^ p) := calc
    ‖F z‖ₑ ^ p = ‖⨍ w in ball z r, F w‖ₑ ^ p := by
      rw [InnerProductSpace.HarmonicOnNhd.setAverage_ball_eq hharm hr]
    _ ≤ (volume (ball z r))⁻¹ * ∫⁻ w in ball z r, ‖F w‖ₑ ^ p := enorm_setAverage_rpow_le hp
    _ ≤ (volume (ball z r))⁻¹ * ∫⁻ w in univ ×ℂ Ioo (z.im - r) (z.im + r), ‖F w‖ₑ ^ p := by
      gcongr
    _ ≤ (volume (ball z r))⁻¹ * (ENNReal.ofReal (2 * r) * H ^ p) := by
      gcongr
      refine (setLIntegral_reProdIm_le (C := H ^ p) fun y hy ↦ ?_).trans_eq ?_
      · rw [Measure.restrict_univ]
        exact lintegral_rpow_eNorm_le_upperHalfPlaneHardyNorm_rpow hp0 (by linarith [hy.1])
      · rw [Real.volume_Ioo]
        ring_nf
  have hfin : (volume (ball z r))⁻¹ * (ENNReal.ofReal (2 * r) * H ^ p) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (measure_ball_pos volume z hr).ne')
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.rpow_ne_top_of_nonneg hp0.le hF.upperHalfPlaneHardyNorm_lt_top.ne))
  have := ENNReal.toReal_mono hfin h
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le,
    ENNReal.toReal_ofReal (by positivity)] at this
  refine this.trans_eq ?_
  simp only [Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr.le, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * r),
    ENNReal.coe_toReal, NNReal.coe_real_pi, ENNReal.toReal_rpow]
  field_simp

/-- **The point bound in `H^p(ℂ₊)`.** For `1 ≤ p < ∞`, `F ∈ H^p(ℂ₊)` and `z ∈ ℂ₊`,
`|F(z)|^p ≤ 2 ‖F‖_p^p / (π Im z)`. -/
theorem MemUpperHalfPlaneHardy.rpow_norm_le {p : ℝ} (hp : 1 ≤ p)
    (hF : MemUpperHalfPlaneHardy (ENNReal.ofReal p) F) {z : ℂ} (hz : 0 < z.im) :
    ‖F z‖ ^ p ≤
      2 * (upperHalfPlaneHardyNorm (ENNReal.ofReal p) F).toReal ^ p / (π * z.im) := by
  set c := 2 * (upperHalfPlaneHardyNorm (ENNReal.ofReal p) F).toReal ^ p
  have hlim : Tendsto (fun r ↦ c / (π * r)) (𝓝[<] z.im) (𝓝 (c / (π * z.im))) :=
    ((continuousAt_const.div (continuousAt_const.mul continuousAt_id)
      (mul_pos Real.pi_pos hz).ne').tendsto).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT hz] with r hr
  exact rpow_norm_le_of_lt hp hF hr.1 hr.2

/-! ### Checks -/

/-- **A nonzero constant is not in `H^p(ℂ₊)`** for `0 < p < ∞`: its `L^p` norm on every horizontal
line is infinite. -/
theorem not_memUpperHalfPlaneHardy_const {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) {c : ℂ}
    (hc : c ≠ 0) : ¬ MemUpperHalfPlaneHardy p (fun _ ↦ c) := by
  rintro ⟨-, hlt⟩
  have h := eLpNorm_le_upperHalfPlaneHardyNorm (F := fun _ ↦ c) p one_pos
  rw [eLpNorm_const c hp0 (Measure.measure_univ_pos.1 (by simp)), Real.volume_univ,
    ENNReal.top_rpow_of_pos (by simpa using ENNReal.toReal_pos hp0 hp),
    ENNReal.mul_top (by simpa using hc)] at h
  exact (top_le_iff.1 h ▸ hlt).ne rfl

end TauCeti

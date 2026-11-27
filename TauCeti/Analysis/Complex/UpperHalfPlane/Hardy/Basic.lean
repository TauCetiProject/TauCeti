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
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Analysis.InnerProductSpace.Harmonic.MeanValue.Basic

/-!
# Hardy spaces of the upper half-plane

For `0 < p < ∞`, the **Hardy space** `H^p(ℂ₊)` consists of the holomorphic functions `F` on the
upper half-plane `ℂ₊` with
`‖F‖_p = sup_{y > 0} ‖F(· + iy)‖_{L^p(ℝ)} < ∞`
(`TauCeti.upperHalfPlaneHardyNorm`, `TauCeti.MemUpperHalfPlaneHardy`); `H²(ℂ₊)` is the case
`p = 2`.

## Main results

* `TauCeti.lintegral_enorm_rpow_le_upperHalfPlaneHardyNorm`: on every horizontal line
  `Im z = y > 0`, `∫ |F(x + iy)|^p dx ≤ ‖F‖_p^p`.
* `TauCeti.MemUpperHalfPlaneHardy.rpow_norm_le`: the **point bound**
  `|F(z)|^p ≤ 2 ‖F‖_p^p / (π Im z)` for `F ∈ H^p(ℂ₊)`, `1 ≤ p < ∞` and `z ∈ ℂ₊`.
* `TauCeti.not_memUpperHalfPlaneHardy_const`: a nonzero constant is in no `H^p(ℂ₊)`, `p < ∞`.

The point bound: for `0 < r < Im z`, the mean-value property of the harmonic function `F` on the
disc `D(z, r)` (`InnerProductSpace.HarmonicOnNhd.setAverage_ball_eq`) and Jensen's inequality for
the convex function `t ↦ t^p` bound `|F(z)|^p` by the mean of `|F|^p` over the disc. The disc lies
in the strip `|Im w - Im z| < r`, on which Tonelli's theorem bounds the integral of `|F|^p` by
`2r ‖F‖_p^p` (`TauCeti.setLIntegral_im_mem_Ioo_le`). So `|F(z)|^p ≤ 2 ‖F‖_p^p / (π r)`; let
`r → Im z`.

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

variable {F : ℂ → ℂ}

/-- The `L^p` norm of `F` on each horizontal line in `ℂ₊` is at most the Hardy norm. -/
theorem eLpNorm_le_upperHalfPlaneHardyNorm (p : ℝ≥0∞) {y : ℝ} (hy : 0 < y) :
    eLpNorm (fun x : ℝ ↦ F (x + y * I)) p ≤ upperHalfPlaneHardyNorm p F :=
  le_iSup₂ (f := fun (y : ℝ) (_ : 0 < y) ↦ eLpNorm (fun x : ℝ ↦ F (x + y * I)) p) y hy

/-- A holomorphic function on `ℂ₊` is continuous on each horizontal line in `ℂ₊`. -/
theorem continuous_comp_add_mul_I (hF : DifferentiableOn ℂ F upperHalfPlaneSet) {y : ℝ}
    (hy : 0 < y) : Continuous fun x : ℝ ↦ F (x + y * I) :=
  hF.continuousOn.comp_continuous (by fun_prop) fun x ↦ show 0 < (x + y * I : ℂ).im by simpa

/-- On every horizontal line `Im z = y > 0`, `∫ |F(x + iy)|^p dx ≤ ‖F‖_p^p`. -/
theorem lintegral_enorm_rpow_le_upperHalfPlaneHardyNorm
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) {p : ℝ} (hp : 0 < p) {y : ℝ} (hy : 0 < y) :
    ∫⁻ x : ℝ, ‖F (x + y * I)‖ₑ ^ p ≤ upperHalfPlaneHardyNorm (ENNReal.ofReal p) F ^ p := by
  have h := eLpNorm_le_upperHalfPlaneHardyNorm (F := F) (ENNReal.ofReal p) hy
  rw [eLpNorm_eq_eLpNorm' (by simpa using hp) ENNReal.ofReal_ne_top
    (continuous_comp_add_mul_I hF hy).aestronglyMeasurable, ENNReal.toReal_ofReal hp.le] at h
  rw [lintegral_rpow_eNorm_eq_rpow_eLpNorm' hp]
  exact ENNReal.rpow_le_rpow h hp.le

/-! ### Integrals over horizontal strips -/

/-- **Tonelli on a horizontal strip.** If `g` is measurable and `∫ g(x + iy) dx ≤ C` for every
`y ∈ (a, b)`, then the integral of `g` over the strip `a < Im w < b` is at most `(b - a) C`. -/
theorem setLIntegral_im_mem_Ioo_le {g : ℂ → ℝ≥0∞} (hg : Measurable g) {a b : ℝ} {C : ℝ≥0∞}
    (hC : ∀ y ∈ Ioo a b, ∫⁻ x : ℝ, g (x + y * I) ≤ C) :
    ∫⁻ w in {w : ℂ | w.im ∈ Ioo a b}, g w ≤ ENNReal.ofReal (b - a) * C := by
  have hS : MeasurableSet {w : ℂ | w.im ∈ Ioo a b} := measurableSet_Ioo.preimage measurable_im
  set G := {w : ℂ | w.im ∈ Ioo a b}.indicator g
  have hG : Measurable G := hg.indicator hS
  have he := volume_preserving_equiv_real_prod.symm
  have hGm : Measurable fun q : ℝ × ℝ ↦ G (measurableEquivRealProd.symm q) :=
    hG.comp measurableEquivRealProd.symm.measurable
  rw [← lintegral_indicator hS, ← he.lintegral_comp_emb
    measurableEquivRealProd.symm.measurableEmbedding, Measure.volume_eq_prod,
    lintegral_prod _ hGm.aemeasurable, lintegral_lintegral_swap hGm.aemeasurable]
  have hpt (y x : ℝ) : G (measurableEquivRealProd.symm (x, y)) =
      (Ioo a b).indicator (fun y ↦ g (x + y * I)) y := by
    simp only [G, measurableEquivRealProd_symm_apply, indicator, mem_ofPred_eq]
    simp only [mk_eq_add_mul_I]
  simp_rw [hpt]
  calc ∫⁻ y, ∫⁻ x : ℝ, (Ioo a b).indicator (fun y ↦ g (x + y * I)) y
      = ∫⁻ y, (Ioo a b).indicator (fun y ↦ ∫⁻ x : ℝ, g (x + y * I)) y := by
        congr 1
        ext y
        by_cases hy : y ∈ Ioo a b <;> simp [indicator, hy]
    _ = ∫⁻ y in Ioo a b, ∫⁻ x : ℝ, g (x + y * I) := lintegral_indicator measurableSet_Ioo _
    _ ≤ ∫⁻ _ in Ioo a b, C := setLIntegral_mono_ae (by simp) (.of_forall hC)
    _ = ENNReal.ofReal (b - a) * C := by rw [setLIntegral_const, Real.volume_Ioo, mul_comm]

/-! ### The point bound -/

/-- The point bound at a radius: for `0 < r < Im z`, `|F(z)|^p ≤ 2 ‖F‖_p^p / (π r)`. -/
private theorem rpow_norm_le_of_lt {p : ℝ} (hp : 1 ≤ p)
    (hF : MemUpperHalfPlaneHardy (ENNReal.ofReal p) F) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hrz : r < z.im) :
    ‖F z‖ ^ p ≤
      2 * (upperHalfPlaneHardyNorm (ENNReal.ofReal p) F).toReal ^ p / (π * r) := by
  have hp0 : 0 < p := by linarith
  set H := upperHalfPlaneHardyNorm (ENNReal.ofReal p) F
  have hH : H ≠ ∞ := hF.2.ne
  -- the closed disc lies in the half-plane
  have hball : closedBall z r ⊆ upperHalfPlaneSet := fun w hw ↦ by
    have : |w.im - z.im| ≤ r := (abs_im_le_norm (w - z)).trans (by simpa [dist_eq_norm] using hw)
    change 0 < w.im
    linarith [abs_le.1 this]
  have hcont : ContinuousOn F (closedBall z r) := hF.1.continuousOn.mono hball
  -- the mean-value property
  have hharm : InnerProductSpace.HarmonicOnNhd F (closedBall z r) := fun w hw ↦
    (hF.1.analyticAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (hball hw))).harmonicAt
  have hmean : ⨍ w in ball z r, F w = F z :=
    InnerProductSpace.HarmonicOnNhd.setAverage_ball_eq hharm hr
  have hvol : volume.real (ball z r) = π * r ^ 2 := by
    rw [measureReal_def, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hr.le, ENNReal.coe_toReal, NNReal.coe_real_pi, mul_comm]
  have hvol0 : volume (ball z r) ≠ 0 := (measure_ball_pos volume z hr).ne'
  have hvoltop : volume (ball z r) ≠ ∞ := measure_ball_lt_top.ne
  have hint : IntegrableOn F (ball z r) :=
    (hcont.integrableOn_compact (isCompact_closedBall z r)).mono_set ball_subset_closedBall
  have hintp : IntegrableOn (fun w ↦ ‖F w‖ ^ p) (ball z r) :=
    ((hcont.norm.rpow_const fun _ _ ↦ Or.inr hp0.le).integrableOn_compact
      (isCompact_closedBall z r)).mono_set ball_subset_closedBall
  -- `|F(z)| ≤ ⨍ |F|`
  have h1 : ‖F z‖ ≤ ⨍ w in ball z r, ‖F w‖ := by
    rw [← hmean, setAverage_eq, setAverage_eq, norm_smul, Real.norm_of_nonneg (by positivity),
      smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
  -- Jensen: `(⨍ |F|)^p ≤ ⨍ |F|^p`
  have h2 : (⨍ w in ball z r, ‖F w‖) ^ p ≤ ⨍ w in ball z r, ‖F w‖ ^ p :=
    (convexOn_rpow hp).map_set_average_le (continuousOn_id.rpow_const fun _ _ ↦ Or.inr hp0.le)
      isClosed_Ici hvol0 hvoltop (.of_forall fun _ ↦ norm_nonneg _) hint.norm hintp
  -- the integral over the disc, bounded by the integral over the strip
  set S := {w : ℂ | w.im ∈ Ioo (z.im - r) (z.im + r)}
  have hSopen : IsOpen S := isOpen_Ioo.preimage continuous_im
  have hSsub : S ⊆ upperHalfPlaneSet := fun w hw ↦ show 0 < w.im by linarith [hw.1]
  classical
  set F' : ℂ → ℂ := S.piecewise F 0
  have hF'm : Measurable F' :=
    (hF.1.continuousOn.mono hSsub).measurable_piecewise continuousOn_const hSopen.measurableSet
  have hballS : ball z r ⊆ S := fun w hw ↦ by
    have : |w.im - z.im| < r := (abs_im_le_norm (w - z)).trans_lt (by simpa [dist_eq_norm] using hw)
    exact ⟨by linarith [abs_lt.1 this], by linarith [abs_lt.1 this]⟩
  have hstrip := setLIntegral_im_mem_Ioo_le (a := z.im - r) (b := z.im + r)
    (g := fun w ↦ ‖F' w‖ₑ ^ p)
    (hF'm.eNorm.pow_const p) (C := H ^ p) fun y hy ↦ by
      have hy0 : 0 < y := by linarith [hy.1]
      have hmem (x : ℝ) : (x + y * I : ℂ) ∈ S := by simpa [S] using hy
      simp only [F', Set.piecewise_eq_of_mem _ _ _ (hmem _)]
      exact lintegral_enorm_rpow_le_upperHalfPlaneHardyNorm hF.1 hp0 hy0
  have h3 : ∫ w in ball z r, ‖F w‖ ^ p ≤ 2 * r * H.toReal ^ p := by
    have hle : ENNReal.ofReal (∫ w in ball z r, ‖F w‖ ^ p) ≤ ENNReal.ofReal (2 * r) * H ^ p := by
      rw [ofReal_integral_eq_lintegral_ofReal hintp (.of_forall fun _ ↦ by positivity)]
      calc ∫⁻ w in ball z r, ENNReal.ofReal (‖F w‖ ^ p)
          = ∫⁻ w in ball z r, ‖F' w‖ₑ ^ p := by
            refine setLIntegral_congr_fun measurableSet_ball fun w hw ↦ ?_
            rw [show F' w = F w from Set.piecewise_eq_of_mem _ _ _ (hballS hw),
              ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
        _ ≤ ∫⁻ w in S, ‖F' w‖ₑ ^ p := lintegral_mono_set hballS
        _ ≤ ENNReal.ofReal (2 * r) * H ^ p := by
            convert hstrip using 3
            ring
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hp0.le hH)) hle
    rwa [ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_ball fun _ _ ↦ by positivity),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ← ENNReal.toReal_rpow] at this
  calc ‖F z‖ ^ p ≤ (⨍ w in ball z r, ‖F w‖) ^ p :=
        Real.rpow_le_rpow (norm_nonneg _) h1 hp0.le
    _ ≤ ⨍ w in ball z r, ‖F w‖ ^ p := h2
    _ = (π * r ^ 2)⁻¹ * ∫ w in ball z r, ‖F w‖ ^ p := by rw [setAverage_eq, hvol, smul_eq_mul]
    _ ≤ (π * r ^ 2)⁻¹ * (2 * r * H.toReal ^ p) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 2 * H.toReal ^ p / (π * r) := by
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

/-- **A nonzero constant is not in `H^p(ℂ₊)`** for `p < ∞`: its `L^p` norm on every horizontal line
is infinite. -/
theorem not_memUpperHalfPlaneHardy_const {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) {c : ℂ}
    (hc : c ≠ 0) : ¬ MemUpperHalfPlaneHardy p (fun _ ↦ c) := by
  rintro ⟨-, hlt⟩
  have h := eLpNorm_le_upperHalfPlaneHardyNorm (F := fun _ ↦ c) p one_pos
  rw [eLpNorm_const c hp0 (Measure.measure_univ_pos.1 (by simp)), Real.volume_univ,
    ENNReal.top_rpow_of_pos (by simpa using ENNReal.toReal_pos hp0 hp),
    ENNReal.mul_top (by simpa using hc)] at h
  exact (top_le_iff.1 h ▸ hlt).ne rfl

end TauCeti

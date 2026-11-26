/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.EMetricSpace.BoundedVariation

import TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.SineIntegral
import TauCeti.Analysis.Fourier.Inversion
import TauCeti.Analysis.Fourier.RiemannLebesgue
import TauCeti.MeasureTheory.Integral.IntervalIntegral.BoundedVariation

/-!
# Dirichlet–Jordan Fourier inversion

Symmetric truncations of the inverse Fourier integral converge to the mean of the one-sided
limits at a point where the original function is locally of bounded variation. The finite sinc
kernel formula reduces the proof to one-sided integrals. Near the origin, Jordan decomposition
and the second mean value theorem bound the error by the local variation times a uniform bound
for the sinc primitive. Away from the origin, the Riemann–Lebesgue lemma gives convergence.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, §5.1.
-/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal FourierTransform

local notation "𝒦" => (fun (T x : ℝ) ↦ 2 * T * Real.sinc (2 * Real.pi * T * x))

private theorem integral_sincKernel (T a b : ℝ) :
    ∫ x in a..b, 𝒦 T x = Real.pi⁻¹ *
      ∫ x in (2 * Real.pi * T * a)..(2 * Real.pi * T * b), Real.sinc x := by
  rw [← intervalIntegral.smul_integral_comp_mul_left]
  simp only [smul_eq_mul]
  simp only [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  field_simp [Real.pi_ne_zero]

private theorem tendsto_integral_sincKernel {d : ℝ} (hd : 0 < d) :
    Tendsto (fun T : ℝ ↦ ∫ x in 0..d, 𝒦 T x) atTop (𝓝 (1 / 2)) := by
  have h := (TauCeti.Contour.tendsto_integral_sinc_atTop.comp
    (tendsto_id.const_mul_atTop (show 0 < 2 * Real.pi * d by positivity))).const_mul Real.pi⁻¹
  convert h using 1
  · ext T
    rw [integral_sincKernel]
    dsimp
    rw [mul_zero]
    ring_nf
  · field_simp [Real.pi_ne_zero]

private theorem integrableOn_sincKernel_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {s : Set ℝ} (hf : IntegrableOn f s) (T : ℝ) :
    IntegrableOn (fun x ↦ 𝒦 T x • f x) s := by
  refine hf.bdd_smul (2 * |T|) (by fun_prop) (.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_sinc_le_one _)

private theorem tendsto_setIntegral_sincKernel_Ioi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℝ → E} {d : ℝ} (hd : 0 < d) (hf : IntegrableOn f (Ioi d)) :
    Tendsto (fun T : ℝ ↦ ∫ x in Ioi d, 𝒦 T x • f x) atTop (𝓝 0) := by
  have hq : IntegrableOn (fun x ↦ ((Real.pi * x)⁻¹ : ℝ) • f x) (Ioi d) := by
    refine hf.bdd_smul (φ := fun x ↦ (Real.pi * x)⁻¹) (Real.pi * d)⁻¹ (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx₀ : 0 < x := hd.trans hx
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ (Real.pi * x)⁻¹)]
    exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hx.le Real.pi_pos.le)
  have H := ((integrable_indicator_iff measurableSet_Ioi).2 hq).tendsto_integral_sin_smul_atTop
  refine H.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Ioi d
  · have hx₀ : 0 < x := hd.trans hx
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Complex.coe_smul, smul_smul,
      Real.sinc_of_ne_zero (by positivity : 2 * Real.pi * T * x ≠ 0)]
    congr 1
    field_simp
  · simp [hx]

private theorem norm_integral_sincKernel_le {M : ℝ}
    (hM : ∀ z : ℝ, ‖∫ x in 0..z, Real.sinc x‖ ≤ M) (T a b : ℝ) :
    ‖∫ x in a..b, 𝒦 T x‖ ≤ 2 * M / Real.pi := by
  rw [integral_sincKernel, norm_mul, norm_inv, Real.norm_of_nonneg Real.pi_pos.le]
  have hi (a b : ℝ) : IntervalIntegrable Real.sinc volume a b :=
    Real.continuous_sinc.intervalIntegrable _ _
  rw [← intervalIntegral.integral_interval_sub_left (hi 0 _) (hi 0 _)]
  calc
    _ ≤ Real.pi⁻¹ * (M + M) :=
      mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add (hM _) (hM _)))
        (inv_nonneg.mpr Real.pi_pos.le)
    _ = _ := by ring

private theorem exists_norm_integral_sincKernel_sub_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {r ε : ℝ} (hr : 0 < r) (hv : BoundedVariationOn f (Icc 0 r))
    (hg : EqOn g f (Ioi 0)) (hgc : ContinuousWithinAt g (Ici 0) 0) (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ ∀ T : ℝ, ‖∫ x in 0..d, 𝒦 T x • (g x - g 0)‖ < ε / 3 := by
  obtain ⟨M, hM₀, hM⟩ := Real.exists_norm_integral_sinc_le
  let C := 2 * M / Real.pi
  have hC : 0 ≤ C := div_nonneg (mul_nonneg (by norm_num) hM₀) Real.pi_pos.le
  have hV := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp
    (hv.tendsto_eVariationOn_Ioc_zero 0)
  have hC₁ : 0 < 3 * (C + 1) :=
    mul_pos (by norm_num) (add_pos_of_nonneg_of_pos hC zero_lt_one)
  have hpos : (0 : ℝ≥0∞).toReal < ε / (3 * (C + 1)) := by
    simpa only [ENNReal.toReal_zero] using div_pos hε hC₁
  have hV' := hV.eventually (gt_mem_nhds hpos)
  obtain ⟨d, hd, hdr, hsmall⟩ : ∃ d : ℝ, 0 < d ∧ d ≤ r ∧
      (eVariationOn f (Ioc 0 d)).toReal < ε / (3 * (C + 1)) := by
    have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[Icc 0 r] 0 := by
      rw [nhdsWithin_Icc_eq_nhdsGE hr]
      exact nhdsWithin_mono _ Ioi_subset_Ici_self
    have H := hle hV'
    apply Eventually.exists (f := 𝓝[>] (0 : ℝ))
    filter_upwards [H, Ioo_mem_nhdsGT hr] with d hd hd'
    have heq : Icc (0 : ℝ) r ∩ Ioc 0 d = Ioc 0 d := by grind
    exact ⟨hd'.1, hd'.2.le, by simpa [Function.comp_def, heq] using hd⟩
  have hvar : eVariationOn g (Icc 0 d) = eVariationOn f (Ioc 0 d) :=
    (eVariationOn.eVariationOn_Ioc_eq_Icc_of_continuousWithinAt hgc).symm.trans
      (eVariationOn.congr (hg.mono Ioc_subset_Ioi_self))
  have hgv : BoundedVariationOn g (Icc 0 d) := by
    rw [BoundedVariationOn, hvar]
    exact hv.mono (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hdr))
  refine ⟨d, hd, fun T ↦ ?_⟩
  refine (hgv.norm_intervalIntegral_smul_sub_left_le hd.le
    ((by fun_prop : Continuous (𝒦 T)).intervalIntegrable _ _)
    (fun c _ ↦ norm_integral_sincKernel_le hM T c d)).trans_lt ?_
  rw [hvar]
  have h := (lt_div_iff₀ hC₁).mp hsmall
  nlinarith [ENNReal.toReal_nonneg (a := eVariationOn f (Ioc 0 d))]

private theorem tendsto_setIntegral_sinc_smul_Ioi_of_boundedVariationOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : ℝ → E} {r : ℝ} (hr : 0 < r) (hf : IntegrableOn f (Ioi 0))
    (hv : BoundedVariationOn f (Icc 0 r)) :
    Tendsto (fun T : ℝ ↦ ∫ x in Ioi 0, 𝒦 T x • f x) atTop
      (𝓝 ((1 / 2 : ℝ) • f.rightLim 0)) := by
  -- Fill the endpoint with the right limit before estimating the variation.
  obtain ⟨l, hl⟩ := hv.exists_tendsto_right 0
  rw [show Icc (0 : ℝ) r ∩ Ioi 0 = Ioc 0 r by grind, nhdsWithin_Ioc_eq_nhdsGT hr] at hl
  rw [rightLim_eq_of_tendsto hl]
  let g := Function.update f 0 l
  have hg : EqOn g f (Ioi 0) := fun y hy ↦ Function.update_of_ne (ne_of_gt hy) _ _
  have hgc : ContinuousWithinAt g (Ici 0) 0 := by
    rw [← insert_Ioi, continuousWithinAt_insert_self]
    simpa [ContinuousWithinAt, g] using hl.congr'
      (eventually_nhdsWithin_iff.mpr (.of_forall fun _ hy ↦ (hg hy).symm))
  have hgi : IntegrableOn g (Ioi 0) := hf.congr_fun hg.symm measurableSet_Ioi
  have hg₀ : g 0 = l := by simp [g]
  rw [← hg₀]
  refine Tendsto.congr (fun T ↦ setIntegral_congr_fun measurableSet_Ioi fun _ hy ↦
    congrArg (𝒦 T _ • ·) (hg hy)) ?_
  refine Metric.tendsto_nhds.2 (fun ε hε ↦ ?_)
  obtain ⟨d, hd, hnear⟩ := exists_norm_integral_sincKernel_sub_lt hr hv hg hgc hε
  have hmass := ((tendsto_integral_sincKernel hd).smul_const (g 0)).eventually
    (Metric.ball_mem_nhds _ (by positivity : 0 < ε / 3))
  have ht := tendsto_setIntegral_sincKernel_Ioi hd (hgi.mono_set (Ioi_subset_Ioi hd.le))
  have htail := ht.eventually (Metric.ball_mem_nhds _ (by positivity : 0 < ε / 3))
  filter_upwards [hmass, htail] with T hT hT'
  have hi := integrableOn_sincKernel_smul hgi T
  have hw := (intervalIntegrable_iff_integrableOn_Ioc_of_le hd.le).2
    (hi.mono_set Ioc_subset_Ioi_self)
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi (hi.mono_set (Ioi_subset_Ioi hd.le))
  rw [dist_eq_norm] at hT hT'
  rw [dist_eq_norm, ← hsplit]
  have heq : (∫ x in 0..d, 𝒦 T x • g x) - (∫ x in 0..d, 𝒦 T x) • g 0 =
      ∫ x in 0..d, 𝒦 T x • (g x - g 0) := by
    have hconst : IntervalIntegrable (fun x ↦ 𝒦 T x • g 0) volume 0 d :=
      intervalIntegrable_const.continuousOn_smul
        (by fun_prop : Continuous (𝒦 T)).continuousOn
    rw [← intervalIntegral.integral_smul_const, ← intervalIntegral.integral_sub hw hconst]
    simp only [smul_sub]
  let A := ∫ x in 0..d, 𝒦 T x • g x
  let B := (∫ x in 0..d, 𝒦 T x) • g 0
  let D := ∫ x in Ioi d, 𝒦 T x • g x
  let L := (1 / 2 : ℝ) • g 0
  have hsum : A + D - L = (A - B) + (B - L) + D := by abel
  have hnear' : ‖A - B‖ < ε / 3 := heq ▸ hnear T
  calc
    ‖A + D - L‖ ≤ ‖A - B‖ + ‖B - L‖ + ‖D‖ := by
      rw [hsum]
      exact (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ < ε := by simp only [sub_zero] at hT'; linarith

/-- **Dirichlet–Jordan inversion.** If an integrable function has bounded variation on a
neighbourhood of `x`, its symmetric inverse Fourier integrals converge to the mean of its
left and right limits at `x`. -/
theorem MeasureTheory.Integrable.tendsto_intervalIntegral_fourierInv_fourier_of_boundedVariationOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : ℝ → E} (hf : Integrable f) {x r : ℝ} (hr : 0 < r)
    (hv : BoundedVariationOn f (Icc (x - r) (x + r))) :
    Tendsto (fun T : ℝ ↦ ∫ t in -T..T, 𝐞 (t * x) • 𝓕 f t) atTop
      (𝓝 ((1 / 2 : ℝ) • (f.leftLim x + f.rightLim x))) := by
  let left : ℝ → ℝ := fun u ↦ x - u
  let right : ℝ → ℝ := fun u ↦ x + u
  have hleft : BoundedVariationOn (f ∘ left) (Icc 0 r) :=
    ne_top_of_le_ne_top hv
      (eVariationOn.comp_le_of_antitoneOn f left (by intro u _ v _ huv; dsimp [left]; linarith)
        (by intro u hu; dsimp [left]; grind))
  have hright : BoundedVariationOn (f ∘ right) (Icc 0 r) :=
    ne_top_of_le_ne_top hv
      (eVariationOn.comp_le_of_monotoneOn f right (by intro u _ v _ huv; dsimp [right]; linarith)
        (by intro u hu; dsimp [right]; grind))
  have hl : Function.rightLim (f ∘ left) 0 = f.leftLim x := by
    obtain ⟨l, hl⟩ := hv.exists_tendsto_left x
    rw [show Icc (x - r) (x + r) ∩ Iio x = Ico (x - r) x by grind,
      nhdsWithin_Ico_eq_nhdsLT (by linarith)] at hl
    rw [leftLim_eq_of_tendsto hl]
    have hm' : map left (𝓝[>] 0) = 𝓝[<] x := by simp [left]
    exact rightLim_eq_of_tendsto (tendsto_map'_iff.mp (hm'.symm ▸ hl))
  have hrr : Function.rightLim (f ∘ right) 0 = f.rightLim x := by
    obtain ⟨l, hl⟩ := hv.exists_tendsto_right x
    rw [show Icc (x - r) (x + r) ∩ Ioi x = Ioc x (x + r) by grind,
      nhdsWithin_Ioc_eq_nhdsGT (by linarith)] at hl
    rw [rightLim_eq_of_tendsto hl]
    have hm' : map right (𝓝[>] 0) = 𝓝[>] x := by simp [right]
    exact rightLim_eq_of_tendsto (tendsto_map'_iff.mp (hm'.symm ▸ hl))
  have hl' := tendsto_setIntegral_sinc_smul_Ioi_of_boundedVariationOn hr
    (hf.comp_sub_left x).integrableOn hleft
  have hr' := tendsto_setIntegral_sinc_smul_Ioi_of_boundedVariationOn hr
    (hf.comp_add_left x).integrableOn hright
  simp only [left, Function.comp_def] at hl
  simp only [right, Function.comp_def] at hrr
  rw [hl] at hl'
  rw [hrr] at hr'
  refine (by simpa only [smul_add] using hl'.add hr' :
    Tendsto (fun T : ℝ ↦ (∫ u in Ioi 0, 𝒦 T u • f (x - u)) +
      ∫ u in Ioi 0, 𝒦 T u • f (x + u)) atTop _).congr (fun T ↦ ?_)
  rw [hf.intervalIntegral_fourierInv_fourier_eq_integral_sinc]
  have hcast (u : ℝ) : 2 * (T : ℂ) * (Real.sinc (2 * Real.pi * T * u) : ℂ) =
      (𝒦 T u : ℂ) := by push_cast; ring
  simp only [hcast, Complex.coe_smul]
  have hi : Integrable (fun u ↦ 𝒦 T u • f (x - u)) :=
    integrableOn_univ.mp (integrableOn_sincKernel_smul (hf.comp_sub_left x).integrableOn T)
  have hs := integral_add_compl (measurableSet_Ioi (a := (0 : ℝ))) hi
  rw [compl_Ioi, integral_Iic_eq_integral_Iio] at hs
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
    (Homeomorph.neg ℝ).measurableEmbedding (fun u ↦ 𝒦 T u • f (x - u)) (Iio 0)
  have hpre : (fun u : ℝ ↦ -u) ⁻¹' Iio 0 = Ioi 0 := by ext u; simp
  rw [hpre] at hneg
  have hK (u : ℝ) : 𝒦 T (-u) = 𝒦 T u := by simp [mul_neg, Real.sinc_neg]
  simpa only [← hneg, hK, sub_neg_eq_add] using hs

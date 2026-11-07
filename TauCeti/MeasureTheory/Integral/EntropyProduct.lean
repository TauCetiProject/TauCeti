/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Entropy
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Functional entropy and product measures

For a nonnegative integrable function whose `x log x` transform is integrable, the functional
entropy under a probability measure is nonnegative. This is Jensen's inequality for `x log x`,
including at zero. The product chain rule decomposes the entropy into averaged section entropies
and the entropy of the section average. An integral log-sum inequality yields entropy convexity
under mixtures and product subadditivity, assuming integrability of both marginal `x log x` terms.
-/

public section

open MeasureTheory Set

namespace MeasureTheory.Measure

private theorem sub_le_mul_log_sub_mul_log {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hzero : b = 0 → a = 0) : a - b ≤ a * Real.log a - a * Real.log b := by
  rcases eq_or_lt_of_le ha with rfl | ha
  · simp
    exact hb
  have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm (fun h ↦ ha.ne' (hzero h)))
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hb' ha)) ha.le
  rw [Real.log_div hb'.ne' ha.ne'] at h
  have hdiv : a * (b / a - 1) = b - a := by field_simp
  rw [hdiv] at h
  nlinarith

private theorem integral_log_sum_le_of_pos {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f h : α → ℝ} (hf : 0 ≤ᵐ[μ] f) (hh : 0 ≤ᵐ[μ] h)
    (hzero : ∀ᵐ x ∂μ, h x = 0 → f x = 0)
    (hfi : Integrable f μ) (hhi : Integrable h μ)
    (hflog : Integrable (fun x ↦ f x * Real.log (f x)) μ)
    (hcross : Integrable (fun x ↦ f x * Real.log (h x)) μ)
    (hF : 0 < ∫ x, f x ∂μ) (hH : 0 < ∫ x, h x ∂μ) :
    (∫ x, f x ∂μ) * Real.log ((∫ x, f x ∂μ) / (∫ x, h x ∂μ)) ≤
      ∫ x, f x * Real.log (f x) - f x * Real.log (h x) ∂μ := by
  let c : ℝ := (∫ x, f x ∂μ) / (∫ x, h x ∂μ)
  have hc : 0 < c := div_pos hF hH
  have hbound : ∀ᵐ x ∂μ, f x - c * h x ≤
      f x * Real.log (f x) - f x * Real.log (c * h x) := by
    filter_upwards [hf, hh, hzero] with x hx hy hz
    exact sub_le_mul_log_sub_mul_log hx (mul_nonneg hc.le hy) (by
      intro hz'
      have : h x = 0 := (mul_eq_zero.mp hz').resolve_left hc.ne'
      exact hz this)
  have hlog_eq : ∀ᵐ x ∂μ,
      f x * Real.log (c * h x) = f x * Real.log c + f x * Real.log (h x) := by
    filter_upwards [hzero] with x hx
    by_cases hz : h x = 0
    · simp [hx hz]
    · rw [Real.log_mul hc.ne' hz]
      ring
  have hscaled : Integrable (fun x ↦ f x * Real.log (c * h x)) μ := by
    apply (hfi.mul_const (Real.log c) |>.add hcross).congr
    filter_upwards [hlog_eq] with x hx
    exact hx.symm
  have hright : Integrable (fun x ↦ f x * Real.log (f x) -
      f x * Real.log (c * h x)) μ := hflog.sub hscaled
  have hint := integral_mono_ae (hfi.sub (hhi.const_mul c)) hright hbound
  change (∫ x, f x - c * h x ∂μ) ≤
    ∫ x, f x * Real.log (f x) - f x * Real.log (c * h x) ∂μ at hint
  rw [integral_sub hfi (hhi.const_mul c), integral_const_mul] at hint
  have hleft : (∫ x, f x ∂μ) - c * (∫ x, h x ∂μ) = 0 := by
    dsimp [c]
    field_simp
    ring
  rw [hleft] at hint
  rw [integral_sub hflog hscaled] at hint
  have heq : ∫ x, f x * Real.log (c * h x) ∂μ =
      (∫ x, f x ∂μ) * Real.log c + ∫ x, f x * Real.log (h x) ∂μ := by
    calc
      _ = ∫ x, f x * Real.log c + f x * Real.log (h x) ∂μ := integral_congr_ae hlog_eq
      _ = _ := by rw [integral_add (hfi.mul_const _) hcross, integral_mul_const]
  rw [heq] at hint
  rw [integral_sub hflog hcross]
  dsimp [c] at hint
  linarith

/-- The integral log-sum inequality. Zero values and zero total masses are allowed. The second
function must vanish only where the first does, and the cross-logarithm must be integrable. -/
theorem integral_log_sum_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f h : α → ℝ} (hf : 0 ≤ᵐ[μ] f) (hh : 0 ≤ᵐ[μ] h)
    (hzero : ∀ᵐ x ∂μ, h x = 0 → f x = 0)
    (hfi : Integrable f μ) (hhi : Integrable h μ)
    (hflog : Integrable (fun x ↦ f x * Real.log (f x)) μ)
    (hcross : Integrable (fun x ↦ f x * Real.log (h x)) μ) :
    (∫ x, f x ∂μ) * Real.log ((∫ x, f x ∂μ) / (∫ x, h x ∂μ)) ≤
      ∫ x, f x * Real.log (f x) - f x * Real.log (h x) ∂μ := by
  have hF := integral_nonneg_of_ae hf
  have hH := integral_nonneg_of_ae hh
  by_cases hFzero : ∫ x, f x ∂μ = 0
  · have hfzero := (integral_eq_zero_iff_of_nonneg_ae hf hfi).mp hFzero
    have hright : (∫ x, f x * Real.log (f x) - f x * Real.log (h x) ∂μ) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hfzero] with x hx
      simp only [Pi.zero_apply] at hx
      simp [hx]
    simp [hFzero, hright]
  · have hFpos : 0 < ∫ x, f x ∂μ := lt_of_le_of_ne hF (Ne.symm hFzero)
    have hHpos : 0 < ∫ x, h x ∂μ := by
      apply lt_of_le_of_ne hH
      intro hz
      have hhzero := (integral_eq_zero_iff_of_nonneg_ae hh hhi).mp hz.symm
      have hfzero : f =ᵐ[μ] 0 := by
        filter_upwards [hhzero, hzero] with x hx hx'
        exact hx' hx
      exact hFzero (integral_eq_zero_of_ae hfzero)
    exact integral_log_sum_le_of_pos μ hf hh hzero hfi hhi hflog hcross hFpos hHpos

/-- Functional entropy is nonnegative under a probability measure. -/
theorem entropy_nonneg {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {g : α → ℝ} (hg : 0 ≤ᵐ[μ] g)
    (hgi : Integrable g μ) (hlog : Integrable (fun x ↦ g x * Real.log (g x)) μ) :
    0 ≤ entropy μ g := by
  have h := Real.convexOn_mul_log.map_integral_le Real.continuous_mul_log.continuousOn
    isClosed_Ici hg hgi hlog
  rw [entropy_def]
  linarith

/-- The functional entropy chain rule for a product measure. -/
theorem entropy_prod_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] (g : α × β → ℝ)
    (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν))
    (hmarg : Integrable (fun x ↦ (∫ y, g (x, y) ∂ν) *
      Real.log (∫ y, g (x, y) ∂ν)) μ) :
    entropy (μ.prod ν) g =
      (∫ x, entropy ν (fun y ↦ g (x, y)) ∂μ) +
        entropy μ (fun x ↦ ∫ y, g (x, y) ∂ν) := by
  simp only [entropy_def]
  rw [integral_prod g hg, integral_prod _ hlog,
    integral_sub hlog.integral_prod_left hmarg]
  ring

/-- Averaging out one coordinate cannot increase the functional entropy. -/
theorem entropy_integral_prod_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (g : α × β → ℝ) (hnonneg : 0 ≤ᵐ[μ.prod ν] g)
    (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν))
    (hmarg : Integrable (fun x ↦ (∫ y, g (x, y) ∂ν) *
      Real.log (∫ y, g (x, y) ∂ν)) μ) :
    entropy μ (fun x ↦ ∫ y, g (x, y) ∂ν) ≤ entropy (μ.prod ν) g := by
  have hsection : ∀ᵐ x ∂μ, 0 ≤ entropy ν (fun y ↦ g (x, y)) := by
    filter_upwards [ae_ae_of_ae_prod hnonneg, hg.prod_right_ae, hlog.prod_right_ae]
      with x hx hxi hli
    exact entropy_nonneg ν hx hxi hli
  rw [entropy_prod_eq μ ν g hg hlog hmarg]
  have := integral_nonneg_of_ae hsection
  linarith

private theorem ae_section_eq_zero_of_marginal_eq_zero {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] {g : α × β → ℝ}
    (hnonneg : 0 ≤ᵐ[μ.prod ν] g) (hg : Integrable g (μ.prod ν)) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, (∫ x, g (x, y) ∂μ) = 0 → g (x, y) = 0 := by
  let b : β → ℝ := fun y ↦ ∫ x, g (x, y) ∂μ
  let gm := hg.aestronglyMeasurable.mk g
  let bm := hg.integral_prod_right.aestronglyMeasurable.mk b
  have hg_eq : g =ᵐ[μ.prod ν] gm := hg.aestronglyMeasurable.ae_eq_mk
  have hb_eq : b =ᵐ[ν] bm := hg.integral_prod_right.aestronglyMeasurable.ae_eq_mk
  have hswap : ∀ᵐ p ∂ν.prod μ, 0 ≤ g (p.2, p.1) :=
    measurePreserving_swap.quasiMeasurePreserving.ae hnonneg
  have hswap_eq : ∀ᵐ p ∂ν.prod μ, g (p.2, p.1) = gm (p.2, p.1) :=
    measurePreserving_swap.quasiMeasurePreserving.ae hg_eq
  have hreverse : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, bm y = 0 → gm (x, y) = 0 := by
    filter_upwards [ae_ae_of_ae_prod hswap, hg.prod_left_ae, hb_eq,
      ae_ae_of_ae_prod hswap_eq] with y hy hyi hby hgy
    by_cases hz : b y = 0
    · have hzero := (integral_eq_zero_iff_of_nonneg_ae hy hyi).mp hz
      filter_upwards [hzero, hgy] with x hx hx'
      intro _
      simpa only [Pi.zero_apply] using hx'.symm.trans hx
    · filter_upwards with x
      intro hbz
      exact False.elim (hz (hby.trans hbz))
  have hmeas : MeasurableSet {p : α × β | bm p.2 = 0 → gm p = 0} := by
    have hbm : Measurable bm := hg.integral_prod_right.aestronglyMeasurable.stronglyMeasurable_mk.measurable
    have hgm : Measurable gm := hg.aestronglyMeasurable.stronglyMeasurable_mk.measurable
    have h1 : MeasurableSet {p : α × β | bm p.2 = 0} :=
      measurableSet_eq_fun (hbm.comp measurable_snd) measurable_const
    have h2 : MeasurableSet {p : α × β | gm p = 0} :=
      measurableSet_eq_fun hgm measurable_const
    convert h1.compl.union h2 using 1
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff]
    exact imp_iff_not_or
  have hforward : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, bm y = 0 → gm (x, y) = 0 :=
    (ae_ae_comm hmeas).mpr hreverse
  have hb_prod : ∀ᵐ p ∂μ.prod ν, b p.2 = bm p.2 :=
    quasiMeasurePreserving_snd.ae hb_eq
  filter_upwards [hforward, ae_ae_of_ae_prod hg_eq, ae_ae_of_ae_prod hb_prod] with x hx hxg hxb
  filter_upwards [hx, hxg, hxb] with y hy hy' hy''
  intro hz
  exact hy'.trans (hy (hy''.symm.trans hz))

private theorem integrable_marginal_cross_log {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] {g : α × β → ℝ}
    (hnonneg : 0 ≤ᵐ[μ.prod ν] g) (hg : Integrable g (μ.prod ν))
    (hmarg : Integrable (fun y ↦ (∫ x, g (x, y) ∂μ) *
      Real.log (∫ x, g (x, y) ∂μ)) ν) :
    Integrable (fun p ↦ g p * Real.log (∫ x, g (x, p.2) ∂μ)) (μ.prod ν) := by
  let b : β → ℝ := fun y ↦ ∫ x, g (x, y) ∂μ
  have hbi : Integrable b ν := hg.integral_prod_right
  have hlog : AEMeasurable (fun y ↦ Real.log (b y)) ν :=
    Real.measurable_log.comp_aemeasurable hbi.aestronglyMeasurable.aemeasurable
  have hmeas : AEStronglyMeasurable (fun p ↦ g p * Real.log (b p.2)) (μ.prod ν) :=
    hg.aestronglyMeasurable.mul
      (hlog.aestronglyMeasurable.comp_quasiMeasurePreserving quasiMeasurePreserving_snd)
  apply (integrable_prod_iff' hmeas).2
  constructor
  · filter_upwards [hg.prod_left_ae] with y hy
    exact hy.mul_const _
  · have hswap : ∀ᵐ p ∂ν.prod μ, 0 ≤ g (p.2, p.1) :=
      measurePreserving_swap.quasiMeasurePreserving.ae hnonneg
    apply hmarg.norm.congr
    filter_upwards [ae_ae_of_ae_prod hswap] with y hy
    have hb : 0 ≤ b y := integral_nonneg_of_ae hy
    calc
      ‖b y * Real.log (b y)‖ = b y * ‖Real.log (b y)‖ := by rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hb]
      _ = ∫ x, g (x, y) * ‖Real.log (b y)‖ ∂μ := (integral_mul_const _ _).symm
      _ = ∫ x, ‖g (x, y) * Real.log (b y)‖ ∂μ := by
        apply integral_congr_ae
        filter_upwards [hy] with x hx
        simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hx]

/-- Entropy is convex under mixtures, when the indicated marginal cross-logarithm is integrable. -/
private theorem entropy_integral_le_integral_entropy_of_pos {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (g : α × β → ℝ)
    (hnonneg : 0 ≤ᵐ[μ.prod ν] g)
    (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν))
    (hmargx : Integrable (fun x ↦ (∫ y, g (x, y) ∂ν) *
      Real.log (∫ y, g (x, y) ∂ν)) μ)
    (hmargy : Integrable (fun y ↦ (∫ x, g (x, y) ∂μ) *
      Real.log (∫ x, g (x, y) ∂μ)) ν)
    (hcross : Integrable (fun p ↦ g p * Real.log (∫ x, g (x, p.2) ∂μ))
      (μ.prod ν))
    (hzero : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, (∫ x, g (x, y) ∂μ) = 0 → g (x, y) = 0)
    (htotal : 0 < ∫ p, g p ∂(μ.prod ν)) :
    entropy μ (fun x ↦ ∫ y, g (x, y) ∂ν) ≤
      ∫ y, entropy μ (fun x ↦ g (x, y)) ∂ν := by
  let a : α → ℝ := fun x ↦ ∫ y, g (x, y) ∂ν
  let b : β → ℝ := fun y ↦ ∫ x, g (x, y) ∂μ
  let m : ℝ := ∫ p, g p ∂(μ.prod ν)
  have hai : Integrable a μ := hg.integral_prod_left
  have hbi : Integrable b ν := hg.integral_prod_right
  have ham : ∫ x, a x ∂μ = m := (integral_prod g hg).symm
  have hbm : ∫ y, b y ∂ν = m := (integral_prod_symm g hg).symm
  have hb : 0 ≤ᵐ[ν] b := by
    have hswap : ∀ᵐ p ∂ν.prod μ, 0 ≤ g (p.2, p.1) :=
      measurePreserving_swap.quasiMeasurePreserving.ae hnonneg
    filter_upwards [ae_ae_of_ae_prod hswap] with y hy
    exact integral_nonneg_of_ae hy
  have hpoint : ∀ᵐ x ∂μ, a x * Real.log (a x) - a x * Real.log m ≤
      ∫ y, g (x, y) * Real.log (g (x, y)) - g (x, y) * Real.log (b y) ∂ν := by
    filter_upwards [ae_ae_of_ae_prod hnonneg, hg.prod_right_ae,
      hlog.prod_right_ae, hcross.prod_right_ae, hzero] with x hx hxi hli hci hz
    have h := integral_log_sum_le ν hx hb hz hxi hbi hli hci
    change a x * Real.log (a x / ∫ y, b y ∂ν) ≤ _ at h
    rw [hbm] at h
    by_cases ha : a x = 0
    · simpa [ha] using h
    · rw [Real.log_div ha htotal.ne'] at h
      linarith
  have hleft := hmargx.sub (hai.mul_const (Real.log m))
  have hright := (hlog.sub hcross).integral_prod_left
  have hint := integral_mono_ae hleft hright hpoint
  change (∫ x, a x * Real.log (a x) - a x * Real.log m ∂μ) ≤
    ∫ x, ∫ y, g (x, y) * Real.log (g (x, y)) -
      g (x, y) * Real.log (b y) ∂ν ∂μ at hint
  rw [integral_sub hmargx (hai.mul_const _), integral_mul_const, ham] at hint
  have hcross_eq : (∫ p, g p * Real.log (b p.2) ∂(μ.prod ν)) =
      ∫ y, b y * Real.log (b y) ∂ν := by
    rw [integral_prod_symm _ hcross]
    apply integral_congr_ae
    filter_upwards [hg.prod_left_ae] with y hy
    exact integral_mul_const _ _
  change (∫ x, a x * Real.log (a x) ∂μ) - m * Real.log m ≤
    ∫ x, ∫ y, ((fun p ↦ g p * Real.log (g p)) -
      (fun p ↦ g p * Real.log (b p.2))) (x, y) ∂ν ∂μ at hint
  rw [← integral_prod _ (hlog.sub hcross)] at hint
  change (∫ x, a x * Real.log (a x) ∂μ) - m * Real.log m ≤
    ∫ p, g p * Real.log (g p) - g p * Real.log (b p.2) ∂(μ.prod ν) at hint
  rw [integral_sub hlog hcross, hcross_eq] at hint
  rw [entropy_def, ham]
  have hsec : (∫ y, entropy μ (fun x ↦ g (x, y)) ∂ν) =
      (∫ p, g p * Real.log (g p) ∂(μ.prod ν)) -
        ∫ y, b y * Real.log (b y) ∂ν := by
    simp only [entropy_def]
    rw [integral_sub hlog.integral_prod_right hmargy,
      ← integral_prod_symm _ hlog]
  rw [hsec]
  exact hint

/-- Entropy is convex under mixtures, including when the total mass is zero. The hypotheses
ensure integrability of both marginal `x log x` terms. -/
theorem entropy_integral_le_integral_entropy {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (g : α × β → ℝ)
    (hnonneg : 0 ≤ᵐ[μ.prod ν] g)
    (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν))
    (hmargx : Integrable (fun x ↦ (∫ y, g (x, y) ∂ν) *
      Real.log (∫ y, g (x, y) ∂ν)) μ)
    (hmargy : Integrable (fun y ↦ (∫ x, g (x, y) ∂μ) *
      Real.log (∫ x, g (x, y) ∂μ)) ν) :
    entropy μ (fun x ↦ ∫ y, g (x, y) ∂ν) ≤
      ∫ y, entropy μ (fun x ↦ g (x, y)) ∂ν := by
  have htotal := integral_nonneg_of_ae hnonneg
  by_cases hz : ∫ p, g p ∂(μ.prod ν) = 0
  · have hgzero := (integral_eq_zero_iff_of_nonneg_ae hnonneg hg).mp hz
    have hsecx : ∀ᵐ x ∂μ, (∫ y, g (x, y) ∂ν) = 0 := by
      filter_upwards [ae_ae_of_ae_prod hgzero] with x hx
      exact integral_eq_zero_of_ae hx
    have hleft : entropy μ (fun x ↦ ∫ y, g (x, y) ∂ν) = 0 := by
      rw [entropy_def, integral_eq_zero_of_ae hsecx]
      have h : (∫ x, (∫ y, g (x, y) ∂ν) *
          Real.log (∫ y, g (x, y) ∂ν) ∂μ) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [hsecx] with x hx
        simp [hx]
      simpa using h
    have hsecy : ∀ᵐ y ∂ν, (fun x ↦ g (x, y)) =ᵐ[μ] 0 := by
      have hswap : ∀ᵐ p ∂ν.prod μ, g (p.2, p.1) = 0 :=
        measurePreserving_swap.quasiMeasurePreserving.ae hgzero
      exact ae_ae_of_ae_prod hswap
    have hright : ∀ᵐ y ∂ν, entropy μ (fun x ↦ g (x, y)) = 0 := by
      filter_upwards [hsecy] with y hy
      rw [entropy_def, integral_eq_zero_of_ae hy]
      have h : (∫ x, g (x, y) * Real.log (g (x, y)) ∂μ) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [hy] with x hx
        simp only [Pi.zero_apply] at hx
        simp [hx]
      simpa using h
    rw [hleft, integral_eq_zero_of_ae hright]
  · exact entropy_integral_le_integral_entropy_of_pos μ ν g hnonneg hg hlog hmargx
      hmargy (integrable_marginal_cross_log μ ν hnonneg hg hmargy)
      (ae_section_eq_zero_of_marginal_eq_zero μ ν hnonneg hg)
      (lt_of_le_of_ne htotal (Ne.symm hz))

/-- Product entropy subadditivity under marginal `x log x` integrability hypotheses. -/
theorem entropy_prod_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (g : α × β → ℝ) (hnonneg : 0 ≤ᵐ[μ.prod ν] g)
    (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν))
    (hmargx : Integrable (fun x ↦ (∫ y, g (x, y) ∂ν) *
      Real.log (∫ y, g (x, y) ∂ν)) μ)
    (hmargy : Integrable (fun y ↦ (∫ x, g (x, y) ∂μ) *
      Real.log (∫ x, g (x, y) ∂μ)) ν) :
    entropy (μ.prod ν) g ≤
      (∫ x, entropy ν (fun y ↦ g (x, y)) ∂μ) +
        ∫ y, entropy μ (fun x ↦ g (x, y)) ∂ν := by
  rw [entropy_prod_eq μ ν g hg hlog hmargx]
  have h := entropy_integral_le_integral_entropy μ ν g hnonneg hg hlog hmargx hmargy
  linarith

end MeasureTheory.Measure

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Entropy.Basic
public import TauCeti.MeasureTheory.Integral.Entropy.LogSum
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import TauCeti.MeasureTheory.Integral.Prod

/-!
# Functional entropy and product measures

For a nonnegative integrable function whose `x log x` transform is integrable, the functional
entropy under a probability measure is nonnegative. This is Jensen's inequality for `x log x`,
including at zero. The product chain rule decomposes the entropy into averaged section entropies
and the entropy of the section average. An integral log-sum inequality yields entropy convexity
under mixtures and product subadditivity. For probability factors, joint integrability suffices;
more general versions take integrability of both marginal `x log x` terms as hypotheses.
-/

public section

open MeasureTheory Set

namespace MeasureTheory.Measure

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

/-- Integrability of `g log g` passes to the marginal over a probability measure when the
remaining measure is finite. -/
theorem integrable_marginal_mul_log {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    {g : α × β → ℝ} (hnonneg : 0 ≤ᵐ[μ.prod ν] g)
    (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    Integrable (fun x ↦ (∫ y, g (x, y) ∂ν) *
      Real.log (∫ y, g (x, y) ∂ν)) μ := by
  have hmeas : AEStronglyMeasurable (fun x ↦ (∫ y, g (x, y) ∂ν) *
      Real.log (∫ y, g (x, y) ∂ν)) μ :=
    (Real.continuous_mul_log.measurable.comp_aemeasurable
      hg.integral_prod_left.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  apply (hlog.integral_prod_left.norm.add (integrable_const 1)).mono' hmeas
  filter_upwards [ae_ae_of_ae_prod hnonneg, hg.prod_right_ae, hlog.prod_right_ae]
    with x hx hxi hli
  have ha := integral_nonneg_of_ae hx
  have hlower := Real.self_sub_one_le_mul_log ha
  have hupper := Real.convexOn_mul_log.map_integral_le
    Real.continuous_mul_log.continuousOn isClosed_Ici hx hxi hli
  simp only [Pi.add_apply, Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · linarith [abs_nonneg (∫ y, g (x, y) * Real.log (g (x, y)) ∂ν)]
  · linarith [le_abs_self (∫ y, g (x, y) * Real.log (g (x, y)) ∂ν)]

/-- Averaging out a probability-measure coordinate cannot increase functional entropy for an
a.e. nonnegative function, when the function, its `x log x` transform, and the marginal `x log x`
are integrable. -/
theorem entropy_integral_prod_left_le_entropy_prod_of_integrable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [IsProbabilityMeasure ν]
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

/-- Averaging over a probability coordinate cannot increase entropy when the outer measure is
finite and the function and its `x log x` transform are integrable. -/
theorem entropy_integral_prod_left_le_entropy_prod
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (g : α × β → ℝ) (hnonneg : 0 ≤ᵐ[μ.prod ν] g)
    (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    entropy μ (fun x ↦ ∫ y, g (x, y) ∂ν) ≤ entropy (μ.prod ν) g :=
  entropy_integral_prod_left_le_entropy_prod_of_integrable μ ν g hnonneg hg hlog
    (integrable_marginal_mul_log μ ν hnonneg hg hlog)

/-- For an a.e. nonnegative function, entropy is convex under mixtures if
the function, its `x log x` transform, both marginal `x log x` terms, and the marginal cross-log
are integrable. The support condition says that a zero marginal forces the function to vanish
a.e. in that section. -/
private theorem entropy_integral_le_integral_entropy_aux {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] (g : α × β → ℝ)
    (hnonneg : 0 ≤ᵐ[μ.prod ν] g)
    (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν))
    (hmargx : Integrable (fun x ↦ (∫ y, g (x, y) ∂ν) *
      Real.log (∫ y, g (x, y) ∂ν)) μ)
    (hmargy : Integrable (fun y ↦ (∫ x, g (x, y) ∂μ) *
      Real.log (∫ x, g (x, y) ∂μ)) ν)
    (hcross : Integrable (fun p ↦ g p * Real.log (∫ x, g (x, p.2) ∂μ))
      (μ.prod ν))
    (hzero : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, (∫ x, g (x, y) ∂μ) = 0 → g (x, y) = 0) :
    entropy μ (fun x ↦ ∫ y, g (x, y) ∂ν) ≤
      ∫ y, entropy μ (fun x ↦ g (x, y)) ∂ν := by
  let a : α → ℝ := fun x ↦ ∫ y, g (x, y) ∂ν
  let b : β → ℝ := fun y ↦ ∫ x, g (x, y) ∂μ
  let m : ℝ := ∫ p, g p ∂(μ.prod ν)
  have hai : Integrable a μ := hg.integral_prod_left
  have hbi : Integrable b ν := hg.integral_prod_right
  have ham : ∫ x, a x ∂μ = m := (integral_prod g hg).symm
  have hbm : ∫ y, b y ∂ν = m := (integral_prod_symm g hg).symm
  have hazero : ∀ᵐ x ∂μ, m = 0 → a x = 0 := by
    by_cases hm : m = 0
    · have hgzero := (integral_eq_zero_iff_of_nonneg_ae hnonneg hg).mp hm
      filter_upwards [ae_ae_of_ae_prod hgzero] with x hx
      intro _
      exact integral_eq_zero_of_ae hx
    · filter_upwards with x
      intro h
      exact (hm h).elim
  have hb : 0 ≤ᵐ[ν] b := by
    have hswap : ∀ᵐ p ∂ν.prod μ, 0 ≤ g (p.2, p.1) :=
      measurePreserving_swap.quasiMeasurePreserving.ae hnonneg
    filter_upwards [ae_ae_of_ae_prod hswap] with y hy
    exact integral_nonneg_of_ae hy
  have hpoint : ∀ᵐ x ∂μ, a x * Real.log (a x) - a x * Real.log m ≤
      ∫ y, g (x, y) * Real.log (g (x, y)) - g (x, y) * Real.log (b y) ∂ν := by
    filter_upwards [ae_ae_of_ae_prod hnonneg, hg.prod_right_ae,
      hlog.prod_right_ae, hcross.prod_right_ae, hzero, hazero] with x hx hxi hli hci hz hmzero
    have h := integral_log_sum_le ν hx hb hz hxi hbi (hli.sub hci)
    -- Expose the named marginals so their common mass can be rewritten.
    change a x * Real.log (a x / ∫ y, b y ∂ν) ≤ _ at h
    rw [hbm] at h
    by_cases hm : m = 0
    · simpa [hmzero hm] using h
    · by_cases ha : a x = 0
      · simpa [ha] using h
      · rw [Real.log_div ha hm] at h
        linarith
  have hleft := hmargx.sub (hai.mul_const (Real.log m))
  have hright := (hlog.sub hcross).integral_prod_left
  have hint := integral_mono_ae hleft hright hpoint
  -- The integrability lemmas use pointwise function subtraction; expose the integrands for Fubini.
  change (∫ x, a x * Real.log (a x) - a x * Real.log m ∂μ) ≤
    ∫ x, ∫ y, g (x, y) * Real.log (g (x, y)) -
      g (x, y) * Real.log (b y) ∂ν ∂μ at hint
  rw [integral_sub hmargx (hai.mul_const _), integral_mul_const, ham] at hint
  have hcross_eq : (∫ p, g p * Real.log (b p.2) ∂(μ.prod ν)) =
      ∫ y, b y * Real.log (b y) ∂ν := by
    rw [integral_prod_symm _ hcross]
    apply integral_congr_ae
    filter_upwards with y
    exact integral_mul_const (μ := μ) (Real.log (b y)) (fun x : α ↦ g (x, y))
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
    have hswap_entropy : entropy (ν.prod μ) (g ∘ Prod.swap) = entropy (μ.prod ν) g := by
      rw [← prod_swap]
      change entropy (Measure.map (MeasurableEquiv.prodComm : α × β ≃ᵐ β × α) (μ.prod ν))
        (g ∘ Prod.swap) = _
      rw [entropy_map (MeasurableEquiv.prodComm : α × β ≃ᵐ β × α).measurableEmbedding]
      change entropy (μ.prod ν) (fun p ↦ g (Prod.swap (Prod.swap p))) = _
      simp only [Prod.swap_swap]
    have hchain := entropy_prod_eq ν μ (g ∘ Prod.swap) hg.swap hlog.swap hmargy
    rw [hswap_entropy] at hchain
    change entropy (μ.prod ν) g =
      (∫ y, entropy μ (fun x ↦ g (x, y)) ∂ν) + entropy ν b at hchain
    rw [entropy_def, entropy_def, integral_prod_symm g hg] at hchain
    linarith
  rw [hsec]
  exact hint

/-- Entropy is convex under mixtures for an a.e. nonnegative function, including when its total
mass is zero. The hypotheses ensure integrability of both marginal `x log x` terms. -/
theorem entropy_integral_le_integral_entropy_of_integrable {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] (g : α × β → ℝ)
    (hnonneg : 0 ≤ᵐ[μ.prod ν] g)
    (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν))
    (hmargx : Integrable (fun x ↦ (∫ y, g (x, y) ∂ν) *
      Real.log (∫ y, g (x, y) ∂ν)) μ)
    (hmargy : Integrable (fun y ↦ (∫ x, g (x, y) ∂μ) *
      Real.log (∫ x, g (x, y) ∂μ)) ν) :
    entropy μ (fun x ↦ ∫ y, g (x, y) ∂ν) ≤
      ∫ y, entropy μ (fun x ↦ g (x, y)) ∂ν := by
  have hweight : AEMeasurable (fun y ↦ Real.log (∫ x, g (x, y) ∂μ)) ν :=
    Real.measurable_log.comp_aemeasurable
      hg.integral_prod_right.aestronglyMeasurable.aemeasurable
  exact entropy_integral_le_integral_entropy_aux μ ν g hnonneg hg hlog hmargx
    hmargy (TauCeti.integrable_mul_marginal_weight μ ν hnonneg hg hweight hmargy)
    (ae_ae_of_ae_prod (TauCeti.ae_eq_zero_of_marginal_eq_zero μ ν hnonneg hg))

/-- Product entropy subadditivity for an a.e. nonnegative function under marginal `x log x`
integrability hypotheses. -/
theorem entropy_prod_le_of_integrable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
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
  have h := entropy_integral_le_integral_entropy_of_integrable μ ν g hnonneg hg hlog hmargx hmargy
  linarith

/-- Entropy is convex under mixtures of probability measures, assuming integrability of the
function and its `x log x` transform. -/
theorem entropy_integral_le_integral_entropy {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (g : α × β → ℝ)
    (hnonneg : 0 ≤ᵐ[μ.prod ν] g)
    (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    entropy μ (fun x ↦ ∫ y, g (x, y) ∂ν) ≤
      ∫ y, entropy μ (fun x ↦ g (x, y)) ∂ν := by
  have hswap : 0 ≤ᵐ[ν.prod μ] (g ∘ Prod.swap) :=
    measurePreserving_swap.quasiMeasurePreserving.ae hnonneg
  exact entropy_integral_le_integral_entropy_of_integrable μ ν g hnonneg hg hlog
    (integrable_marginal_mul_log μ ν hnonneg hg hlog)
    (integrable_marginal_mul_log ν μ hswap hg.swap hlog.swap)

/-- Product entropy subadditivity for probability measures, assuming integrability of the
function and its `x log x` transform. -/
theorem entropy_prod_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (g : α × β → ℝ) (hnonneg : 0 ≤ᵐ[μ.prod ν] g)
    (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    entropy (μ.prod ν) g ≤
      (∫ x, entropy ν (fun y ↦ g (x, y)) ∂μ) +
        ∫ y, entropy μ (fun x ↦ g (x, y)) ∂ν := by
  have hswap : 0 ≤ᵐ[ν.prod μ] (g ∘ Prod.swap) :=
    measurePreserving_swap.quasiMeasurePreserving.ae hnonneg
  exact entropy_prod_le_of_integrable μ ν g hnonneg hg hlog
    (integrable_marginal_mul_log μ ν hnonneg hg hlog)
    (integrable_marginal_mul_log ν μ hswap hg.swap hlog.swap)

end MeasureTheory.Measure

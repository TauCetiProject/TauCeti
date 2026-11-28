/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Entropy.Basic
import TauCeti.InformationTheory.KullbackLeibler.Convex
public import TauCeti.MeasureTheory.Integral.Prod.MulLog

/-!
# Functional entropy and product measures

The product chain rule applies to signed functions when `g`, `g log g`, and the first marginal's
`x log x` transform are integrable. An integral log-sum inequality yields entropy
convexity under unnormalized mixtures and product subadditivity for a.e. nonnegative functions.
The mixture inequality integrates both sides against the mixing measure without dividing by its
mass. For finite factors, integrability of `g` and `g log g` on the product suffices. The s-finite
mixture and subadditivity results require both marginal transforms to be integrable; the chain
rule and averaging inequality require only the first. Averaging assumes a probability second
factor and an a.e. nonnegative function; the mixture inequality needs no normalization.
Product subadditivity bounds joint entropy by the sum of integrated coordinate entropies;
factorwise logarithmic Sobolev bounds can therefore be applied to the sections for tensorization.
-/

public section

open MeasureTheory Set

namespace MeasureTheory.Measure

/-- Swapping both factors and the function's arguments preserves product entropy. -/
@[simp]
theorem entropy_prod_swap {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] (g : α × β → ℝ) :
    entropy (ν.prod μ) (g ∘ Prod.swap) = entropy (μ.prod ν) g := by
  rw [← measurePreserving_swap.map_eq]
  have hswap : MeasurableEmbedding (Prod.swap : α × β → β × α) :=
    MeasurableEquiv.prodComm.measurableEmbedding
  rw [entropy_map hswap]
  simp [Function.comp_def]

/-- Integrating first-coordinate section entropies subtracts the marginal
`x log x` integral from the joint `x log x` integral. -/
private theorem integral_entropy_prod_left {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] (g : α × β → ℝ)
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν))
    (hmarg : Integrable (fun x ↦ (∫ y, g (x, y) ∂ν) *
      Real.log (∫ y, g (x, y) ∂ν)) μ) :
    (∫ x, entropy ν (fun y ↦ g (x, y)) ∂μ) =
      (∫ p, g p * Real.log (g p) ∂(μ.prod ν)) -
        ∫ x, (∫ y, g (x, y) ∂ν) * Real.log (∫ y, g (x, y) ∂ν) ∂μ := by
  simp only [entropy_def]
  rw [integral_sub hlog.integral_prod_left hmarg, ← integral_prod _ hlog]

/-- The functional entropy chain rule when `g`, `g log g`, and the first marginal's `x log x`
transform are integrable. -/
theorem entropy_prod_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] (g : α × β → ℝ)
    (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν))
    (hmarg : Integrable (fun x ↦ (∫ y, g (x, y) ∂ν) *
      Real.log (∫ y, g (x, y) ∂ν)) μ) :
    entropy (μ.prod ν) g =
      (∫ x, entropy ν (fun y ↦ g (x, y)) ∂μ) +
        entropy μ (fun x ↦ ∫ y, g (x, y) ∂ν) := by
  rw [integral_entropy_prod_left μ ν g hlog hmarg]
  simp only [entropy_def]
  rw [integral_prod g hg]
  ring

/-- Section entropies are integrable when the joint and first marginal `x log x`
transforms are integrable. -/
theorem integrable_entropy_prod_left {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite ν] (g : α × β → ℝ)
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν))
    (hmarg : Integrable (fun x ↦ (∫ y, g (x, y) ∂ν) *
      Real.log (∫ y, g (x, y) ∂ν)) μ) :
    Integrable (fun x ↦ entropy ν (fun y ↦ g (x, y))) μ := by
  convert hlog.integral_prod_left.sub hmarg using 1
  funext x
  simp only [entropy_def, Pi.sub_apply]

/-- Section entropies in the second coordinate are integrable under the corresponding
joint and marginal `x log x` hypotheses. -/
theorem integrable_entropy_prod_right {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] (g : α × β → ℝ)
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν))
    (hmarg : Integrable (fun y ↦ (∫ x, g (x, y) ∂μ) *
      Real.log (∫ x, g (x, y) ∂μ)) ν) :
    Integrable (fun y ↦ entropy μ (fun x ↦ g (x, y))) ν := by
  convert hlog.integral_prod_right.sub hmarg using 1
  funext y
  simp only [entropy_def, Pi.sub_apply]

/-- Averaging out a probability-measure coordinate cannot increase functional entropy for an
a.e. nonnegative function, when the function, its `x log x` transform, and the marginal `x log x`
are integrable. -/
theorem entropy_integral_prod_left_le_entropy_prod_of_integrable_marginal_mul_log
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

/-- Averaging an a.e. nonnegative function over a probability coordinate cannot increase entropy
when the outer measure is finite and the function and its `x log x` transform are integrable. -/
theorem entropy_integral_prod_left_le_entropy_prod
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (g : α × β → ℝ) (hnonneg : 0 ≤ᵐ[μ.prod ν] g)
    (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    entropy μ (fun x ↦ ∫ y, g (x, y) ∂ν) ≤ entropy (μ.prod ν) g :=
  entropy_integral_prod_left_le_entropy_prod_of_integrable_marginal_mul_log μ ν g hnonneg hg hlog
    (integrable_marginal_mul_log_left μ ν hg hlog)

/-- Integrating section entropies is the difference of the joint and marginal `x log x`
integrals. -/
private theorem integral_entropy_prod_right {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] (g : α × β → ℝ)
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν))
    (hmargy : Integrable (fun y ↦ (∫ x, g (x, y) ∂μ) *
      Real.log (∫ x, g (x, y) ∂μ)) ν) :
    (∫ y, entropy μ (fun x ↦ g (x, y)) ∂ν) =
      (∫ p, g p * Real.log (g p) ∂(μ.prod ν)) -
        ∫ y, (∫ x, g (x, y) ∂μ) * Real.log (∫ x, g (x, y) ∂μ) ∂ν := by
  have h := integral_entropy_prod_left ν μ (g ∘ Prod.swap) hlog.swap hmargy
  have hswap : (∫ p : β × α, g p.swap * Real.log (g p.swap) ∂(ν.prod μ)) =
      ∫ p : α × β, g p * Real.log (g p) ∂(μ.prod ν) :=
    integral_prod_swap (fun p ↦ g p * Real.log (g p))
  simpa only [Function.comp_apply, Prod.swap_prod_mk, hswap] using h

private theorem integral_mul_comp_snd_eq {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] (g : α × β → ℝ) (w : β → ℝ)
    (h : Integrable (fun p ↦ g p * w p.2) (μ.prod ν)) :
    (∫ p, g p * w p.2 ∂(μ.prod ν)) =
      ∫ y, (∫ x, g (x, y) ∂μ) * w y ∂ν := by
  rw [integral_prod_symm _ h]
  apply integral_congr_ae
  filter_upwards with y
  exact integral_mul_const (μ := μ) (w y) (fun x : α ↦ g (x, y))

/-- The split-log form of the integral log-sum inequality, including zero total masses. -/
private theorem integral_log_sum_split_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f h : α → ℝ} (hf : 0 ≤ᵐ[μ] f) (hh : 0 ≤ᵐ[μ] h)
    (hzero : ∀ᵐ x ∂μ, h x = 0 → f x = 0)
    (hfi : Integrable f μ) (hhi : Integrable h μ)
    (hdiff : Integrable (fun x ↦ f x * Real.log (f x) - f x * Real.log (h x)) μ) :
    (∫ x, f x ∂μ) * Real.log (∫ x, f x ∂μ) -
        (∫ x, f x ∂μ) * Real.log (∫ x, h x ∂μ) ≤
      ∫ x, f x * Real.log (f x) - f x * Real.log (h x) ∂μ := by
  have hsum := integral_log_sum_le μ hf hh hzero hfi hhi hdiff
  have hBzero : (∫ x, h x ∂μ) = 0 → (∫ x, f x ∂μ) = 0 := by
    intro hB
    have hhzero : h =ᵐ[μ] fun _ ↦ 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hh hhi).mp hB
    have hfzero : f =ᵐ[μ] fun _ ↦ 0 := by
      filter_upwards [hzero, hhzero] with x hx hhx
      exact hx hhx
    rw [integral_congr_ae hfzero]
    simp
  rw [← Real.mul_log_div _ _ hBzero]
  exact hsum

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
  have hb : 0 ≤ᵐ[ν] b := μ.ae_nonneg_integral_prod_right ν hnonneg
  have hpoint : ∀ᵐ x ∂μ, a x * Real.log (a x) - a x * Real.log m ≤
      ∫ y, g (x, y) * Real.log (g (x, y)) - g (x, y) * Real.log (b y) ∂ν := by
    filter_upwards [ae_ae_of_ae_prod hnonneg, hg.prod_right_ae,
      hlog.prod_right_ae, hcross.prod_right_ae, hzero] with x hx hxi hli hci hz
    have h := integral_log_sum_split_le ν hx hb hz hxi hbi (hli.sub hci)
    rw [hbm] at h
    simpa only [a, b] using h
  have hleft := hmargx.sub (hai.mul_const (Real.log m))
  have hright := (hlog.sub hcross).integral_prod_left
  have hint := integral_mono_ae hleft hright hpoint
  have hcross_eq : (∫ p, g p * Real.log (b p.2) ∂(μ.prod ν)) =
      ∫ y, b y * Real.log (b y) ∂ν :=
    integral_mul_comp_snd_eq μ ν g (fun y ↦ Real.log (b y)) hcross
  have hint' : (∫ x, a x * Real.log (a x) - a x * Real.log m ∂μ) ≤
      ∫ x, ∫ y, g (x, y) * Real.log (g (x, y)) -
        g (x, y) * Real.log (b y) ∂ν ∂μ := by
    simpa only [Pi.sub_apply] using hint
  have hleft_eq : (∫ x, a x * Real.log (a x) - a x * Real.log m ∂μ) =
      (∫ x, a x * Real.log (a x) ∂μ) - m * Real.log m := by
    rw [integral_sub hmargx (hai.mul_const _), integral_mul_const, ham]
  have hright_eq : (∫ x, ∫ y, g (x, y) * Real.log (g (x, y)) -
      g (x, y) * Real.log (b y) ∂ν ∂μ) =
      (∫ p, g p * Real.log (g p) ∂(μ.prod ν)) -
        ∫ y, b y * Real.log (b y) ∂ν := by
    have hfubini : (∫ x, ∫ y, g (x, y) * Real.log (g (x, y)) -
        g (x, y) * Real.log (b y) ∂ν ∂μ) =
        ∫ p, g p * Real.log (g p) - g p * Real.log (b p.2) ∂(μ.prod ν) := by
      simpa only [Pi.sub_apply] using (integral_prod _ (hlog.sub hcross)).symm
    rw [hfubini, integral_sub hlog hcross, hcross_eq]
  rw [hleft_eq, hright_eq] at hint'
  rw [entropy_def, ham]
  rw [integral_entropy_prod_right μ ν g hlog hmargy]
  exact hint'

/-- Entropy is convex under unnormalized mixtures for an a.e. nonnegative function and s-finite
measures, including when its total mass is zero. Both sides integrate against `ν` without
dividing by its mass. The function and its `x log x` transform must be integrable on the product,
and both marginal `x log x` transforms must be integrable. -/
theorem entropy_integral_le_integral_entropy_of_integrable_marginals_mul_log {α β : Type*}
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
    hmargy (μ.integrable_mul_comp_snd_of_integrable_marginal_mul ν hnonneg
      hg.aestronglyMeasurable hg.prod_left_ae hweight hmargy)
    (ae_ae_of_ae_prod (μ.ae_eq_zero_of_marginal_right_eq_zero ν hnonneg
      hg.aestronglyMeasurable hg.prod_left_ae))

/-- Product entropy subadditivity for an a.e. nonnegative function when the function and its
`x log x` transform are integrable on the product, and both marginal transforms are integrable. -/
theorem entropy_prod_le_of_integrable_marginals_mul_log {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
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
  have h := entropy_integral_le_integral_entropy_of_integrable_marginals_mul_log
    μ ν g hnonneg hg hlog hmargx hmargy
  linarith

/-- Entropy is convex when integrating sections of an a.e. nonnegative function against `ν`,
with the reference measure `μ` fixed. Both sides integrate against `ν` without dividing by its
mass. Both measures are finite and the function and its `x log x` transform are integrable. -/
theorem entropy_integral_le_integral_entropy {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (g : α × β → ℝ)
    (hnonneg : 0 ≤ᵐ[μ.prod ν] g)
    (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    entropy μ (fun x ↦ ∫ y, g (x, y) ∂ν) ≤
      ∫ y, entropy μ (fun x ↦ g (x, y)) ∂ν := by
  exact entropy_integral_le_integral_entropy_of_integrable_marginals_mul_log μ ν g hnonneg hg hlog
    (integrable_marginal_mul_log_left μ ν hg hlog)
    (integrable_marginal_mul_log_right μ ν hg hlog)

/-- Product entropy subadditivity for an a.e. nonnegative function under finite measures,
assuming integrability of the function and its `x log x` transform. -/
theorem entropy_prod_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (g : α × β → ℝ) (hnonneg : 0 ≤ᵐ[μ.prod ν] g)
    (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    entropy (μ.prod ν) g ≤
      (∫ x, entropy ν (fun y ↦ g (x, y)) ∂μ) +
        ∫ y, entropy μ (fun x ↦ g (x, y)) ∂ν :=
  entropy_prod_le_of_integrable_marginals_mul_log μ ν g hnonneg hg hlog
    (integrable_marginal_mul_log_left μ ν hg hlog)
    (integrable_marginal_mul_log_right μ ν hg hlog)

end MeasureTheory.Measure

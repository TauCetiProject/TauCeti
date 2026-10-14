/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Function.Lp.Translation
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# `L¹` continuity of kernel potentials

An integrable kernel translated by a measurable family of shifts can be integrated against
integrable weights. Almost everywhere convergence of the shifts and `L¹` convergence of the
weights imply `L¹` convergence of these potentials. A quantitative estimate separates the weight
error from the kernel translation error.
-/

public section

open Filter
open scoped Topology

namespace MeasureTheory
namespace Integrable

variable {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
  {ν : Measure G} [ν.IsAddRightInvariant] [SFinite ν]
  [IsLocallyFiniteMeasure ν] [ν.InnerRegularCompactLTTop]

section Potential
variable {K : Type*} [NormedRing K] [MeasurableSpace K] [BorelSpace K]
  [SecondCountableTopology K]
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
variable {k : G → K}

omit [SFinite μ] [IsLocallyFiniteMeasure ν]
  [ν.InnerRegularCompactLTTop] in
/-- An integrable kernel with integrable weights and a.e.-measurable shifts gives a jointly
integrable function `(t, z) ↦ k (z - c t) * v t` for the product measure. -/
theorem integrable_prod_comp_sub_mul (hk : Integrable k ν) (hmk : Measurable k)
    {c : α → G} {v : α → K} (hc : AEMeasurable c μ)
    (hv : Integrable v μ) :
    Integrable (fun p : α × G ↦ k (p.2 - c p.1) * v p.1) (μ.prod ν) := by
  have hm : AEStronglyMeasurable (fun p : α × G ↦ k (p.2 - c p.1) * v p.1)
      (μ.prod ν) :=
    ((hmk.comp_aemeasurable (measurable_snd.aemeasurable.sub hc.comp_fst)).mul
      hv.aestronglyMeasurable.aemeasurable.comp_fst).aestronglyMeasurable
  have hi (t : α) : Integrable (fun z ↦ k (z - c t)) ν := hk.comp_sub_right (c t)
  apply (integrable_prod_iff hm).2
  constructor
  · exact Filter.Eventually.of_forall fun t ↦ (hi t).mul_const (v t)
  · apply (hv.norm.const_mul (∫ z : G, ‖k z‖ ∂ν)).mono' hm.norm.integral_prod_right'
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
    calc
      _ ≤ ∫ z : G, ‖k (z - c t)‖ * ‖v t‖ ∂ν :=
        integral_mono ((hi t).mul_const (v t)).norm ((hi t).norm.mul_const ‖v t‖)
          (fun z ↦ norm_mul_le _ _)
      _ = (∫ z : G, ‖k z‖ ∂ν) * ‖v t‖ := by
        rw [integral_mul_const, integral_sub_right_eq_self (fun z : G ↦ ‖k z‖)]
omit [IsLocallyFiniteMeasure ν] [ν.InnerRegularCompactLTTop] in
/-- An integrable kernel with integrable weights and measurable shifts has an integrable
weighted potential after integrating over the shifts. -/
theorem integral_comp_sub_mul [NormedSpace ℝ K] (hk : Integrable k ν) (hmk : Measurable k)
    {c : α → G} {v : α → K} (hc : AEMeasurable c μ) (hv : Integrable v μ) :
    Integrable (fun z ↦ ∫ t, k (z - c t) * v t ∂μ) ν :=
  (hk.integrable_prod_comp_sub_mul hmk hc hv).integral_prod_right

end Potential

section Weighted
variable {K V : Type*} [NormedAddCommGroup K] [NormedAddCommGroup V]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
variable {k : G → K}

omit [SecondCountableTopology K] [MeasurableSub₂ G]
  [MeasurableSpace K] [BorelSpace K] [SFinite ν]
  [IsLocallyFiniteMeasure ν] [ν.InnerRegularCompactLTTop] in
/-- The `L¹` distance between two translates is at most twice the kernel's `L¹` norm. -/
theorem integral_norm_kernel_translation_sub_le (hk : Integrable k ν) (a b : G) :
    (∫ z : G, ‖k (z - a) - k (z - b)‖ ∂ν) ≤ 2 * ∫ z : G, ‖k z‖ ∂ν := by
  have hi (c : G) : Integrable (fun z ↦ k (z - c)) ν := hk.comp_sub_right c
  calc
    (∫ z : G, ‖k (z - a) - k (z - b)‖ ∂ν) ≤ ∫ z : G, ‖k (z - a)‖ + ‖k (z - b)‖ ∂ν :=
      integral_mono ((hi a).sub (hi b)).norm ((hi a).norm.add (hi b).norm)
        (fun z ↦ norm_sub_le _ _)
    _ = 2 * ∫ z : G, ‖k z‖ ∂ν := by
      rw [integral_add (hi a).norm (hi b).norm]
      rw [integral_sub_right_eq_self (fun z : G ↦ ‖k z‖),
        integral_sub_right_eq_self (fun z : G ↦ ‖k z‖)]
      ring

omit [SecondCountableTopology K] [MeasurableSub₂ G]
  [MeasurableSpace K] [BorelSpace K] [SFinite ν]
  [IsLocallyFiniteMeasure ν] [ν.InnerRegularCompactLTTop] in
private theorem norm_weighted_kernel_translation_sub_le (hk : Integrable k ν)
    (a b : G) (v : V) :
    ‖(∫ z : G, ‖k (z - a) - k (z - b)‖ ∂ν) * ‖v‖‖ ≤
      (2 * ∫ z : G, ‖k z‖ ∂ν) * ‖v‖ := by
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right (hk.integral_norm_kernel_translation_sub_le a b)
    (norm_nonneg _)

omit [SFinite μ] [IsLocallyFiniteMeasure ν]
  [ν.InnerRegularCompactLTTop] in
/-- The translation error weighted by an integrable function is integrable. -/
theorem integrable_integral_norm_comp_sub_sub_mul_norm (hk : Integrable k ν) (hmk : Measurable k)
    {a b : α → G} {v : α → V} (ha : AEMeasurable a μ) (hb : AEMeasurable b μ)
    (hv : Integrable v μ) :
    Integrable (fun t ↦ (∫ z : G, ‖k (z - a t) - k (z - b t)‖ ∂ν) * ‖v t‖) μ := by
  have hm : AEStronglyMeasurable
      (fun t ↦ (∫ z : G, ‖k (z - a t) - k (z - b t)‖ ∂ν) * ‖v t‖) μ := by
    have hprod : AEStronglyMeasurable
        (fun p : α × G ↦ ‖k (p.2 - a p.1) - k (p.2 - b p.1)‖) (μ.prod ν) :=
      ((hmk.comp_aemeasurable (measurable_snd.aemeasurable.sub ha.comp_fst)).sub
        (hmk.comp_aemeasurable
          (measurable_snd.aemeasurable.sub hb.comp_fst))).norm.aestronglyMeasurable
    exact hprod.integral_prod_right'.mul hv.aestronglyMeasurable.norm
  apply (hv.norm.const_mul (2 * ∫ z : G, ‖k z‖ ∂ν)).mono' hm
  filter_upwards with t
  exact norm_weighted_kernel_translation_sub_le hk (a t) (b t) (v t)

omit [SFinite μ] in
/-- Almost everywhere convergence of shifts gives weighted `L¹` translation convergence. -/
theorem tendsto_integral_weighted_kernel_translation_sub (hk : Integrable k ν) (hmk : Measurable k)
    {cn : ℕ → α → G} {c : α → G} {v : α → V} (hcn : ∀ n, AEMeasurable (cn n) μ)
    (hc : AEMeasurable c μ) (hv : Integrable v μ)
    (hlim : ∀ᵐ t ∂μ, Tendsto (fun n ↦ cn n t) atTop (𝓝 (c t))) :
    Tendsto (fun n ↦ ∫ t, (∫ z : G, ‖k (z - cn n t) - k (z - c t)‖ ∂ν) * ‖v t‖ ∂μ)
      atTop (𝓝 0) := by
  have hm (n : ℕ) :=
    (integrable_integral_norm_comp_sub_sub_mul_norm hk hmk (hcn n) hc hv).aestronglyMeasurable
  have hpointwise : ∀ᵐ t ∂μ, Tendsto
      (fun n ↦ (∫ z : G, ‖k (z - cn n t) - k (z - c t)‖ ∂ν) * ‖v t‖)
      atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hlim] with t ht
    simpa using (hk.tendsto_integral_norm_translate_sub ht).mul_const ‖v t‖
  have h := tendsto_integral_of_dominated_convergence
    (fun t ↦ (2 * ∫ z : G, ‖k z‖ ∂ν) * ‖v t‖) hm (hv.norm.const_mul _)
    (fun n ↦ Filter.Eventually.of_forall fun t ↦
      norm_weighted_kernel_translation_sub_le hk (cn n t) (c t) (v t)) hpointwise
  simpa using h
end Weighted

section Fixed
variable {K : Type*} [NormedRing K]

omit [MeasurableSub₂ G] [SFinite ν]
  [IsLocallyFiniteMeasure ν] [ν.InnerRegularCompactLTTop] in
/-- For fixed shifts and weights, split the product difference into a weight error and a
translation error, retaining the exact `L¹` constants. -/
theorem integral_norm_translated_kernel_mul_sub_le {k : G → K}
    (hk : Integrable k ν) (a b : G) (u v : K) :
    (∫ z : G, ‖k (z - a) * u - k (z - b) * v‖ ∂ν) ≤
      (∫ z : G, ‖k z‖ ∂ν) * ‖u - v‖ +
        (∫ z : G, ‖k (z - a) - k (z - b)‖ ∂ν) * ‖v‖ := by
  have hi (c : G) : Integrable (fun z ↦ k (z - c)) ν := hk.comp_sub_right c
  have hu : Integrable (fun z ↦ ‖k (z - a)‖ * ‖u - v‖) ν :=
    (hi a).norm.mul_const ‖u - v‖
  have hv : Integrable (fun z ↦ ‖k (z - a) - k (z - b)‖ * ‖v‖) ν := by
    simpa only [Pi.sub_apply] using ((hi a).sub (hi b)).norm.mul_const ‖v‖
  calc
    _ ≤ ∫ z : G, ‖k (z - a)‖ * ‖u - v‖ + ‖k (z - a) - k (z - b)‖ * ‖v‖ ∂ν := by
      apply integral_mono (((hi a).mul_const u).sub ((hi b).mul_const v)).norm (hu.add hv)
      intro z
      have he : k (z - a) * u - k (z - b) * v =
          k (z - a) * (u - v) + (k (z - a) - k (z - b)) * v := by
        rw [mul_sub, sub_mul]
        abel
      simp only [Pi.sub_apply, Pi.add_apply]
      rw [he]
      exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ = _ := by
      rw [integral_add hu hv]
      simp_rw [integral_mul_const]
      rw [integral_sub_right_eq_self (fun z : G ↦ ‖k z‖)]

end Fixed

section Estimate
variable {K : Type*} [NormedRing K] [NormedSpace ℝ K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
variable {k : G → K}

omit [IsLocallyFiniteMeasure ν] [ν.InnerRegularCompactLTTop] in
/-- A kernel potential difference is bounded by the weight discrepancy and a translation error. -/
theorem integral_norm_kernel_potential_sub_le (hk : Integrable k ν) (hmk : Measurable k)
    {a b : α → G} {u v : α → K} (ha : AEMeasurable a μ) (hb : AEMeasurable b μ)
    (hu : Integrable u μ) (hv : Integrable v μ) :
    (∫ z : G, ‖(∫ t, k (z - a t) * u t ∂μ) - (∫ t, k (z - b t) * v t ∂μ)‖ ∂ν) ≤
      (∫ z : G, ‖k z‖ ∂ν) * (∫ t, ‖u t - v t‖ ∂μ) +
      ∫ t, (∫ z : G, ‖k (z - a t) - k (z - b t)‖ ∂ν) * ‖v t‖ ∂μ := by
  have hA := integrable_prod_comp_sub_mul hk hmk ha hu
  have hB := integrable_prod_comp_sub_mul hk hmk hb hv
  have hD := hA.sub hB
  have hweighted := integrable_integral_norm_comp_sub_sub_mul_norm hk hmk ha hb hv
  have hweight : Integrable (fun t ↦ (∫ z : G, ‖k z‖ ∂ν) * ‖u t - v t‖) μ := by
    simpa only [Pi.sub_apply] using (hu.sub hv).norm.const_mul (∫ z : G, ‖k z‖ ∂ν)
  calc
    -- Minkowski moves the norm inside the parameter integral.
    _ ≤ ∫ z : G, ∫ t, ‖k (z - a t) * u t - k (z - b t) * v t‖ ∂μ ∂ν := by
      apply integral_mono_ae
      · exact (hA.swap.integral_prod_left.sub hB.swap.integral_prod_left).norm
      · exact hD.integral_norm_prod_right
      · filter_upwards [hA.prod_left_ae, hB.prod_left_ae] with z hzA hzB
        rw [← integral_sub hzA hzB]
        exact norm_integral_le_integral_norm _
    -- Fubini makes the fixed-shift estimate available pointwise in the parameter.
    _ = ∫ t, (∫ z : G, ‖k (z - a t) * u t - k (z - b t) * v t‖ ∂ν) ∂μ :=
      integral_integral_swap hD.swap.norm
    -- Separate the weight discrepancy from the kernel translation error.
    _ ≤ ∫ t, (∫ z : G, ‖k z‖ ∂ν) * ‖u t - v t‖ +
        (∫ z : G, ‖k (z - a t) - k (z - b t)‖ ∂ν) * ‖v t‖ ∂μ :=
      integral_mono hD.integral_norm_prod_left (hweight.add hweighted)
        (fun t ↦ integral_norm_translated_kernel_mul_sub_le hk (a t) (b t) (u t) (v t))
    _ = _ := by rw [integral_add hweight hweighted, integral_const_mul]
/-- Almost everywhere convergence of shifts and `L¹` convergence of weights give `L¹`
convergence of the corresponding kernel potentials. -/
theorem tendsto_integral_norm_kernel_potential_sub
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {k : G → K} (hk : Integrable k ν) (hmk : Measurable k)
    {cn : ℕ → α → G} {vn : ℕ → α → K} {c : α → G} {v : α → K}
    (hcn : ∀ n, AEMeasurable (cn n) μ) (hc : AEMeasurable c μ)
    (hvn : ∀ n, Integrable (vn n) μ) (hv : Integrable v μ)
    (hclim : ∀ᵐ t ∂μ, Tendsto (fun n ↦ cn n t) atTop (𝓝 (c t)))
    (hvlim : Tendsto (fun n ↦ ∫ t, ‖vn n t - v t‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ z : G,
      ‖(∫ t, k (z - cn n t) * vn n t ∂μ) - (∫ t, k (z - c t) * v t ∂μ)‖ ∂ν)
      atTop (𝓝 0) := by
  have hbound := (hvlim.const_mul (∫ z : G, ‖k z‖ ∂ν)).add
    (tendsto_integral_weighted_kernel_translation_sub hk hmk hcn hc hv hclim)
  apply squeeze_zero (fun n ↦ integral_nonneg (fun _ ↦ norm_nonneg _))
    (fun n ↦ integral_norm_kernel_potential_sub_le hk hmk (hcn n) hc (hvn n) hv)
  simpa using hbound

end Estimate

end Integrable
end MeasureTheory

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Function.LpSpace.Translation
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
variable {G K : Type*} [NormedAddCommGroup G] [NormedField K] [NormedSpace ℝ K]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace K] [BorelSpace K]
  [MeasurableSub₂ G] [SecondCountableTopology K]
  {ν : Measure G} [ν.IsAddRightInvariant] [SFinite ν]
  [IsLocallyFiniteMeasure ν] [ν.InnerRegularCompactLTTop]

section Potential
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
variable {k : G → K}

omit [SFinite μ] [NormedSpace ℝ K] [IsLocallyFiniteMeasure ν]
  [ν.InnerRegularCompactLTTop] in
/-- Integrating an integrable kernel against integrable weights gives an integrable product. -/
theorem integrable_translatedKernel_mul (hk : Integrable k ν) (hmk : Measurable k)
    {c : α → G} {v : α → K} (hc : AEMeasurable c μ)
    (hv : Integrable v μ) :
    Integrable (fun p : α × G ↦ k (p.2 - c p.1) * v p.1) (μ.prod ν) := by
  have hm : AEStronglyMeasurable (fun p : α × G ↦ k (p.2 - c p.1) * v p.1)
      (μ.prod ν) :=
    ((hmk.comp_aemeasurable (measurable_snd.aemeasurable.sub hc.comp_fst)).mul
      hv.aestronglyMeasurable.aemeasurable.comp_fst).aestronglyMeasurable
  apply (integrable_prod_iff hm).2
  constructor
  · exact Filter.Eventually.of_forall fun t ↦
      (((measurePreserving_sub_right ν (c t)).integrable_comp
        hk.aestronglyMeasurable).2 hk).mul_const (v t)
  · have heq : (fun t ↦ ∫ z : G, ‖k (z - c t) * v t‖ ∂ν) =
        fun t ↦ (∫ z : G, ‖k z‖ ∂ν) * ‖v t‖ := by
      funext t
      simp_rw [norm_mul, integral_mul_const]
      rw [integral_sub_right_eq_self (fun z : G ↦ ‖k z‖)]
    rw [heq]
    exact hv.norm.const_mul _
end Potential

section Weighted
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
variable {k : G → K}

omit [NormedSpace ℝ K] [SecondCountableTopology K] [MeasurableSub₂ G]
  [MeasurableSpace K] [BorelSpace K] [SFinite ν]
  [IsLocallyFiniteMeasure ν] [ν.InnerRegularCompactLTTop] in
/-- The `L¹` distance between two translates is at most twice the kernel's `L¹` norm. -/
theorem integral_norm_kernelTranslation_sub_le (hk : Integrable k ν) (a b : G) :
    (∫ z : G, ‖k (z - a) - k (z - b)‖ ∂ν) ≤ 2 * ∫ z : G, ‖k z‖ ∂ν := by
  have hi (c : G) : Integrable (fun z ↦ k (z - c)) ν :=
    ((measurePreserving_sub_right ν c).integrable_comp hk.aestronglyMeasurable).2 hk
  calc
    (∫ z : G, ‖k (z - a) - k (z - b)‖ ∂ν) ≤ ∫ z : G, ‖k (z - a)‖ + ‖k (z - b)‖ ∂ν :=
      integral_mono ((hi a).sub (hi b)).norm ((hi a).norm.add (hi b).norm)
        (fun z ↦ norm_sub_le _ _)
    _ = 2 * ∫ z : G, ‖k z‖ ∂ν := by
      rw [integral_add (hi a).norm (hi b).norm]
      rw [integral_sub_right_eq_self (fun z : G ↦ ‖k z‖),
        integral_sub_right_eq_self (fun z : G ↦ ‖k z‖)]
      ring

omit [SFinite μ] [NormedSpace ℝ K] in
/-- Almost everywhere convergence of shifts gives weighted `L¹` translation convergence. -/
theorem tendsto_integral_weightedKernelTranslation_sub (hk : Integrable k ν) (hmk : Measurable k)
    {cn : ℕ → α → G} {c : α → G} {v : α → K} (hcn : ∀ n, AEMeasurable (cn n) μ)
    (hc : AEMeasurable c μ) (hv : Integrable v μ)
    (hlim : ∀ᵐ t ∂μ, Tendsto (fun n ↦ cn n t) atTop (𝓝 (c t))) :
    Tendsto (fun n ↦ ∫ t, (∫ z : G, ‖k (z - cn n t) - k (z - c t)‖ ∂ν) * ‖v t‖ ∂μ)
      atTop (𝓝 0) := by
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun t ↦ (∫ z : G, ‖k (z - cn n t) - k (z - c t)‖ ∂ν) * ‖v t‖) μ := by
    have hprod : AEStronglyMeasurable
        (fun p : α × G ↦ ‖k (p.2 - cn n p.1) - k (p.2 - c p.1)‖) (μ.prod ν) :=
      ((hmk.comp_aemeasurable (measurable_snd.aemeasurable.sub (hcn n).comp_fst)).sub
        (hmk.comp_aemeasurable
          (measurable_snd.aemeasurable.sub hc.comp_fst))).norm.aestronglyMeasurable
    exact hprod.integral_prod_right'.mul hv.aestronglyMeasurable.norm
  have h := tendsto_integral_of_dominated_convergence
    (fun t ↦ (2 * ∫ z : G, ‖k z‖ ∂ν) * ‖v t‖) hm (hv.norm.const_mul _)
    (fun n ↦ Filter.Eventually.of_forall fun t ↦ ?_)
    (show ∀ᵐ t ∂μ, Tendsto
      (fun n ↦ (∫ z : G, ‖k (z - cn n t) - k (z - c t)‖ ∂ν) * ‖v t‖) atTop (𝓝 (0 : ℝ)) from ?_)
  · simpa using h
  · rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _)) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_right (integral_norm_kernelTranslation_sub_le hk _ _) (norm_nonneg _)
  · filter_upwards [hlim] with t ht
    simpa using (hk.tendsto_integral_norm_translate_sub ht).mul_const ‖v t‖
end Weighted

section Estimate
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
variable {k : G → K}

omit [IsLocallyFiniteMeasure ν] [ν.InnerRegularCompactLTTop] in
/-- A kernel potential difference is bounded by the weight discrepancy and a translation error. -/
theorem integral_norm_kernelPotential_sub_le (hk : Integrable k ν) (hmk : Measurable k)
    {a b : α → G} {u v : α → K} (ha : AEMeasurable a μ) (hb : AEMeasurable b μ)
    (hu : Integrable u μ) (hv : Integrable v μ) :
    (∫ z : G, ‖(∫ t, k (z - a t) * u t ∂μ) - (∫ t, k (z - b t) * v t ∂μ)‖ ∂ν) ≤
      (∫ z : G, ‖k z‖ ∂ν) * (∫ t, ‖u t - v t‖ ∂μ) +
      ∫ t, (∫ z : G, ‖k (z - a t) - k (z - b t)‖ ∂ν) * ‖v t‖ ∂μ := by
  have hA := integrable_translatedKernel_mul hk hmk ha hu
  have hB := integrable_translatedKernel_mul hk hmk hb hv
  have hD := hA.sub hB
  have hF := (integrable_translatedKernel_mul hk hmk ha hv).sub
    (integrable_translatedKernel_mul hk hmk hb hv)
  have hi (c : G) : Integrable (fun z ↦ k (z - c)) ν :=
    ((measurePreserving_sub_right ν c).integrable_comp hk.aestronglyMeasurable).2 hk
  have hnorm : Integrable (fun t ↦ (∫ z : G, ‖k z‖ ∂ν) * ‖u t - v t‖ +
      (∫ z : G, ‖k (z - a t) - k (z - b t)‖ ∂ν) * ‖v t‖) μ := by
    have hf : (fun t ↦ ∫ z : G, ‖k (z - a t) * v t - k (z - b t) * v t‖ ∂ν) =
        fun t ↦ (∫ z : G, ‖k (z - a t) - k (z - b t)‖ ∂ν) * ‖v t‖ := by
      funext t
      simp_rw [← sub_mul, norm_mul, integral_mul_const]
    exact ((hu.sub hv).norm.const_mul _).add (hf ▸ hF.integral_norm_prod_left)
  calc
    _ ≤ ∫ z : G, ∫ t, ‖k (z - a t) * u t - k (z - b t) * v t‖ ∂μ ∂ν := by
      apply integral_mono_ae
      · exact (hA.swap.integral_prod_left.sub hB.swap.integral_prod_left).norm
      · exact hD.integral_norm_prod_right
      · filter_upwards [hA.prod_left_ae, hB.prod_left_ae] with z hzA hzB
        rw [← integral_sub hzA hzB]
        exact norm_integral_le_integral_norm _
    _ = ∫ t, (∫ z : G, ‖k (z - a t) * u t - k (z - b t) * v t‖ ∂ν) ∂μ :=
      integral_integral_swap hD.swap.norm
    _ ≤ ∫ t, (∫ z : G, ‖k z‖ ∂ν) * ‖u t - v t‖ +
        (∫ z : G, ‖k (z - a t) - k (z - b t)‖ ∂ν) * ‖v t‖ ∂μ := by
      apply integral_mono hD.integral_norm_prod_left hnorm
      intro t
      calc
        _ ≤ ∫ z : G, ‖k (z - a t) * (u t - v t)‖ +
            ‖(k (z - a t) - k (z - b t)) * v t‖ ∂ν := by
          apply integral_mono (((hi (a t)).mul_const (u t)).sub ((hi (b t)).mul_const (v t))).norm
            (((hi (a t)).mul_const (u t - v t)).norm.add
              (((hi (a t)).sub (hi (b t))).mul_const (v t)).norm)
          intro z
          have he : k (z - a t) * u t - k (z - b t) * v t =
              k (z - a t) * (u t - v t) + (k (z - a t) - k (z - b t)) * v t := by ring
          simp only [Pi.sub_apply, Pi.add_apply]
          rw [he]
          exact norm_add_le _ _
        _ = _ := by
          have hw : Integrable (fun z ↦ ‖(k (z - a t) - k (z - b t)) * v t‖) ν :=
            (((hi (a t)).sub (hi (b t))).mul_const (v t)).norm
          rw [integral_add (((hi (a t)).mul_const (u t - v t)).norm) hw]
          simp_rw [norm_mul, integral_mul_const]
          rw [integral_sub_right_eq_self (fun z : G ↦ ‖k z‖)]
    _ = _ := by
      have hweighted : Integrable
          (fun t ↦ (∫ z : G, ‖k (z - a t) - k (z - b t)‖ ∂ν) * ‖v t‖) μ := by
        convert hnorm.sub ((hu.sub hv).norm.const_mul (∫ z : G, ‖k z‖ ∂ν)) using 1
        funext t
        simp
      have huv : Integrable (fun t ↦ (∫ z : G, ‖k z‖ ∂ν) * ‖u t - v t‖) μ :=
        (hu.sub hv).norm.const_mul _
      rw [integral_add huv hweighted]
      rw [integral_const_mul]
end Estimate

/-- Almost everywhere convergence of shifts and `L¹` convergence of weights give `L¹`
convergence of the corresponding kernel potentials. -/
theorem tendsto_integral_norm_kernelPotential_sub
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
    (tendsto_integral_weightedKernelTranslation_sub hk hmk hcn hc hv hclim)
  apply squeeze_zero (fun n ↦ integral_nonneg (fun _ ↦ norm_nonneg _))
    (fun n ↦ integral_norm_kernelPotential_sub_le hk hmk (hcn n) hc (hvn n) hv)
  simpa using hbound

end MeasureTheory

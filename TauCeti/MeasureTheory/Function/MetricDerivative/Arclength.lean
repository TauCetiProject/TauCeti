/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.DerivComp
public import TauCeti.MeasureTheory.Function.MetricDerivative.ConstantSpeed
public import TauCeti.MeasureTheory.Function.MetricDerivative.Variation
public import TauCeti.Topology.MetricSpace.Arclength.Basic
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousSubstitution.Basic

/-!
# Metric speed, the derivative and the arclength factorization

Let `V` be a finite-dimensional real normed space and let `γ : ℝ → V` be absolutely continuous
on `[a, b]`. Its metric derivative is `‖γ'‖ₑ` almost everywhere on `[a, b]`, as for any curve of
bounded variation (`BoundedVariationOn.ae_metricDerivative_eq_enorm_deriv`). Write
`s(t) = variationOnFromTo γ (Icc a b) a t` for its cumulative arclength and
`c = naturalParameterization γ (Icc a b) a` for its unit-speed reparametrization, so that
`γ = c ∘ s` on `[a, b]` (`LocallyBoundedVariationOn.naturalParameterization_variationOnFromTo`).

* `s'(t) = ‖γ'(t)‖` at almost every `t ∈ [a, b]`
  (`AbsolutelyContinuousOnInterval.ae_deriv_variationOnFromTo_eq_norm_deriv`): the inequality
  `s' ≥ ‖γ'‖` holds pointwise almost everywhere, and both sides integrate to the length of `γ`.
* For almost every `t ∈ [a, b]` with `γ'(t) ≠ 0`, `c` is differentiable at `s(t)` with
  `‖c'(s(t))‖ = 1` and `γ'(t) = ‖γ'(t)‖ c'(s(t))`
  (`AbsolutelyContinuousOnInterval.ae_deriv_eq_norm_smul_deriv_naturalParameterization`). The
  chain rule for the monotone change of parameter `s` gives `γ' = s' · c' ∘ s` almost
  everywhere, and the times `t` with `s'(t) > 0` at which `s(t)` is a bad point of `c` form a null
  set, because the image under `s` of `s'(t) dt` on `[a, b]` is Lebesgue measure on the length
  interval.
* `γ(t) − γ(a) = ∫_0^{s(t)} c'` for every `t ∈ [a, b]`
  (`AbsolutelyContinuousOnInterval.sub_eq_integral_deriv_naturalParameterization`).

No inverse of `s` is used: `s` is constant where `γ` pauses.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows*, second edition, §1.1 (metric derivative
  and arclength reparametrization).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {γ : ℝ → F} {a b : ℝ}

namespace AbsolutelyContinuousOnInterval

/-- **The derivative of the arclength.** For a curve absolutely continuous on `[a, b]`, the
cumulative arclength `s(t) = variationOnFromTo γ (Icc a b) a t` has derivative `‖γ'(t)‖` at almost
every `t ∈ [a, b]`. -/
theorem ae_deriv_variationOnFromTo_eq_norm_deriv (hγ : AbsolutelyContinuousOnInterval γ a b) :
    ∀ᵐ t, t ∈ Icc a b → deriv (variationOnFromTo γ (Icc a b) a) t = ‖deriv γ t‖ := by
  rcases lt_or_ge b a with hba | hab
  · exact Eventually.of_forall fun t ht ↦ absurd (ht.1.trans ht.2) (not_le.2 hba)
  set s := variationOnFromTo γ (Icc a b) a
  have hBVu := hγ.boundedVariationOn
  have hs : AbsolutelyContinuousOnInterval s a b :=
    hγ.absolutelyContinuousOnInterval_variationOnFromTo_Icc
  have hmono : MonotoneOn s (Icc a b) := variationOnFromTo.monotoneOn
    (uIcc_of_le hab ▸ hBVu).locallyBoundedVariationOn (left_mem_Icc.2 hab)
  -- `‖γ'‖ ≤ s'` almost everywhere on `[a, b]`.
  have hle : ∀ᵐ t, t ∈ Ioc a b → ‖deriv γ t‖ ≤ deriv s t := by
    have h₁ := hBVu.ae_metricDerivative_le_enorm_deriv_variationOnFromTo
    have h₂ := hBVu.ae_metricDerivative_eq_enorm_deriv
    rw [uIcc_of_le hab] at h₁ h₂
    filter_upwards [h₁, h₂, volume.ae_ne b] with t ht₁ ht₂ htb hmem
    have hIoo : t ∈ Ioo a b := ⟨hmem.1, lt_of_le_of_ne hmem.2 htb⟩
    have hnn : 0 ≤ deriv s t := by
      rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hIoo.1 hIoo.2)]
      exact hmono.derivWithin_nonneg
    have h := (ht₂ (Ioc_subset_Icc_self hmem)).symm.trans_le (ht₁ (Ioc_subset_Icc_self hmem))
    rwa [eNorm_le_iff_norm_le, Real.norm_of_nonneg hnn] at h
  -- Both sides integrate to the length of `γ`.
  have hint : ∫ t in a..b, (deriv s t - ‖deriv γ t‖) = 0 := by
    have hsb : s b = (eVariationOn γ (Icc a b)).toReal :=
      variationOnFromTo.eq_toReal_eVariationOn_Icc _ _ _
    have hsa : s a = 0 := variationOnFromTo.self _ _ _
    rw [intervalIntegral.integral_sub hs.intervalIntegrable_deriv_of_finiteDimensional
      hγ.intervalIntegrable_deriv_of_finiteDimensional.norm,
      hs.integral_deriv_eq_sub_of_finiteDimensional,
      hγ.integral_norm_deriv_eq_eVariationOn_toReal hab,
      hsb, hsa, sub_zero, uIcc_of_le hab, sub_self]
  have hzero := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hab
    ((ae_restrict_iff' measurableSet_Ioc).2 (hle.mono fun t ht hmem ↦ sub_nonneg.2 (ht hmem)))
    (hs.intervalIntegrable_deriv_of_finiteDimensional.sub
      hγ.intervalIntegrable_deriv_of_finiteDimensional.norm)).1 hint
  filter_upwards [(ae_restrict_iff' measurableSet_Ioc).1 hzero, volume.ae_ne a] with t ht hta hmem
  exact sub_eq_zero.1 (ht ⟨lt_of_le_of_ne hmem.1 (Ne.symm hta), hmem.2⟩)

/-- **The arclength factorization of the derivative.** Let `γ` be absolutely continuous on
`[a, b]`, with cumulative arclength `s` and natural parameterization `c`. At almost every
`t ∈ [a, b]` with `γ'(t) ≠ 0`, `c` is differentiable at `s(t)`, `‖c'(s(t))‖ = 1` and
`γ'(t) = ‖γ'(t)‖ c'(s(t))`. -/
theorem ae_deriv_eq_norm_smul_deriv_naturalParameterization
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    ∀ᵐ t, t ∈ Icc a b → deriv γ t ≠ 0 →
      DifferentiableAt ℝ (naturalParameterization γ (Icc a b) a)
          (variationOnFromTo γ (Icc a b) a t) ∧
        ‖deriv (naturalParameterization γ (Icc a b) a) (variationOnFromTo γ (Icc a b) a t)‖ = 1 ∧
        deriv γ t = ‖deriv γ t‖ •
          deriv (naturalParameterization γ (Icc a b) a) (variationOnFromTo γ (Icc a b) a t) := by
  rcases lt_or_ge b a with hba | hab
  · exact Eventually.of_forall fun t ht ↦ absurd (ht.1.trans ht.2) (not_le.2 hba)
  set s := variationOnFromTo γ (Icc a b) a
  set c := naturalParameterization γ (Icc a b) a
  set L := (eVariationOn γ (Icc a b)).toReal
  have hBV := hγ.boundedVariationOn
  have hcont := hγ.continuousOn
  rw [uIcc_of_le hab] at hBV hcont
  have hs : AbsolutelyContinuousOnInterval s a b :=
    hγ.absolutelyContinuousOnInterval_variationOnFromTo_Icc
  have hc : AbsolutelyContinuousOnInterval c 0 L :=
    hBV.absolutelyContinuousOnInterval_naturalParameterization hcont hab
  have hmono : MonotoneOn s (Icc a b) :=
    variationOnFromTo.monotoneOn hBV.locallyBoundedVariationOn (left_mem_Icc.2 hab)
  have himage : s '' Icc a b = Icc 0 L := hBV.image_variationOnFromTo_Icc hcont hab
  have hmap : MapsTo s (Icc a b) (uIcc 0 L) := by
    rw [uIcc_of_le ENNReal.toReal_nonneg, ← himage]
    exact mapsTo_image _ _
  have hfac (t : ℝ) (ht : t ∈ Icc a b) : c (s t) = γ t :=
    hBV.locallyBoundedVariationOn.naturalParameterization_variationOnFromTo (left_mem_Icc.2 hab) ht
  -- The bad set of `c`: points where `c` is not differentiable with a unit derivative.
  set N := {u | ¬(DifferentiableAt ℝ c u ∧ ‖deriv c u‖ = 1)}
  have hN : volume.restrict (Icc (s a) (s b)) N = 0 := by
    have hu0 := hBV.hasUnitSpeedOn_naturalParameterization hcont hab
    rw [← uIcc_of_le ENNReal.toReal_nonneg] at hu0
    have hu := HasConstantSpeedOnWith.ae_norm_deriv_eq hu0
    rw [uIcc_of_le ENNReal.toReal_nonneg] at hu
    rw [show s a = 0 from variationOnFromTo.self _ _ _,
      show s b = L from variationOnFromTo.eq_toReal_eVariationOn_Icc _ _ _]
    refine measure_eq_zero_iff_ae_notMem.2 (hu.mono fun u hu hN ↦ hN ?_)
    exact ⟨hu.1, by exact_mod_cast hu.2⟩
  have hchain := hc.ae_hasDerivAt_comp_of_monotoneOn hs hab hmono hmap
  filter_upwards [hchain, hs.ae_notMem_of_deriv_ne_zero_of_monotoneOn hmono hN,
    hγ.ae_deriv_variationOnFromTo_eq_norm_deriv, volume.ae_ne a, volume.ae_ne b]
    with t hct hgt hst hta htb hmem hγt
  have hIoo : t ∈ Ioo a b := ⟨lt_of_le_of_ne hmem.1 (Ne.symm hta), lt_of_le_of_ne hmem.2 htb⟩
  -- `γ = c ∘ s` near `t`, so `γ'(t) = s'(t) c'(s(t))`.
  have hderiv : deriv γ t = deriv s t • deriv c (s t) := by
    refine ((hct (by rwa [uIcc_of_le hab])).congr_of_eventuallyEq ?_).deriv
    filter_upwards [Icc_mem_nhds hIoo.1 hIoo.2] with u hu
    exact (hfac u hu).symm
  have hgood : s t ∉ N := hgt hmem (by rw [hst hmem]; exact norm_ne_zero_iff.2 hγt)
  simp only [N, mem_ofPred_eq, not_not] at hgood
  exact ⟨hgood.1, hgood.2, hderiv.trans (by rw [hst hmem])⟩

/-- **The fundamental theorem of calculus for the arclength factorization.** For a curve `γ`
absolutely continuous on `[a, b]`, with cumulative arclength `s` and natural parameterization `c`,
`γ(t) − γ(a) = ∫_0^{s(t)} c'` for every `t ∈ [a, b]`. -/
theorem sub_eq_integral_deriv_naturalParameterization
    (hγ : AbsolutelyContinuousOnInterval γ a b) {t : ℝ} (ht : t ∈ Icc a b) :
    γ t - γ a = ∫ u in 0..variationOnFromTo γ (Icc a b) a t,
      deriv (naturalParameterization γ (Icc a b) a) u := by
  have hab := ht.1.trans ht.2
  have hBV := hγ.boundedVariationOn
  have hcont := hγ.continuousOn
  rw [uIcc_of_le hab] at hBV hcont
  have hc := hBV.absolutelyContinuousOnInterval_naturalParameterization hcont hab
  have hst : variationOnFromTo γ (Icc a b) a t ∈ Icc 0 (eVariationOn γ (Icc a b)).toReal := by
    rw [← hBV.image_variationOnFromTo_Icc hcont hab]
    exact mem_image_of_mem _ ht
  have hsub : uIcc 0 (variationOnFromTo γ (Icc a b) a t) ⊆
      uIcc 0 (eVariationOn γ (Icc a b)).toReal :=
    uIcc_subset_uIcc left_mem_uIcc (by rwa [uIcc_of_le ENNReal.toReal_nonneg])
  rw [(hc.mono hsub).integral_deriv_eq_sub_of_finiteDimensional,
    hBV.locallyBoundedVariationOn.naturalParameterization_variationOnFromTo (left_mem_Icc.2 hab) ht,
    hBV.locallyBoundedVariationOn.naturalParameterization_zero (left_mem_Icc.2 hab)]

end AbsolutelyContinuousOnInterval

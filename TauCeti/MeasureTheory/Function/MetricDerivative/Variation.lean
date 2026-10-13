/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.MetricDerivative.Basic
public import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Total variation and the metric speed of absolutely continuous curves

The total variation of an absolutely continuous metric-valued curve equals the integral of its
metric derivative. For curves in finite-dimensional real normed spaces this identifies total
variation with the integral of the norm of the canonical derivative.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace eVariationOn

/-- An integral density that controls distances along a curve also controls its total variation. -/
theorem le_lintegral_of_edist_le_lintegral {X : Type*} [PseudoEMetricSpace X]
    {γ : ℝ → X} {m : ℝ → ℝ≥0∞} {a b : ℝ}
    (h : ∀ s ∈ Icc a b, ∀ u ∈ Icc a b, edist (γ s) (γ u) ≤ ∫⁻ t in uIoc s u, m t) :
    eVariationOn γ (Icc a b) ≤ ∫⁻ t in Ioc a b, m t := by
  let L (s u : ℝ) := ∫⁻ t in Ioc s u, m t
  have hadd {s u v : ℝ} (hsu : s ≤ u) (huv : u ≤ v) : L s u + L u v = L s v := by
    dsimp [L]
    rw [← lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl),
      Ioc_union_Ioc_eq_Ioc hsu huv]
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  have hsegment (i : ℕ) : edist (γ (u (i + 1))) (γ (u i)) ≤ L (u i) (u (i + 1)) := by
    rw [edist_comm]
    simpa only [L, uIoc_of_le (hu (Nat.le_succ i))] using h _ (hus i) _ (hus (i + 1))
  have hsum (k : ℕ) : ∑ i ∈ Finset.range k, L (u i) (u (i + 1)) = L (u 0) (u k) := by
    induction k with
    | zero => simp [L]
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, hadd (hu (Nat.zero_le k)) (hu (Nat.le_succ k))]
  calc
    ∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i)) ≤
        ∑ i ∈ Finset.range n, L (u i) (u (i + 1)) := Finset.sum_le_sum fun i _ ↦ hsegment i
    _ = L (u 0) (u n) := hsum n
    _ ≤ ∫⁻ t in Ioc a b, m t := lintegral_mono_set (Ioc_subset_Ioc (hus 0).1 (hus n).2)

end eVariationOn

namespace AbsolutelyContinuousOnInterval

variable {X : Type*} [PseudoMetricSpace X] {γ : ℝ → X} {a b : ℝ}

/-- The integrated metric derivative of an absolutely continuous curve bounds its total
variation from above. -/
theorem eVariationOn_le_lintegral_metricDerivative (hγ : AbsolutelyContinuousOnInterval γ a b) :
    eVariationOn γ (uIcc a b) ≤ ∫⁻ t in uIoc a b, TauCeti.metricDerivative γ t := by
  rw [uIcc, uIoc]
  apply eVariationOn.le_lintegral_of_edist_le_lintegral
  exact fun s hs u hu ↦ hγ.edist_le_lintegral_metricDerivative hs hu

/-- The cumulative total variation of an absolutely continuous metric-valued curve is an
absolutely continuous real function. -/
theorem absolutelyContinuousOnInterval_variationOnFromTo
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    AbsolutelyContinuousOnInterval (variationOnFromTo γ (uIcc a b) a) a b := by
  have hBV := hγ.boundedVariationOn'
  have hcontrol {s u : ℝ} (hs : s ∈ uIcc a b) (hu : u ∈ uIcc a b) (hsu : s ≤ u) :
      edist (variationOnFromTo γ (uIcc a b) a s) (variationOnFromTo γ (uIcc a b) a u) ≤
        ∫⁻ t in uIoc s u, TauCeti.metricDerivative γ t := by
    rw [edist_comm, edist_eq_enorm_sub,
      variationOnFromTo.sub_right hBV.locallyBoundedVariationOn left_mem_uIcc hu hs,
      variationOnFromTo.eq_of_le _ _ hsu, Real.enorm_eq_ofReal ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal ((eVariationOn.mono _ inter_subset_left).trans_lt hBV.lt_top).ne]
    refine (eVariationOn.mono _ inter_subset_right).trans ?_
    simpa only [uIcc_of_le hsu] using
      (hγ.mono (uIcc_subset_uIcc hs hu)).eVariationOn_le_lintegral_metricDerivative
  apply TauCeti.absolutelyContinuousOnInterval_of_edist_le_lintegral
    hγ.lintegral_metricDerivative_lt_top.ne
  intro s hs u hu
  rcases le_total s u with hsu | hus
  · exact hcontrol hs hu hsu
  · rw [edist_comm, uIoc_comm]
    exact hcontrol hu hs hus

/-- Total variation of an absolutely continuous metric-valued curve is its integrated metric
speed, for either orientation of the parameter interval. -/
theorem eVariationOn_eq_lintegral_metricDerivative (hγ : AbsolutelyContinuousOnInterval γ a b) :
    eVariationOn γ (uIcc a b) = ∫⁻ t in uIoc a b, TauCeti.metricDerivative γ t := by
  wlog hab : a ≤ b
  · rw [uIcc_comm a b, uIoc_comm a b]
    exact this hγ.symm (le_of_not_ge hab)
  have hBV := hγ.boundedVariationOn'
  let V := variationOnFromTo γ (uIcc a b) a
  have hV : AbsolutelyContinuousOnInterval V a b :=
    hγ.absolutelyContinuousOnInterval_variationOnFromTo
  have hVmono : MonotoneOn V (uIcc a b) :=
    variationOnFromTo.monotoneOn hBV.locallyBoundedVariationOn left_mem_uIcc
  have hnonneg : ∀ᵐ t, t ∈ uIcc a b → 0 ≤ deriv V t := by
    filter_upwards [volume.ae_ne a, volume.ae_ne b] with t hta htb ht
    rw [← derivWithin_of_mem_nhds (TauCeti.uIcc_mem_nhds_of_ne ht hta htb)]
    exact hVmono.derivWithin_nonneg
  have hnonneg' : ∀ᵐ t ∂volume.restrict (uIoc a b), 0 ≤ deriv V t := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hnonneg] with t ht hmem
    exact ht (uIoc_subset_uIcc hmem)
  have hchange : V b - V a = (eVariationOn γ (uIcc a b)).toReal := by
    dsimp [V]
    rw [variationOnFromTo.self, sub_zero, variationOnFromTo.eq_of_le _ _ hab]
    simp only [uIcc_of_le hab, inter_self]
  have hnormIntegral : (∫⁻ t in uIoc a b, ‖deriv V t‖ₑ) = eVariationOn γ (uIcc a b) := by
    calc
      ∫⁻ t in uIoc a b, ‖deriv V t‖ₑ = ∫⁻ t in uIoc a b, ENNReal.ofReal (deriv V t) := by
        apply lintegral_congr_ae
        filter_upwards [hnonneg'] with t ht
        exact Real.enorm_eq_ofReal ht
      _ = ENNReal.ofReal (∫ t in a..b, deriv V t) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hV.intervalIntegrable_deriv.def' hnonneg',
          uIoc_of_le hab, ← intervalIntegral.integral_of_le hab]
      _ = eVariationOn γ (uIcc a b) := by
        rw [hV.integral_deriv_eq_sub, hchange, ENNReal.ofReal_toReal hBV]
  refine le_antisymm hγ.eVariationOn_le_lintegral_metricDerivative ?_
  rw [← hnormIntegral]
  apply lintegral_mono_ae
  rw [ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [hBV.ae_metricDerivative_le_enorm_deriv_variationOnFromTo] with t ht hmem
  exact ht (uIoc_subset_uIcc hmem)

section NormedSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {γ : ℝ → F}

/-- In a finite-dimensional real normed space, the total variation of an absolutely continuous
curve equals the integral of the norm of its canonical derivative. -/
theorem eVariationOn_eq_lintegral_enorm_deriv (hγ : AbsolutelyContinuousOnInterval γ a b) :
    eVariationOn γ (uIcc a b) = ∫⁻ t in uIoc a b, ‖deriv γ t‖ₑ := by
  rw [hγ.eVariationOn_eq_lintegral_metricDerivative]
  apply lintegral_congr_ae
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [hγ.boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with t ht hmem
  exact (ht (uIoc_subset_uIcc hmem)).hasDerivAt.metricDerivative_eq

/-- The real integrated speed of an absolutely continuous finite-dimensional curve is its total
variation converted to `ℝ`, on a nonnegative oriented parameter interval. -/
theorem integral_norm_deriv_eq_eVariationOn_toReal
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hab : a ≤ b) :
    ∫ t in a..b, ‖deriv γ t‖ = (eVariationOn γ (uIcc a b)).toReal := by
  calc
    ∫ t in a..b, ‖deriv γ t‖ = ∫ t in uIoc a b, ‖deriv γ t‖ := by
      rw [uIoc_of_le hab, intervalIntegral.integral_of_le hab]
    _ = (∫⁻ t in uIoc a b, ‖deriv γ t‖ₑ).toReal :=
      integral_norm_eq_lintegral_enorm
        hγ.intervalIntegrable_deriv_of_finiteDimensional.def'.aestronglyMeasurable
    _ = (eVariationOn γ (uIcc a b)).toReal :=
      congrArg ENNReal.toReal hγ.eVariationOn_eq_lintegral_enorm_deriv.symm

end NormedSpace

end AbsolutelyContinuousOnInterval

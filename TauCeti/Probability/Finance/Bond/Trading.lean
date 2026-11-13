/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.Bond.Basic
public import TauCeti.MeasureTheory.VectorMeasure.FiniteHorizon
public import TauCeti.MeasureTheory.VectorMeasure.WithDensity
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Pathwise integration against the money-market account

On a finite horizon with continuous short rate, the money-market account has bounded
variation. Its finite-horizon Stieltjes measure is exactly the signed measure with
Lebesgue density `r(t) β(t)`, and its variation has density `|r(t) β(t)|`.
Thus arbitrary bond holdings, not just simple holdings, gain the ordinary time integral
of their interest income. Rates and holdings may have either sign; no moment assumption
on a random holding is involved in these pathwise identities.

The measure is constructed using `BoundedVariationOn.vectorMeasureIcc`, so it has no
initial-time atom and uses no information outside the declared horizon. Integration uses
`MeasureTheory.VectorMeasure.integral_mul_withDensityᵥ`.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer,
  2004, §5.2.
-/

public section

noncomputable section

open MeasureTheory Real Set

namespace TauCeti.Finance

variable {r : ℝ → ℝ} {β₀ T : ℝ}

/-- A continuous short rate gives an absolutely continuous bond price on the horizon. -/
theorem absolutelyContinuousOnInterval_bondPrice (hr : ContinuousOn r (Icc 0 T))
    (hT : 0 ≤ T) (β₀ : ℝ) : AbsolutelyContinuousOnInterval (bondPrice r β₀) 0 T := by
  have hint : IntervalIntegrable (fun t ↦ r t * bondPrice r β₀ t) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
    exact (hr.mul (continuousOn_bondPrice hr β₀)).integrableOn_Icc
  have hprim := hint.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (left_mem_uIcc)
  have hshift : LipschitzWith 1 (fun x : ℝ ↦ β₀ + x) := by
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    simp
  refine (hshift.comp_absolutelyContinuousOnInterval hprim).congr ?_
  rw [uIcc_of_le hT]
  intro t ht
  rw [Function.comp_apply, integral_mul_bondPrice hr β₀ ⟨le_rfl, hT⟩ ht, bondPrice_zero]
  ring

/-- The bond has finite variation on every horizon where the short rate is continuous. -/
theorem boundedVariationOn_bondPrice (hr : ContinuousOn r (Icc 0 T)) (hT : 0 ≤ T)
    (β₀ : ℝ) : BoundedVariationOn (bondPrice r β₀) (Icc 0 T) := by
  simpa only [uIcc_of_le hT] using
    (absolutelyContinuousOnInterval_bondPrice hr hT β₀).boundedVariationOn

/-- The bond's Stieltjes measure on `(0,T]` is the signed measure with density `r β`.
In particular this identification does not require the interest rate to be nonnegative. -/
theorem vectorMeasureIcc_bondPrice (hr : ContinuousOn r (Icc 0 T)) (hT : 0 ≤ T)
    (β₀ : ℝ) :
    (boundedVariationOn_bondPrice hr hT β₀).vectorMeasureIcc hT =
      (volume.restrict (Ioc 0 T)).withDensityᵥ (fun t ↦ r t * bondPrice r β₀ t) := by
  have hint : IntegrableOn (fun t ↦ r t * bondPrice r β₀ t) (Ioc 0 T) :=
    (hr.mul (continuousOn_bondPrice hr β₀)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  symm
  apply ((boundedVariationOn_bondPrice hr hT β₀).eq_vectorMeasureIcc_iff hT
    (fun t ht ↦ (continuousOn_bondPrice hr β₀ t ht).mono
      (Icc_subset_Icc_left ht.1)) _).2
  constructor
  · ext s hs : 1
    rw [VectorMeasure.restrict_apply _ measurableSet_Ioc hs,
      withDensityᵥ_apply hint (hs.inter measurableSet_Ioc), withDensityᵥ_apply hint hs]
    rw [Measure.restrict_restrict_of_subset inter_subset_right,
      Measure.restrict_restrict hs]
  · intro t ht
    rw [withDensityᵥ_apply hint measurableSet_Ioc,
      Measure.restrict_restrict_of_subset (Ioc_subset_Ioc_right ht.2),
      ← intervalIntegral.integral_of_le ht.1, integral_mul_bondPrice hr β₀ ⟨le_rfl, hT⟩ ht]

/-- Absolute bond variation is integration against the absolute interest-income density. -/
theorem variation_vectorMeasureIcc_bondPrice (hr : ContinuousOn r (Icc 0 T))
    (hT : 0 ≤ T) (β₀ : ℝ) :
    ((boundedVariationOn_bondPrice hr hT β₀).vectorMeasureIcc hT).variation =
      (volume.restrict (Ioc 0 T)).withDensity (fun t ↦ ‖r t * bondPrice r β₀ t‖ₑ) := by
  have hint : IntegrableOn (fun t ↦ r t * bondPrice r β₀ t) (Ioc 0 T) :=
    (hr.mul (continuousOn_bondPrice hr β₀)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [vectorMeasureIcc_bondPrice hr hT, Measure.variation_withDensityᵥ hint]

/-- A bond holding is integrable exactly when its holding weighted by the absolute
interest-income density is Lebesgue integrable. No measurability outside `(0,T]` is needed. -/
theorem integrable_vectorMeasureIcc_bondPrice_iff (hr : ContinuousOn r (Icc 0 T))
    (hT : 0 ≤ T) (β₀ : ℝ) (b : ℝ → ℝ) :
    ((boundedVariationOn_bondPrice hr hT β₀).vectorMeasureIcc hT).Integrable b ↔
      IntegrableOn (fun t ↦ ‖r t * bondPrice r β₀ t‖ * b t) (Ioc 0 T) := by
  have hint : IntegrableOn (fun t ↦ r t * bondPrice r β₀ t) (Ioc 0 T) :=
    (hr.mul (continuousOn_bondPrice hr β₀)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [VectorMeasure.Integrable, variation_vectorMeasureIcc_bondPrice hr hT,
    integrable_withDensity_iff_integrable_smul₀' hint.aestronglyMeasurable.eNorm
      (ae_of_all _ fun _ ↦ eNorm_lt_top)]
  simp only [toReal_eNorm, smul_eq_mul, IntegrableOn]

/-- For any holding, integration against the bond's Stieltjes measure is the time integral
of its interest income. As usual, both integrals take the value zero when not integrable. -/
theorem integral_vectorMeasureIcc_bondPrice (hr : ContinuousOn r (Icc 0 T))
    (hT : 0 ≤ T) (β₀ : ℝ) (b : ℝ → ℝ) :
    ∫ᵛ t, b t ∂[ContinuousLinearMap.mul ℝ ℝ;
      (boundedVariationOn_bondPrice hr hT β₀).vectorMeasureIcc hT] =
      ∫ t in 0..T, b t * (r t * bondPrice r β₀ t) := by
  have hint : IntegrableOn (fun t ↦ r t * bondPrice r β₀ t) (Ioc 0 T) :=
    (hr.mul (continuousOn_bondPrice hr β₀)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [vectorMeasureIcc_bondPrice hr hT, VectorMeasure.integral_mul_withDensityᵥ hint,
    intervalIntegral.integral_of_le hT]

/-- The bond-gains formula up to any observation time uses the same full-horizon
Stieltjes measure. Holdings need not be simple or continuous. -/
theorem setIntegral_Ioc_vectorMeasureIcc_bondPrice (hr : ContinuousOn r (Icc 0 T))
    (hT : 0 ≤ T) (β₀ : ℝ) (b : ℝ → ℝ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∫ᵛ u in Ioc 0 t, b u ∂[ContinuousLinearMap.mul ℝ ℝ;
      (boundedVariationOn_bondPrice hr hT β₀).vectorMeasureIcc hT] =
      ∫ u in 0..t, b u * (r u * bondPrice r β₀ u) := by
  rw [BoundedVariationOn.vectorMeasureIcc_restrict_Ioc
    _ hT (fun u hu ↦ (continuousOn_bondPrice hr β₀ u hu).mono
      (Icc_subset_Icc_left hu.1)) ⟨le_rfl, hT⟩ ht ht.1]
  exact integral_vectorMeasureIcc_bondPrice (hr.mono (Icc_subset_Icc_right ht.2)) ht.1 β₀ b

/-- Simple-strategy bond gains agree with integration against the full-horizon
Stieltjes measure, including at every trading date. -/
theorem simpleGains_eq_setIntegral_vectorMeasureIcc_bondPrice {Ω : Type*}
    {τ : ℕ → ℝ} {n : ℕ} (hr : ContinuousOn r (Icc 0 T)) (hT : 0 ≤ T) (β₀ : ℝ)
    (hτ : MonotoneOn τ (Iic n)) (hτ₀ : 0 ≤ τ 0) (b : ℕ → Ω → ℝ) (ω : Ω)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    simpleGains τ n b (fun u _ ↦ bondPrice r β₀ u) t ω =
      ∫ᵛ u in Ioc 0 t, simpleHolding τ n b u ω ∂[ContinuousLinearMap.mul ℝ ℝ;
        (boundedVariationOn_bondPrice hr hT β₀).vectorMeasureIcc hT] := by
  rw [setIntegral_Ioc_vectorMeasureIcc_bondPrice hr hT β₀ _ ht]
  exact simpleGains_bondPrice (hr.mono (Icc_subset_Icc_right ht.2)) β₀ hτ hτ₀ b ω

end TauCeti.Finance

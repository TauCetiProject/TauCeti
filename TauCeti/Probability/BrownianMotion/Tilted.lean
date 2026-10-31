/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.ExponentialMartingale
import TauCeti.Probability.Distributions.Tilted
import Mathlib.Probability.Independence.Integration

/-!
# Brownian increments under a terminal exponential tilt

Let `W` be Brownian relative to a filtration `ℱ`. Under the probability measure
`Q = P.tilted (θ * W T ·)`, every increment `W t - W s`, for `s ≤ t ≤ T`, has law
`N(θ (t - s), t - s)` and is independent of `ℱ s`. Thus the increments of
`W t - θ t` are centered Gaussian and independent of the past on the whole finite horizon.
Taking `θ = -κ` gives the drift correction `W t + κ t`.

The transition formula on a past event is also exported. It uses the density at time `t`
and the independence under `P` to separate the past density from the increment density.
Exponential tilting of the scalar Gaussian identifies the latter factor. No assertion
about times beyond `T` is made.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991, §3.5.
* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  §5.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ}

/-- Under a terminal exponential tilt, the probability of an increment event and an event
known at its starting time factors through the shifted Gaussian transition law. -/
theorem tilted_mul_eval_inter_preimage (hW : IsFilteredPreBrownianReal ℱ W P) (θ : ℝ)
    {s t T : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T)
    {A : Set Ω} (hA : MeasurableSet[ℱ s] A) {B : Set ℝ} (hB : MeasurableSet B) :
    P.tilted (fun ω ↦ θ * W T ω) (A ∩ (W t - W s) ⁻¹' B) =
      P.tilted (fun ω ↦ θ * W T ω) A *
        gaussianReal (θ * ((t : ℝ) - s)) (t - s) B := by
  classical
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let X := W t - W s
  let F := A.indicator (exponentialMartingale θ W s)
  let g := B.indicator (fun x : ℝ ↦ exp (θ * x - θ ^ 2 * ((t : ℝ) - s) / 2))
  have hX : Measurable[ℱ t] X := (hW.adapted t).sub ((hW.adapted s).mono (ℱ.mono hst) le_rfl)
  have hF : Measurable[ℱ s] F :=
    (hW.adapted.stronglyAdapted_exponentialMartingale θ s).measurable.indicator hA
  have hg : Measurable g := (by fun_prop : Measurable
    (fun x : ℝ ↦ exp (θ * x - θ ^ 2 * ((t : ℝ) - s) / 2))).indicator hB
  have hFG : IndepFun F (g ∘ X) P :=
    indep_of_indep_of_le (hW.indep_sub hst).symm hF.comap_le
      (hg.comp (comap_measurable X)).comap_le
  have hfactor := hFG.integral_fun_mul_eq_mul_integral
    (hF.mono (ℱ.le s) le_rfl).aestronglyMeasurable
    (hg.comp (hX.mono (ℱ.le t) le_rfl)).aestronglyMeasurable
  have hprod : (fun ω ↦ F ω * (g ∘ X) ω) =
      (A ∩ X ⁻¹' B).indicator (exponentialMartingale θ W t) := by
    ext ω
    by_cases ha : ω ∈ A <;> by_cases hb : X ω ∈ B <;>
      simp only [F, g, Function.comp_apply, indicator_apply, mem_inter_iff, mem_preimage,
        ha, hb, and_self, false_and, and_false, ↓reduceIte, mul_zero, zero_mul]
    exact (exponentialMartingale_eq_mul θ W s t ω).symm
  have hAB : MeasurableSet (A ∩ X ⁻¹' B) :=
    (ℱ.le t _ (ℱ.mono hst _ hA)).inter (hB.preimage (hX.mono (ℱ.le t) le_rfl))
  rw [hprod, integral_indicator hAB, integral_indicator (ℱ.le s _ hA)] at hfactor
  have hlaw : HasLaw X (gaussianReal 0 (t - s)) P := by
    convert (hW.shift s).hasLaw_eval (t - s) using 1
    ext ω
    simp [X, add_tsub_cancel_of_le hst]
  have hgint : ∫ ω, (g ∘ X) ω ∂P =
      (gaussianReal (θ * ((t : ℝ) - s)) (t - s)).real B := by
    rw [hlaw.integral_comp hg.aestronglyMeasurable, integral_indicator hB]
    have hexp : (fun x : ℝ ↦ exp (θ * x - θ ^ 2 * ((t : ℝ) - s) / 2)) =
        fun x ↦ exp (-(θ ^ 2 * ((t : ℝ) - s) / 2)) * exp (θ * x) := by
      ext x
      rw [← exp_add]
      congr 1
      ring
    rw [hexp, integral_const_mul, setIntegral_exp_mul_gaussianReal]
    simp only [NNReal.coe_sub hst, zero_mul, zero_add]
    rw [← mul_assoc, ← exp_add]
    simp [mul_comm]
  rw [hgint] at hfactor
  rw [hW.tilted_mul_eval_apply θ htT (hA := (ℱ.mono hst _ hA).inter (hB.preimage hX)),
    hW.tilted_mul_eval_apply θ (hst.trans htT) hA, hfactor,
    ENNReal.ofReal_mul (integral_nonneg fun ω ↦ (exponentialMartingale_pos θ W s ω).le),
    ofReal_measureReal]

/-- On the tilting horizon, a Brownian increment acquires mean `θ (t - s)` and retains
variance `t - s`. The statement includes zero-length increments. -/
theorem hasLaw_sub_tilted_mul_eval (hW : IsFilteredPreBrownianReal ℱ W P) (θ : ℝ)
    {s t T : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T) :
    HasLaw (W t - W s) (gaussianReal (θ * ((t : ℝ) - s)) (t - s))
      (P.tilted (fun ω ↦ θ * W T ω)) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have := isProbabilityMeasure_tilted (hW.integrable_exp_mul_eval θ T)
  refine ⟨((hW.adapted.measurable.sub hW.adapted.measurable).aemeasurable.mono_ac
    (tilted_absolutelyContinuous _ _)), Measure.ext fun B hB ↦ ?_⟩
  rw [Measure.map_apply (hW.adapted.measurable.sub hW.adapted.measurable) hB]
  simpa using hW.tilted_mul_eval_inter_preimage θ hst htT (A := univ) MeasurableSet.univ hB

/-- Brownian increments remain independent of the past under the terminal exponential tilt,
provided the increment ends no later than the tilting horizon. -/
theorem indep_sub_tilted_mul_eval (hW : IsFilteredPreBrownianReal ℱ W P) (θ : ℝ)
    {s t T : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T) :
    Indep (.comap (W t - W s) inferInstance) (ℱ s) (P.tilted (fun ω ↦ θ * W T ω)) := by
  rw [Indep_iff]
  intro B A hB hA
  obtain ⟨B, hBmeas, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hB
  rw [inter_comm, hW.tilted_mul_eval_inter_preimage θ hst htT hA hBmeas,
    ← (hW.hasLaw_sub_tilted_mul_eval θ hst htT).map_eq,
    Measure.map_apply (hW.adapted.measurable.sub hW.adapted.measurable) hBmeas, mul_comm]

/-- Subtracting the acquired drift centers every increment under the terminal tilt. With
`θ = -κ` this is the Gaussian increment law of `W t + κ t` on `[0,T]`. -/
theorem hasLaw_sub_drift_tilted_mul_eval (hW : IsFilteredPreBrownianReal ℱ W P) (θ : ℝ)
    {s t T : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T) :
    HasLaw (fun ω ↦ (W t ω - θ * t) - (W s ω - θ * s)) (gaussianReal 0 (t - s))
      (P.tilted (fun ω ↦ θ * W T ω)) := by
  convert gaussianReal_add_const (hW.hasLaw_sub_tilted_mul_eval θ hst htT)
    (-θ * ((t : ℝ) - s)) using 1
  · ext ω
    simp only [Pi.sub_apply]
    ring
  · congr 1
    ring

/-- The drift-corrected increments are independent of the original filtration's past. -/
theorem indep_sub_drift_tilted_mul_eval (hW : IsFilteredPreBrownianReal ℱ W P) (θ : ℝ)
    {s t T : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T) :
    Indep (.comap (fun ω ↦ (W t ω - θ * t) - (W s ω - θ * s)) inferInstance) (ℱ s)
      (P.tilted (fun ω ↦ θ * W T ω)) := by
  have heq : (fun ω ↦ (W t ω - θ * t) - (W s ω - θ * s)) =
      (fun x : ℝ ↦ x - θ * ((t : ℝ) - s)) ∘ (W t - W s) := by
    ext ω
    simp only [Function.comp_apply, Pi.sub_apply]
    ring
  rw [heq, ← MeasurableSpace.comap_comp]
  exact indep_of_indep_of_le_left (hW.indep_sub_tilted_mul_eval θ hst htT)
    (MeasurableSpace.comap_mono (by fun_prop : Measurable
      (fun x : ℝ ↦ x - θ * ((t : ℝ) - s))).comap_le)

end TauCeti.Probability.IsFilteredPreBrownianReal

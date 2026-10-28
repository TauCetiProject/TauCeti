/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Tilted
import Mathlib.Probability.Independence.Integration
import TauCeti.Probability.Independence.Filtration

/-!
# Girsanov's theorem for a constant drift

Let `W` be a Brownian motion relative to a filtration `ℱ` under `P`, let `θ : ℝ` and `T : ℝ≥0`,
and let `Q = P.tilted (θ * W T ·)`, the probability measure with density
`exp (θ W_T - θ² T / 2)` with respect to `P`. Then the process
`W^Q_t = W_t - θ min(t, T)`
is a Brownian motion relative to the same filtration `ℱ`, now under `Q`. On the horizon `[0, T]`
it is `W_t - θ t`; with `θ = -κ` for a market price of risk `κ` it is `W_t + κ t`. After time `T`
the density introduces no further drift: an increment of `W` starting at or after `T` keeps its
law `N(0, t - s)` and its independence from the past under `Q`.

As `Q` is absolutely continuous with respect to `P`, almost surely continuous paths of `W` give
almost surely continuous paths of `W^Q`, which is then a Brownian motion under `Q` in the sense of
`ProbabilityTheory.IsBrownianReal`.

## Main declarations

* `TauCeti.Probability.IsFilteredPreBrownianReal.hasLaw_sub_tilted_mul_eval_of_horizon_le` and
  `TauCeti.Probability.IsFilteredPreBrownianReal.indep_sub_tilted_mul_eval_of_horizon_le`:
  increments starting at or after the tilting horizon.
* `TauCeti.Probability.IsFilteredPreBrownianReal.sub_mul_min_tilted_mul_eval`: **Girsanov's
  theorem** for a constant drift.
* `TauCeti.Probability.IsFilteredPreBrownianReal.isBrownianReal_sub_mul_min_tilted_mul_eval`:
  the same statement for a Brownian motion with continuous paths.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991, §3.5.
* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  §5.2.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ}

/-- Once the tilting horizon `T` has passed, the density of the tilted measure is known: an event
known at time `s ≥ T` and an event of the increment `W t - W s` factor, the latter with its
original Gaussian probability. -/
theorem tilted_mul_eval_inter_preimage_of_horizon_le (hW : IsFilteredPreBrownianReal ℱ W P)
    (θ : ℝ) {s t T : ℝ≥0} (hTs : T ≤ s) (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[ℱ s] A)
    {B : Set ℝ} (hB : MeasurableSet B) :
    P.tilted (fun ω ↦ θ * W T ω) (A ∩ (W t - W s) ⁻¹' B) =
      P.tilted (fun ω ↦ θ * W T ω) A * gaussianReal 0 (t - s) B := by
  have hD : Measurable (W t - W s) := hW.adapted.measurable.sub hW.adapted.measurable
  have hA' : MeasurableSet A := ℱ.le s A hA
  have hlaw : HasLaw (W t - W s) (gaussianReal 0 (t - s)) P := by
    convert (hW.shift s).hasLaw_eval (t - s) using 1
    ext ω
    simp [add_tsub_cancel_of_le hst]
  let f : Ω → ℝ≥0∞ := A.indicator fun ω ↦ ENNReal.ofReal (exponentialMartingale θ W T ω)
  let g : Ω → ℝ≥0∞ := ((W t - W s) ⁻¹' B).indicator 1
  have hf : Measurable[ℱ s] f :=
    ((hW.adapted.stronglyAdapted_exponentialMartingale θ T).measurable.mono (ℱ.mono hTs)
      le_rfl).ennreal_ofReal.indicator hA
  have hg : Measurable[.comap (W t - W s) inferInstance] g :=
    Measurable.indicator (f := 1) measurable_const ⟨B, hB, rfl⟩
  have hfg : (A ∩ (W t - W s) ⁻¹' B).indicator
      (fun ω ↦ ENNReal.ofReal (exponentialMartingale θ W T ω)) = fun ω ↦ f ω * g ω := by
    ext ω
    by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ (W t - W s) ⁻¹' B <;> simp [f, g, ha, hb]
  rw [hW.tilted_mul_eval_eq_withDensity, withDensity_apply _ (hA'.inter (hB.preimage hD)),
    withDensity_apply _ hA', ← lintegral_indicator (hA'.inter (hB.preimage hD)), hfg,
    lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace (ℱ.le s)
      hD.comap_le (hW.indep_sub hst).symm hf hg,
    lintegral_indicator hA', lintegral_indicator_one (hB.preimage hD), ← hlaw.map_eq,
    Measure.map_apply hD hB]

/-- An increment of `W` starting at or after the tilting horizon keeps its centered Gaussian law
under the tilted measure. -/
theorem hasLaw_sub_tilted_mul_eval_of_horizon_le (hW : IsFilteredPreBrownianReal ℱ W P)
    (θ : ℝ) {s t T : ℝ≥0} (hTs : T ≤ s) (hst : s ≤ t) :
    HasLaw (W t - W s) (gaussianReal 0 (t - s)) (P.tilted (fun ω ↦ θ * W T ω)) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have := isProbabilityMeasure_tilted (hW.integrable_exp_mul_eval θ T)
  refine ⟨((hW.adapted.measurable.sub hW.adapted.measurable).aemeasurable.mono_ac
    (tilted_absolutelyContinuous _ _)), Measure.ext fun B hB ↦ ?_⟩
  rw [Measure.map_apply (hW.adapted.measurable.sub hW.adapted.measurable) hB]
  simpa using
    hW.tilted_mul_eval_inter_preimage_of_horizon_le θ hTs hst (A := univ) MeasurableSet.univ hB

/-- An increment of `W` starting at or after the tilting horizon remains independent of the past
under the tilted measure. -/
theorem indep_sub_tilted_mul_eval_of_horizon_le (hW : IsFilteredPreBrownianReal ℱ W P)
    (θ : ℝ) {s t T : ℝ≥0} (hTs : T ≤ s) (hst : s ≤ t) :
    Indep (.comap (W t - W s) inferInstance) (ℱ s) (P.tilted (fun ω ↦ θ * W T ω)) := by
  rw [Indep_iff]
  intro B A hB hA
  obtain ⟨B, hBmeas, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hB
  rw [inter_comm, hW.tilted_mul_eval_inter_preimage_of_horizon_le θ hTs hst hA hBmeas,
    ← (hW.hasLaw_sub_tilted_mul_eval_of_horizon_le θ hTs hst).map_eq,
    Measure.map_apply (hW.adapted.measurable.sub hW.adapted.measurable) hBmeas, mul_comm]

/-- **Girsanov's theorem** for a constant drift. If `W` is a Brownian motion relative to `ℱ`
under `P`, then `t ↦ W t - θ min(t, T)` is a Brownian motion relative to `ℱ` under the measure
`P.tilted (θ * W T ·)`, whose density with respect to `P` is `exp (θ W_T - θ² T / 2)`. -/
theorem sub_mul_min_tilted_mul_eval (hW : IsFilteredPreBrownianReal ℱ W P) (θ : ℝ) (T : ℝ≥0) :
    IsFilteredPreBrownianReal ℱ (fun t ω ↦ W t ω - θ * (min t T : ℝ≥0))
      (P.tilted (fun ω ↦ θ * W T ω)) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have := isProbabilityMeasure_tilted (hW.integrable_exp_mul_eval θ T)
  set Q := P.tilted (fun ω ↦ θ * W T ω)
  set X : ℝ≥0 → Ω → ℝ := fun t ω ↦ W t ω - θ * (min t T : ℝ≥0)
  have hX : Adapted ℱ X := fun t ↦ (hW.adapted t).sub_const _
  -- `G s t`: the increment over `[s, t]` is `N(0, t - s)` and independent of `ℱ s` under `Q`.
  let G (s t : ℝ≥0) : Prop :=
    HasLaw (X t - X s) (gaussianReal 0 (t - s)) Q ∧
      Indep (.comap (X t - X s) inferInstance) (ℱ s) Q
  -- Increments inside the horizon `[0, T]`.
  have before {s t : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T) : G s t := by
    have hXts : X t - X s = fun ω ↦ (W t ω - θ * t) - (W s ω - θ * s) := by
      ext ω
      simp only [X, Pi.sub_apply, min_eq_left htT, min_eq_left (hst.trans htT)]
    dsimp only [G]
    rw [hXts]
    exact ⟨hW.hasLaw_sub_drift_tilted_mul_eval θ hst htT,
      hW.indep_sub_drift_tilted_mul_eval θ hst htT⟩
  -- Increments after the horizon.
  have after {s t : ℝ≥0} (hTs : T ≤ s) (hst : s ≤ t) : G s t := by
    have hXts : X t - X s = W t - W s := by
      ext ω
      simp only [X, Pi.sub_apply, min_eq_right hTs, min_eq_right (hTs.trans hst)]
      ring
    dsimp only [G]
    rw [hXts]
    exact ⟨hW.hasLaw_sub_tilted_mul_eval_of_horizon_le θ hTs hst,
      hW.indep_sub_tilted_mul_eval_of_horizon_le θ hTs hst⟩
  -- An increment straddling `T` is the sum of two independent centered Gaussian increments.
  have across {s t : ℝ≥0} (hsT : s ≤ T) (hTt : T ≤ t) : G s t := by
    obtain ⟨hlaw₁, hind₁⟩ := before hsT le_rfl
    obtain ⟨hlaw₂, hind₂⟩ := after le_rfl hTt
    have hpair : IndepFun (X T - X s) (X t - X T) Q :=
      (indep_of_indep_of_le_right hind₂ ((hX T).sub (hX.measurable_le hsT)).comap_le).symm
    refine ⟨⟨(hX.measurable.sub hX.measurable).aemeasurable, ?_⟩,
      hX.indep_comap_sub_of_indep_comap_sub hsT hind₁ hind₂⟩
    rw [← sub_add_sub_cancel' (X T) (X s) (X t), gaussianReal_add_gaussianReal_of_indepFun
      hpair hlaw₁ hlaw₂, zero_add, add_comm, tsub_add_tsub_cancel hTt hsT]
  have hG {s t : ℝ≥0} (hst : s ≤ t) : G s t := by
    rcases le_total t T with htT | hTt
    · exact before hst htT
    rcases le_total T s with hTs | hsT
    · exact after hTs hst
    · exact across hsT hTt
  refine hX.isFilteredPreBrownianReal ?_ (fun s t hst ↦ (hG hst).1) (fun s t hst ↦ (hG hst).2)
  filter_upwards [(tilted_absolutelyContinuous _ _).ae_le hW.eval_zero_ae_eq_zero] with ω hω
  simp [X, hω]

/-- **Girsanov's theorem** for a constant drift, with continuous paths. If moreover `W` has almost
surely continuous paths, then `t ↦ W t - θ min(t, T)` is a Brownian motion under the measure
`P.tilted (θ * W T ·)`. -/
theorem isBrownianReal_sub_mul_min_tilted_mul_eval (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (W · ω)) (θ : ℝ) (T : ℝ≥0) :
    IsBrownianReal (fun t ω ↦ W t ω - θ * (min t T : ℝ≥0)) (P.tilted (fun ω ↦ θ * W T ω)) where
  toIsPreBrownianReal := (hW.sub_mul_min_tilted_mul_eval θ T).toIsPreBrownianReal
  cont := by
    filter_upwards [(tilted_absolutelyContinuous _ _).ae_le hcont] with ω hω
    fun_prop

end TauCeti.Probability.IsFilteredPreBrownianReal

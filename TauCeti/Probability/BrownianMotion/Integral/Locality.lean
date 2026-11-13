/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.L2
import TauCeti.Probability.Process.ElementaryDensity
import Mathlib.MeasureTheory.Function.Holder
import TauCeti.MeasureTheory.Function.Lp.Indicator

/-!
# Event locality of the predictable L² Brownian integral

An event known at time `s` can be pulled out of an integral over `(s,T]`. Consequently,
if two integrands agree on that event after `s`, their future integrals agree there too.
These identities provide the eventwise gluing used to compare stopped integrals.

The statements concern the constructed terminal L² integral on the original filtration.
They require neither continuous Brownian paths nor usual filtration conditions, and make
no assertion of simultaneous-time equality for arbitrarily selected L² representatives.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

/-- An event known at `s` factors out of the completed Brownian integral over `(s,T]`.
The input is any predictable L² class, not necessarily a simple or bounded integrand.
The identity also holds when `T ≤ s`, when both future integrals vanish. -/
theorem coeFn_l2Integral_indicator_Ioc_prod (hW : IsFilteredPreBrownianReal ℱ W P)
    (T s : ℝ≥0) {A : Set Ω} (hA : MeasurableSet[ℱ s] A)
    (f : Lp ℝ 2 (ℱ.predictableMeasure P T)) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    hW.l2Integral T (((Lp.memLp f).indicator
      (measurableSet_predictable_Ioc_prod s T hA).nullMeasurableSet).toLp
        ((Ioc s T ×ˢ A).indicator f)) =ᵐ[P]
      A.indicator (hW.l2Integral T (((Lp.memLp f).indicator
        (measurableSet_predictable_Ioc_prod s T (𝓕 := ℱ) MeasurableSet.univ).nullMeasurableSet).toLp
          ((Ioc s T ×ˢ univ).indicator f))) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let μ := ℱ.predictableMeasure P T
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let hR := measurableSet_predictable_Ioc_prod s T hA
  let hD := measurableSet_predictable_Ioc_prod s T (𝓕 := ℱ) MeasurableSet.univ
  let J := (hW.l2Integral T).toContinuousLinearMap
  let R := (ContinuousLinearMap.mul ℝ ℝ).holderL μ ∞ 2 2
    (linftyIndicator μ (Ioc s T ×ˢ A) hR)
  let D := (ContinuousLinearMap.mul ℝ ℝ).holderL μ ∞ 2 2
    (linftyIndicator μ (Ioc s T ×ˢ univ) hD)
  let E := (ContinuousLinearMap.mul ℝ ℝ).holderL P ∞ 2 2
    (linftyIndicator P A (ℱ.le s _ hA))
  -- Both sides are continuous linear maps; it suffices to compare predictable rectangles.
  have hmaps : J.comp R = E.comp (J.comp D) := by
    apply ContinuousLinearMap.ext_indicatorConstLp_Ioc_prod_predictableMeasure T
    intro u v _ hv B hB
    let g : Lp ℝ 2 μ := indicatorConstLp 2
      (measurableSet_predictable_Ioc_prod u v hB) (measure_ne_top _ _) 1
    have hAB : MeasurableSet[ℱ (max s u)] (A ∩ B) :=
      ((ℱ.mono (le_max_left _ _)) _ hA).inter ((ℱ.mono (le_max_right _ _)) _ hB)
    have hB' : MeasurableSet[ℱ (max s u)] B := (ℱ.mono (le_max_right _ _)) _ hB
    -- Intersect a test rectangle with the future strip and with a known event.
    have hstep (C : Set Ω) (hC : MeasurableSet[ℱ s] C) :
        (ContinuousLinearMap.mul ℝ ℝ).holderL μ ∞ 2 2
          (linftyIndicator μ (Ioc s T ×ˢ C) (measurableSet_predictable_Ioc_prod s T hC)) g =
        indicatorConstLp 2 (measurableSet_predictable_Ioc_prod (max s u) v
          (((ℱ.mono (le_max_left _ _)) _ hC).inter hB')) (measure_ne_top _ _) 1 := by
      apply Lp.ext
      filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2)
        (linftyIndicator μ (Ioc s T ×ˢ C) (measurableSet_predictable_Ioc_prod s T hC)) g,
        coeFn_linftyIndicator (μ := μ) (measurableSet_predictable_Ioc_prod s T hC),
        indicatorConstLp_coeFn (p := 2) (hs := measurableSet_predictable_Ioc_prod u v hB)
          (hμs := measure_ne_top μ _) (c := (1 : ℝ)),
        indicatorConstLp_coeFn (p := 2) (hs := measurableSet_predictable_Ioc_prod (max s u) v
          (((ℱ.mono (le_max_left _ _)) _ hC).inter hB'))
          (hμs := measure_ne_top μ _) (c := (1 : ℝ))] with p hp hCp hp₁ hp₂
      rw [ContinuousLinearMap.holderL_apply_apply, hp, ContinuousLinearMap.mul_apply',
        hCp, hp₁, hp₂]
      simp only [Set.indicator, Set.mem_prod, Set.mem_Ioc, max_lt_iff, Pi.one_apply]
      split_ifs <;> grind
    have hDstep := hstep univ MeasurableSet.univ
    simp only [univ_inter] at hDstep
    simp only [ContinuousLinearMap.comp_apply]
    rw [hstep A hA, hDstep]
    -- The elementary integral only sees the intersection of the two known events.
    apply Lp.ext
    filter_upwards [hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod T (max s u) v hAB 1,
      hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod T (max s u) v hB' 1,
      (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2)
        (linftyIndicator P A (ℱ.le s _ hA))
        (hW.l2Integral T (indicatorConstLp 2
          (measurableSet_predictable_Ioc_prod (max s u) v hB') (measure_ne_top _ _) 1)),
      coeFn_linftyIndicator (μ := P) (ℱ.le s _ hA)] with ω h₁ h₂ h₃ h₄
    simp only [J, E, ContinuousLinearMap.holderL_apply_apply,
      LinearIsometry.coe_toContinuousLinearMap] at *
    rw [h₁, h₃, ContinuousLinearMap.mul_apply', h₄, h₂]
    by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B <;> simp [hωA, hωB]
  -- Express Hölder multiplication as the usual indicator cutoff on L² classes.
  have hcut (C : Set (ℝ≥0 × Ω)) (hC : MeasurableSet C) :
      (ContinuousLinearMap.mul ℝ ℝ).holderL μ ∞ 2 2 (linftyIndicator μ C hC) f =
        ((Lp.memLp f).indicator hC.nullMeasurableSet).toLp (C.indicator f) := by
    apply Lp.ext
    filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder
      (r := 2) (linftyIndicator μ C hC) f, coeFn_linftyIndicator (μ := μ) hC,
      ((Lp.memLp f).indicator hC.nullMeasurableSet).coeFn_toLp] with p hp hC hp'
    rw [ContinuousLinearMap.holderL_apply_apply, hp, ContinuousLinearMap.mul_apply', hC, hp']
    by_cases h : p ∈ C <;> simp [h]
  have heq := congrArg (fun L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P ↦ L f) hmaps
  simp only [ContinuousLinearMap.comp_apply, J, R, D,
    LinearIsometry.coe_toContinuousLinearMap, hcut] at heq
  rw [heq]
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2)
    (linftyIndicator P A (ℱ.le s _ hA)) (hW.l2Integral T
      (((Lp.memLp f).indicator hD.nullMeasurableSet).toLp ((Ioc s T ×ˢ univ).indicator f))),
    coeFn_linftyIndicator (μ := P) (ℱ.le s _ hA)] with ω hω hAω
  rw [ContinuousLinearMap.holderL_apply_apply, hω, ContinuousLinearMap.mul_apply', hAω]
  by_cases h : ω ∈ A <;> simp [h]

/-- If two predictable L² integrands agree on an event known at `s`, their integrals
from `s` to `T` agree on that event. The premise only concerns the actual future strip. -/
theorem l2Integral_congr_on_event (hW : IsFilteredPreBrownianReal ℱ W P)
    (T s : ℝ≥0) {A : Set Ω} (hA : MeasurableSet[ℱ s] A)
    (f g : Lp ℝ 2 (ℱ.predictableMeasure P T))
    (hfg : ∀ᵐ p ∂ℱ.predictableMeasure P T, p ∈ Ioc s T ×ˢ A → f p = g p) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    ∀ᵐ ω ∂P, ω ∈ A →
      hW.l2Integral T (((Lp.memLp f).indicator
        (measurableSet_predictable_Ioc_prod s T (𝓕 := ℱ) MeasurableSet.univ).nullMeasurableSet).toLp
          ((Ioc s T ×ˢ univ).indicator f)) ω =
      hW.l2Integral T (((Lp.memLp g).indicator
        (measurableSet_predictable_Ioc_prod s T (𝓕 := ℱ) MeasurableSet.univ).nullMeasurableSet).toLp
          ((Ioc s T ×ˢ univ).indicator g)) ω := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hc : ((Lp.memLp f).indicator
        (measurableSet_predictable_Ioc_prod s T hA).nullMeasurableSet).toLp
          ((Ioc s T ×ˢ A).indicator f) =
      ((Lp.memLp g).indicator
        (measurableSet_predictable_Ioc_prod s T hA).nullMeasurableSet).toLp
          ((Ioc s T ×ˢ A).indicator g) := by
    apply Lp.ext
    filter_upwards [hfg, ((Lp.memLp f).indicator
        (measurableSet_predictable_Ioc_prod s T hA).nullMeasurableSet).coeFn_toLp,
      ((Lp.memLp g).indicator
        (measurableSet_predictable_Ioc_prod s T hA).nullMeasurableSet).coeFn_toLp] with p hp hf hg
    rw [hf, hg]
    by_cases h : p ∈ Ioc s T ×ˢ A <;> simp [h, hp]
  have hf := hW.coeFn_l2Integral_indicator_Ioc_prod T s hA f
  have hg := hW.coeFn_l2Integral_indicator_Ioc_prod T s hA g
  rw [hc] at hf
  filter_upwards [hf, hg] with ω hfω hgω hω
  simpa only [Set.indicator_of_mem hω] using hfω.symm.trans hgω

end TauCeti.Probability.IsFilteredPreBrownianReal

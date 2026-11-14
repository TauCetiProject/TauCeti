/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.L2
import TauCeti.Probability.Process.ElementaryDensity
import TauCeti.MeasureTheory.Function.Lp.Indicator

/-!
# Event locality of the predictable L² Brownian integral

An event known at time `s` can be pulled out of an integral over `(s,t]`, at any
ambient horizon `T`. Consequently, if two integrands agree on that event after `s`,
their future integrals agree there too. These identities provide the eventwise gluing
used to compare stopped integrals. Representative-based forms also apply directly to
L² classes, without requiring a particular `MemLp.toLp` cutoff expression.

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

/-- An event known at `s` factors out of the completed Brownian integral over `(s,t]`.
The input is any predictable L² class, not necessarily a simple or bounded integrand.
No ordering of `s`, `t` and the ambient horizon `T` is required. -/
theorem coeFn_l2Integral_indicator_Ioc_prod (hW : IsFilteredPreBrownianReal ℱ W P)
    (T s t : ℝ≥0) {A : Set Ω} (hA : MeasurableSet[ℱ s] A)
    (f : Lp ℝ 2 (ℱ.predictableMeasure P T)) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    hW.l2Integral T (((Lp.memLp f).indicator
      (measurableSet_predictable_Ioc_prod s t hA).nullMeasurableSet).toLp
        ((Ioc s t ×ˢ A).indicator f)) =ᵐ[P]
      A.indicator (hW.l2Integral T (((Lp.memLp f).indicator
        (measurableSet_predictable_Ioc_prod s t (𝓕 := ℱ) MeasurableSet.univ).nullMeasurableSet).toLp
          ((Ioc s t ×ˢ univ).indicator f))) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let μ := ℱ.predictableMeasure P T
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let hR := measurableSet_predictable_Ioc_prod s t hA
  let hD := measurableSet_predictable_Ioc_prod s t (𝓕 := ℱ) MeasurableSet.univ
  let J := (hW.l2Integral T).toContinuousLinearMap
  let R := (ContinuousLinearMap.mul ℝ ℝ).holderL μ ∞ 2 2
    (linftyIndicator μ (Ioc s t ×ˢ A) hR)
  let D := (ContinuousLinearMap.mul ℝ ℝ).holderL μ ∞ 2 2
    (linftyIndicator μ (Ioc s t ×ˢ univ) hD)
  let E := (ContinuousLinearMap.mul ℝ ℝ).holderL P ∞ 2 2
    (linftyIndicator P A (ℱ.le s _ hA))
  -- Both sides are continuous linear maps; compare predictable rectangles.
  have hmaps : J.comp R = E.comp (J.comp D) := by
    apply ContinuousLinearMap.ext_indicatorConstLp_Ioc_prod_predictableMeasure T
    intro u v _ _ B hB
    have hB' : MeasurableSet[ℱ (max s u)] B := (ℱ.mono (le_max_right _ _)) _ hB
    have hAB := ((ℱ.mono (le_max_left s u)) _ hA).inter hB'
    have hstep (C : Set Ω) (hC : MeasurableSet[ℱ s] C) :
        (ContinuousLinearMap.mul ℝ ℝ).holderL μ ∞ 2 2
          (linftyIndicator μ (Ioc s t ×ˢ C) (measurableSet_predictable_Ioc_prod s t hC))
          (indicatorConstLp 2 (measurableSet_predictable_Ioc_prod u v hB)
            (measure_ne_top _ _) 1) =
        indicatorConstLp 2 (measurableSet_predictable_Ioc_prod (max s u) (min t v)
          (((ℱ.mono (le_max_left _ _)) _ hC).inter hB')) (measure_ne_top _ _) 1 := by
      rw [holderL_linftyIndicator_indicatorConstLp]
      congr 1
      ext p
      simp only [mem_inter_iff, mem_prod, mem_Ioc, max_lt_iff, le_min_iff]
      tauto
    have hDstep := hstep univ MeasurableSet.univ
    simp only [univ_inter] at hDstep
    simp only [ContinuousLinearMap.comp_apply]
    rw [hstep A hA, hDstep]
    apply Lp.ext
    filter_upwards [hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod T (max s u) (min t v) hAB 1,
      hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod T (max s u) (min t v) hB' 1,
      coeFn_holderL_linftyIndicator (ℱ.le s _ hA)
        (hW.l2Integral T (indicatorConstLp 2
          (measurableSet_predictable_Ioc_prod (max s u) (min t v) hB')
            (measure_ne_top _ _) 1))] with ω h₁ h₂ h₃
    simp only [J, E, LinearIsometry.coe_toContinuousLinearMap] at *
    rw [h₁, h₃]
    by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B <;> simp [hωA, hωB, h₂]
  have heq := congrArg (fun L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P ↦ L f) hmaps
  simp only [ContinuousLinearMap.comp_apply, J, R, D,
    LinearIsometry.coe_toContinuousLinearMap, holderL_linftyIndicator_eq_toLp] at heq
  rw [heq]
  exact coeFn_holderL_linftyIndicator (ℱ.le s _ hA) _

/-- If two predictable L² integrands agree on an event known at `s` during `(s,t]`,
their integrals over that strip agree on that event, at any ambient horizon `T`. -/
theorem ae_l2Integral_indicator_Ioc_prod_eq_of_mem (hW : IsFilteredPreBrownianReal ℱ W P)
    {T s t : ℝ≥0} {A : Set Ω} (hA : MeasurableSet[ℱ s] A)
    {f g : Lp ℝ 2 (ℱ.predictableMeasure P T)}
    (hfg : ∀ᵐ p ∂ℱ.predictableMeasure P T, p ∈ Ioc s t ×ˢ A → f p = g p) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    ∀ᵐ ω ∂P, ω ∈ A →
      hW.l2Integral T (((Lp.memLp f).indicator
        (measurableSet_predictable_Ioc_prod s t (𝓕 := ℱ) MeasurableSet.univ).nullMeasurableSet).toLp
          ((Ioc s t ×ˢ univ).indicator f)) ω =
      hW.l2Integral T (((Lp.memLp g).indicator
        (measurableSet_predictable_Ioc_prod s t (𝓕 := ℱ) MeasurableSet.univ).nullMeasurableSet).toLp
          ((Ioc s t ×ˢ univ).indicator g)) ω := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hc : ((Lp.memLp f).indicator
        (measurableSet_predictable_Ioc_prod s t hA).nullMeasurableSet).toLp
          ((Ioc s t ×ˢ A).indicator f) =
      ((Lp.memLp g).indicator
        (measurableSet_predictable_Ioc_prod s t hA).nullMeasurableSet).toLp
          ((Ioc s t ×ˢ A).indicator g) := by
    apply Lp.ext
    filter_upwards [hfg, ((Lp.memLp f).indicator
        (measurableSet_predictable_Ioc_prod s t hA).nullMeasurableSet).coeFn_toLp,
      ((Lp.memLp g).indicator
        (measurableSet_predictable_Ioc_prod s t hA).nullMeasurableSet).coeFn_toLp] with p hp hf hg
    rw [hf, hg]
    by_cases h : p ∈ Ioc s t ×ˢ A <;> simp [h, hp]
  have hf := hW.coeFn_l2Integral_indicator_Ioc_prod T s t hA f
  have hg := hW.coeFn_l2Integral_indicator_Ioc_prod T s t hA g
  rw [hc] at hf
  filter_upwards [hf, hg] with ω hfω hgω hω
  simpa only [Set.indicator_of_mem hω] using hfω.symm.trans hgω

/-- A representative supported after `s` admits factoring by an event known at `s`.
The event-cutoff representative may be supplied as any L² class `g` equal to it almost
everywhere; callers need not construct a particular `MemLp.toLp` expression. -/
theorem coeFn_l2Integral_eq_indicator_of_ae_eq
    (hW : IsFilteredPreBrownianReal ℱ W P) {T s : ℝ≥0} {A : Set Ω}
    (hA : MeasurableSet[ℱ s] A) {f g : Lp ℝ 2 (ℱ.predictableMeasure P T)}
    (hf : ∀ᵐ p ∂ℱ.predictableMeasure P T, p.1 ≤ s → f p = 0)
    (hg : g =ᵐ[ℱ.predictableMeasure P T] (univ ×ˢ A).indicator f) :
    hW.l2Integral T g =ᵐ[P] A.indicator (hW.l2Integral T f) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have htime : ∀ᵐ p ∂ℱ.predictableMeasure P T, p ∈ Ioc 0 T ×ˢ (univ : Set Ω) := by
    have h := ae_restrict_mem (μ := ℱ.predictableMeasure P T)
      (measurableSet_predictable_Ioc_prod 0 T (𝓕 := ℱ) MeasurableSet.univ)
    simpa only [ℱ.predictableMeasure_restrict P T T, min_self] using h
  have hD : ((Lp.memLp f).indicator
      (measurableSet_predictable_Ioc_prod s T (𝓕 := ℱ) MeasurableSet.univ).nullMeasurableSet).toLp
        ((Ioc s T ×ˢ univ).indicator f) = f := by
    apply Lp.ext
    filter_upwards [hf, htime,
      ((Lp.memLp f).indicator (measurableSet_predictable_Ioc_prod s T
        (𝓕 := ℱ) MeasurableSet.univ).nullMeasurableSet).coeFn_toLp] with p hfp hp hx
    rw [hx]
    by_cases h : p.1 ≤ s <;> simp [Set.indicator, Set.mem_prod, Set.mem_Ioc] at * <;> grind
  have hR : ((Lp.memLp f).indicator
      (measurableSet_predictable_Ioc_prod s T hA).nullMeasurableSet).toLp
        ((Ioc s T ×ˢ A).indicator f) = g := by
    apply Lp.ext
    filter_upwards [hf, hg, htime, ((Lp.memLp f).indicator
      (measurableSet_predictable_Ioc_prod s T hA).nullMeasurableSet).coeFn_toLp]
        with p hfp hgp hp hx
    rw [hx, hgp]
    by_cases h : p.1 ≤ s <;> simp [Set.indicator, Set.mem_prod, Set.mem_Ioc] at * <;> grind
  simpa only [hR, hD] using hW.coeFn_l2Integral_indicator_Ioc_prod T s T hA f

/-- If two representatives agree before `s` and on an event known at `s`, their
terminal Brownian integrals agree almost everywhere on that event. -/
theorem ae_l2Integral_eq_of_mem (hW : IsFilteredPreBrownianReal ℱ W P)
    {T s : ℝ≥0} {A : Set Ω} (hA : MeasurableSet[ℱ s] A)
    {f g : Lp ℝ 2 (ℱ.predictableMeasure P T)}
    (hfg : ∀ᵐ p ∂ℱ.predictableMeasure P T, (p.1 ≤ s ∨ p.2 ∈ A) → f p = g p) :
    ∀ᵐ ω ∂P, ω ∈ A → hW.l2Integral T f ω = hW.l2Integral T g ω := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hd : ∀ᵐ p ∂ℱ.predictableMeasure P T, p.1 ≤ s → (f - g) p = 0 := by
    filter_upwards [hfg, Lp.coeFn_sub f g] with p hp hd hs
    exact hd.trans (sub_eq_zero.mpr (hp (Or.inl hs)))
  have hz : (0 : Lp ℝ 2 (ℱ.predictableMeasure P T)) =ᵐ[ℱ.predictableMeasure P T]
      (univ ×ˢ A).indicator (f - g : Lp ℝ 2 (ℱ.predictableMeasure P T)) := by
    filter_upwards [hfg, Lp.coeFn_sub f g, Lp.coeFn_zero ℝ 2 (ℱ.predictableMeasure P T)]
      with p hp hd hz
    rw [hz]
    by_cases h : p ∈ univ ×ˢ A
    · rw [Set.indicator_of_mem h, hd]
      exact (sub_eq_zero.mpr (hp (Or.inr h.2))).symm
    · rw [Set.indicator_of_notMem h]
      rfl
  have h := hW.coeFn_l2Integral_eq_indicator_of_ae_eq hA hd hz
  rw [map_zero, map_sub] at h
  filter_upwards [h, Lp.coeFn_zero ℝ 2 P,
    Lp.coeFn_sub (hW.l2Integral T f) (hW.l2Integral T g)] with ω hω hz hd hAω
  rw [hz, Set.indicator_of_mem hAω, hd] at hω
  exact sub_eq_zero.mp hω.symm

/-- Agreement on an event known initially implies agreement of the terminal Brownian
integrals on that event. No premise at time zero is needed, since it has zero time mass. -/
theorem ae_l2Integral_eq_of_mem_initial (hW : IsFilteredPreBrownianReal ℱ W P)
    {T : ℝ≥0} {A : Set Ω} (hA : MeasurableSet[ℱ 0] A)
    {f g : Lp ℝ 2 (ℱ.predictableMeasure P T)}
    (hfg : ∀ᵐ p ∂ℱ.predictableMeasure P T, p.2 ∈ A → f p = g p) :
    ∀ᵐ ω ∂P, ω ∈ A → hW.l2Integral T f ω = hW.l2Integral T g ω := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  apply hW.ae_l2Integral_eq_of_mem hA
  have hzero := measure_eq_zero_iff_ae_notMem.1
    (ℱ.predictableMeasure_singleton_zero_prod P T (A := univ) MeasurableSet.univ)
  filter_upwards [hfg, hzero] with p hp hzero h
  exact hp (h.resolve_left (by simpa only [mem_prod, mem_singleton_iff, mem_univ,
    and_true, not_le, pos_iff_ne_zero, ne_eq] using hzero))

end TauCeti.Probability.IsFilteredPreBrownianReal

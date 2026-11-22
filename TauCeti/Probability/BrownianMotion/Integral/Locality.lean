/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.L2
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.Probability.BrownianMotion.Integral.Restriction
import TauCeti.Probability.Process.ElementaryDensity
import TauCeti.MeasureTheory.Function.Lp.Indicator

/-!
# Event locality of the predictable L² Brownian integral

An event known at time `s` can be pulled out of an integral over `(s,t]`, at any
ambient horizon `T`. Consequently, if two integrands agree on that event after `s`,
their future integrals agree there too. These identities provide the eventwise gluing
used to compare stopped integrals. Representative-based forms also apply directly to
L² classes, without requiring a particular `MemLp.toLp` cutoff expression; for a
`BrownianIntegrable` integrand within the horizon `T`, restricting to `(u, v] × E`
gives the `E`-gated increment `hW.l2Integral v - hW.l2Integral u`
(`coeFn_l2Integral_indicator_Ioc_prod_eq_indicator_sub`).

The statements concern the constructed terminal L² integral on the original filtration.
They require neither continuous Brownian paths nor usual filtration conditions, and make
no assertion of simultaneous-time equality for arbitrarily selected L² representatives.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

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
      rw [ContinuousLinearMap.holderL_apply_apply, holder_mul_linftyIndicator_indicatorConstLp]
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
      coeFn_holder_mul_linftyIndicator (ℱ.le s _ hA)
        (hW.l2Integral T (indicatorConstLp 2
          (measurableSet_predictable_Ioc_prod (max s u) (min t v) hB')
            (measure_ne_top _ _) 1))] with ω h₁ h₂ h₃
    simp only [J, E, LinearIsometry.coe_toContinuousLinearMap,
      ContinuousLinearMap.holderL_apply_apply] at *
    rw [h₁, h₃]
    by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B <;> simp [hωA, hωB, h₂]
  have heq := congrArg (fun L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P ↦ L f) hmaps
  simp only [ContinuousLinearMap.comp_apply, J, R, D,
    LinearIsometry.coe_toContinuousLinearMap, ContinuousLinearMap.holderL_apply_apply,
    holder_mul_linftyIndicator_eq_toLp] at heq
  rw [heq]
  exact coeFn_holder_mul_linftyIndicator (ℱ.le s _ hA) _

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
theorem coeFn_l2Integral_ae_eq_indicator_of_ae_eq
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

/-- An event known at time zero factors out of the terminal Brownian integral.
No support premise at time zero is needed, since it has zero time mass. -/
theorem coeFn_l2Integral_ae_eq_indicator_of_ae_eq_of_measurableSet_zero
    (hW : IsFilteredPreBrownianReal ℱ W P) {T : ℝ≥0} {A : Set Ω}
    (hA : MeasurableSet[ℱ 0] A) {f g : Lp ℝ 2 (ℱ.predictableMeasure P T)}
    (hg : g =ᵐ[ℱ.predictableMeasure P T] (univ ×ˢ A).indicator f) :
    hW.l2Integral T g =ᵐ[P] A.indicator (hW.l2Integral T f) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  refine hW.coeFn_l2Integral_ae_eq_indicator_of_ae_eq hA ?_ hg
  have hzero := measure_eq_zero_iff_ae_notMem.1
    (ℱ.predictableMeasure_singleton_zero_prod P T (A := univ) MeasurableSet.univ)
  filter_upwards [hzero] with p hp hs
  exact False.elim (hp ⟨nonpos_iff_eq_zero.mp hs, mem_univ _⟩)

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
  have h := hW.coeFn_l2Integral_ae_eq_indicator_of_ae_eq hA hd hz
  rw [map_zero, map_sub] at h
  filter_upwards [h, Lp.coeFn_zero ℝ 2 P,
    Lp.coeFn_sub (hW.l2Integral T f) (hW.l2Integral T g)] with ω hω hz hd hAω
  rw [hz, Set.indicator_of_mem hAω, hd] at hω
  exact sub_eq_zero.mp hω.symm

/-- Agreement on an event known initially implies agreement of the terminal Brownian
integrals on that event. No premise at time zero is needed, since it has zero time mass. -/
theorem ae_l2Integral_eq_of_mem_of_measurableSet_zero (hW : IsFilteredPreBrownianReal ℱ W P)
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

/-- Restricting a `BrownianIntegrable` integrand to a predictable rectangle `(u, v] × E` within
the horizon `T` evaluates to the `E`-gated increment of `l2Integral` from `u` to `v`. -/
theorem coeFn_l2Integral_indicator_Ioc_prod_eq_indicator_sub
    (hW : IsFilteredPreBrownianReal ℱ W P)
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H)
    {u v T : ℝ≥0} (huv : u ≤ v) (hvT : v ≤ T) {E : Set Ω} (hE : MeasurableSet[ℱ u] E) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    hW.l2Integral T ((hH.indicator_Ioc_prod u v hE).toPredictableLp T) =ᵐ[P]
      E.indicator (fun ω ↦ hW.l2Integral v (hH.toPredictableLp v) ω -
        hW.l2Integral u (hH.toPredictableLp u) ω) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let f := hH.toPredictableLp T
  have hL : ((Lp.memLp f).indicator
      (measurableSet_predictable_Ioc_prod u v hE).nullMeasurableSet).toLp
        ((Ioc u v ×ˢ E).indicator f) = (hH.indicator_Ioc_prod u v hE).toPredictableLp T := by
    apply Lp.ext
    filter_upwards [((Lp.memLp f).indicator
        (measurableSet_predictable_Ioc_prod u v hE).nullMeasurableSet).coeFn_toLp,
      hH.coeFn_toPredictableLp T, (hH.indicator_Ioc_prod u v hE).coeFn_toPredictableLp T]
      with ⟨t, ω⟩ h1 h2 h3
    rw [h1, h3]
    by_cases ht : t ∈ Ioc u v <;> by_cases hω : ω ∈ E <;> simp [ht, hω, f, h2]
  have hR : ((Lp.memLp f).indicator
      (measurableSet_predictable_Ioc_prod u v (𝓕 := ℱ) MeasurableSet.univ).nullMeasurableSet).toLp
        ((Ioc u v ×ˢ univ).indicator f) =
      ℱ.predictableMeasureExtendLp P ℝ hvT (hH.toPredictableLp v) -
        ℱ.predictableMeasureExtendLp P ℝ (huv.trans hvT) (hH.toPredictableLp u) := by
    apply Lp.ext
    filter_upwards [((Lp.memLp f).indicator (measurableSet_predictable_Ioc_prod u v
        (𝓕 := ℱ) MeasurableSet.univ).nullMeasurableSet).coeFn_toLp,
      Lp.coeFn_sub (ℱ.predictableMeasureExtendLp P ℝ hvT (hH.toPredictableLp v))
        (ℱ.predictableMeasureExtendLp P ℝ (huv.trans hvT) (hH.toPredictableLp u)),
      hH.coeFn_toPredictableLp T,
      ℱ.coeFn_predictableMeasureExtendLp_of_ae_eq P (𝕜 := ℝ) hvT (hH.coeFn_toPredictableLp v),
      ℱ.coeFn_predictableMeasureExtendLp_of_ae_eq P (𝕜 := ℝ) (huv.trans hvT)
        (hH.coeFn_toPredictableLp u)] with ⟨t, ω⟩ h1 hsub hf hv hu
    rw [h1, hsub]
    dsimp only [f, Pi.sub_apply]
    rw [hv, hu]
    simp only [Function.uncurry_apply_pair, Set.indicator, Set.mem_prod,
      Set.mem_Ioc, Set.mem_univ, and_true] at hf ⊢
    by_cases hut : u < t <;> by_cases htv : t ≤ v
    · have ht0 : 0 < t := bot_le.trans_lt hut
      simp [hut, htv, ht0, not_le_of_gt hut, hf]
    · simp [hut, htv, not_le_of_gt hut]
    · have htu : t ≤ u := not_lt.mp hut
      by_cases ht0 : 0 < t <;> simp [hut, htv, ht0, htu]
    · exact False.elim (htv ((not_lt.mp hut).trans huv))
  have hloc := hW.coeFn_l2Integral_indicator_Ioc_prod T u v hE f
  rw [hL, hR, map_sub, hW.l2Integral_predictableMeasureExtendLp hvT,
    hW.l2Integral_predictableMeasureExtendLp (huv.trans hvT)] at hloc
  filter_upwards [hloc, Lp.coeFn_sub (hW.l2Integral v (hH.toPredictableLp v))
    (hW.l2Integral u (hH.toPredictableLp u))] with ω hω hsub
  rw [hω]
  by_cases hωE : ω ∈ E
  · simpa only [Set.indicator_of_mem hωE, Pi.sub_apply] using hsub
  · simp only [Set.indicator_of_notMem hωE]

private theorem coeFn_l2Integral_ite_lt_simpleFunc_mul_eq_mul_sub
    (hW : IsFilteredPreBrownianReal ℱ W P)
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H)
    {s T : ℝ≥0} (hst : s ≤ T) (g : @SimpleFunc Ω (ℱ s) ℝ) (hg_bd : MemLp g ∞ P) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    hW.l2Integral T ((hH.ite_lt_mul s g.stronglyMeasurable hg_bd).toPredictableLp T) =ᵐ[P]
      fun ω ↦ g ω * (hW.l2Integral T (hH.toPredictableLp T) ω -
        hW.l2Integral s (hH.toPredictableLp s) ω) := by
  classical
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let : MeasurableSpace Ω := ℱ s
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let R (c : ℝ) : Lp ℝ 2 (ℱ.predictableMeasure P T) :=
    (hH.indicator_Ioc_prod s T (g.measurableSet_fiber c)).toPredictableLp T
  have hmem_T : ∀ᵐ p ∂ℱ.predictableMeasure P T, p.1 ∈ Ioc 0 T := by
    have hb := ae_restrict_mem (μ := ℱ.predictableMeasure P T)
      (measurableSet_predictable_Ioc_prod 0 T (𝓕 := ℱ) MeasurableSet.univ)
    rw [ℱ.predictableMeasure_restrict, min_self] at hb
    exact hb.mono fun _ hp ↦ hp.1
  have hin : (hH.ite_lt_mul s g.stronglyMeasurable hg_bd).toPredictableLp T =
      ∑ c ∈ g.range, c • R c := by
    apply Lp.ext
    filter_upwards [(hH.ite_lt_mul s g.stronglyMeasurable hg_bd).coeFn_toPredictableLp T,
      Lp.coeFn_finsetSum g.range (fun c ↦ c • R c),
      (ae_ball_iff g.range.countable_toSet).2 fun c _ ↦ Lp.coeFn_smul c (R c),
      (ae_ball_iff g.range.countable_toSet).2 fun c _ ↦
        (hH.indicator_Ioc_prod s T (g.measurableSet_fiber c)).coeFn_toPredictableLp T,
      hmem_T] with ⟨t, ω⟩ hp hsum hsmul hR ht
    rw [hp, hsum, Finset.sum_apply]
    rw [Finset.sum_congr rfl fun c hc ↦ by
      rw [hsmul c hc, Pi.smul_apply, smul_eq_mul, hR c hc, Function.uncurry_apply_pair]]
    by_cases hps : s < t
    · have ht_mem : t ∈ Ioc s T := ⟨hps, ht.2⟩
      simp only [Function.uncurry_apply_pair, hps, ↓reduceIte]
      simp_rw [Set.indicator_of_mem ht_mem, Set.indicator_apply, Set.mem_preimage,
        Set.mem_singleton_iff, mul_ite, mul_zero, eq_comm (a := g ω)]
      rw [Finset.sum_ite_eq']
      simp [g.mem_range_self]
    · have ht_nmem : t ∉ Ioc s T := fun h ↦ hps h.1
      simp [hps, ht_nmem]
  rw [hin, map_sum]
  filter_upwards [Lp.coeFn_finsetSum g.range (fun c ↦ hW.l2Integral T (c • R c)),
    (ae_ball_iff g.range.countable_toSet).2 fun c _ ↦
      Lp.coeFn_smul c (hW.l2Integral T (R c)),
    (ae_ball_iff g.range.countable_toSet).2 fun c _ ↦
      hW.coeFn_l2Integral_indicator_Ioc_prod_eq_indicator_sub hH hst le_rfl
        (g.measurableSet_fiber c)] with ω hsum hsmul hR
  rw [hsum, Finset.sum_apply]
  simp only [map_smul]
  rw [Finset.sum_congr rfl fun c hc ↦ by
    rw [hsmul c hc, Pi.smul_apply, smul_eq_mul, hR c hc]]
  simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff, mul_ite, mul_zero]
  simp_rw [eq_comm (a := g ω)]
  rw [Finset.sum_ite_eq']
  simp [g.mem_range_self]

/-- Multiplying a `BrownianIntegrable` integrand after a deterministic time `s` by an
essentially bounded `ℱ s`-measurable random variable scales the increment of `l2Integral` from
`min s T` to `T` by that multiplier. -/
theorem coeFn_l2Integral_ite_lt_mul_eq_mul_sub
    (hW : IsFilteredPreBrownianReal ℱ W P)
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H)
    (s T : ℝ≥0) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) (hξ_bd : MemLp ξ ∞ P) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    hW.l2Integral T ((hH.ite_lt_mul s hξ hξ_bd).toPredictableLp T) =ᵐ[P]
      fun ω ↦ ξ ω * (hW.l2Integral T (hH.toPredictableLp T) ω -
        hW.l2Integral (min s T) (hH.toPredictableLp (min s T)) ω) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  by_cases hst : s ≤ T
  · rw [min_eq_left hst]
    let g (n : ℕ) : @SimpleFunc Ω (ℱ s) ℝ := by
      let : MeasurableSpace Ω := ℱ s
      exact SimpleFunc.approxOn ξ hξ.measurable univ 0 (mem_univ _) n
    have hg_sm (n : ℕ) : StronglyMeasurable[ℱ s] (g n) :=
      @SimpleFunc.stronglyMeasurable Ω ℝ (ℱ s) _ (g n)
    have hg_bd (n : ℕ) : MemLp (g n) ∞ P := by
      refine memLp_top_of_bound ((hg_sm n).mono (ℱ.le s)).aestronglyMeasurable
        (∑ c ∈ @SimpleFunc.range Ω ℝ (ℱ s) (g n), ‖c‖) (Eventually.of_forall fun ω ↦ ?_)
      exact Finset.single_le_sum (f := fun c : ℝ ↦ ‖c‖) (fun _ _ ↦ norm_nonneg _)
        (@SimpleFunc.mem_range_self Ω ℝ (ℱ s) (g n) ω)
    let F (a : Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ := if s < t then a ω * H t ω else 0
    let hF (n : ℕ) := hH.ite_lt_mul s (hg_sm n) (hg_bd n)
    let hFξ := hH.ite_lt_mul s hξ hξ_bd
    have hlim : ∀ ω, Tendsto (fun n ↦ g n ω) atTop (𝓝 (ξ ω)) := fun ω ↦ by
      let : MeasurableSpace Ω := ℱ s
      exact SimpleFunc.tendsto_approxOn hξ.measurable (mem_univ _) (by simp)
    have hgn_le (ω : Ω) (n : ℕ) : ‖g n ω - ξ ω‖₊ ≤ ‖ξ ω‖₊ := by
      let : MeasurableSpace Ω := ℱ s
      simpa only [sub_zero] using
        SimpleFunc.nnNorm_approxOn_le (s := univ) (y₀ := (0 : ℝ)) hξ.measurable (mem_univ _) ω n
    have henergy : Tendsto (fun n ↦ eLpNorm
        (fun p ↦ F (g n) p.1 p.2 - F ξ p.1 p.2) 2 ((timeMeasure T).prod P)) atTop (𝓝 0) := by
      refine tendsto_eLpNorm_sub_of_ae_tendsto (C := 1) (by norm_num)
        (Eventually.of_forall fun n ↦ ((hF n).memLp_timeMeasure T).aestronglyMeasurable)
        (hFξ.memLp_timeMeasure T)
        (Eventually.of_forall fun n ↦ Eventually.of_forall fun ⟨t, ω⟩ ↦ ?_)
        (Eventually.of_forall fun ⟨t, ω⟩ ↦ ?_)
      · by_cases hps : s < t
        · simp only [F, hps, ↓reduceIte, ← sub_mul, ENNReal.coe_one, one_mul,
            Function.uncurry_apply_pair, eNorm_mul]
          refine mul_le_mul_of_nonneg_right ?_ bot_le
          simpa only [eNorm_eq_nnNorm, ENNReal.coe_le_coe] using hgn_le ω n
        · simp [F, hps]
      · by_cases hps : s < t
        · simpa [F, hps] using (hlim ω).mul_const (H t ω)
        · simp [F, hps]
    have hLp : Tendsto (fun n ↦ eLpNorm
        (fun ω ↦ hW.l2Integral T ((hF n).toPredictableLp T) ω -
          hW.l2Integral T (hFξ.toPredictableLp T) ω) 2 P) atTop (𝓝 0) :=
      henergy.congr fun n ↦ (hW.eLpNorm_l2Integral_sub_l2Integral (hF n) hFξ T).symm
    have hout : TendstoInMeasure P (fun n ↦ hW.l2Integral T ((hF n).toPredictableLp T)) atTop
        (hW.l2Integral T (hFξ.toPredictableLp T)) :=
      tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) hLp
    have hs (n : ℕ) : hW.l2Integral T ((hF n).toPredictableLp T) =ᵐ[P]
        fun ω ↦ g n ω * (hW.l2Integral T (hH.toPredictableLp T) ω -
          hW.l2Integral s (hH.toPredictableLp s) ω) :=
      hW.coeFn_l2Integral_ite_lt_simpleFunc_mul_eq_mul_sub hH hst (g n) (hg_bd n)
    exact tendstoInMeasure_ae_unique (hout.congr_left hs)
      (tendstoInMeasure_of_tendsto_ae
        (fun n ↦ (Lp.memLp (hW.l2Integral T ((hF n).toPredictableLp T))).aestronglyMeasurable.congr
          (hs n))
        (Eventually.of_forall fun ω ↦ (hlim ω).mul_const _))
  · have hTs : T ≤ s := (not_le.mp hst).le
    rw [min_eq_right hTs]
    have hzero : (hH.ite_lt_mul s hξ hξ_bd).toPredictableLp T =
        (BrownianIntegrable.zero : BrownianIntegrable ℱ P 0).toPredictableLp T := by
      let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
      apply Lp.ext
      have hb := ae_restrict_mem (μ := ℱ.predictableMeasure P T)
        (measurableSet_predictable_Ioc_prod 0 T (𝓕 := ℱ) MeasurableSet.univ)
      rw [ℱ.predictableMeasure_restrict, min_self] at hb
      filter_upwards [(hH.ite_lt_mul s hξ hξ_bd).coeFn_toPredictableLp T,
        (BrownianIntegrable.zero : BrownianIntegrable ℱ P 0).coeFn_toPredictableLp T, hb]
        with ⟨t, ω⟩ h1 h2 ht
      have hnot : ¬ s < t := not_lt.mpr (ht.1.2.trans hTs)
      rw [h1, h2]
      simp [hnot]
    rw [hzero, BrownianIntegrable.toPredictableLp_zero, map_zero]
    filter_upwards [Lp.coeFn_zero ℝ 2 P] with ω hω
    simpa only [Pi.zero_apply, sub_self, mul_zero] using hω

end TauCeti.Probability.IsFilteredPreBrownianReal

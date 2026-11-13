/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.L2
import TauCeti.MeasureTheory.Function.Lp.ExtendByZero

/-!
# Deterministic restriction of the completed Brownian integral

Extending a predictable L² integrand by zero from a shorter horizon to a longer one does
not change its Brownian integral. Consequently a terminal integral splits into the integral
up to an intermediate time and the integral of the remaining integrand. These are equalities
of L² random variables, not conditional-expectation identities or pathwise version selections.
They allow finite-horizon integral constructions to be compared before selecting a process.

The proof uses predictable-rectangle density through `l2Integral_unique`, and the existing
linear isometry `TauCeti.extendByZeroLpₗᵢ` for extension between restricted measures.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

/-- Extending an integrand by zero to a longer horizon preserves its completed Brownian
integral. The representative identity is required only almost everywhere for the longer
horizon's predictable measure. In particular, no values at time zero are prescribed. -/
theorem l2Integral_eq_of_ae_eq_indicator (hW : IsFilteredPreBrownianReal ℱ W P)
    {S T : ℝ≥0} (hST : S ≤ T)
    (f : Lp ℝ 2 (ℱ.predictableMeasure P S))
    (g : Lp ℝ 2 (ℱ.predictableMeasure P T))
    (hfg : g =ᵐ[ℱ.predictableMeasure P T] (Ioc 0 S ×ˢ univ).indicator f) :
    hW.l2Integral T g = hW.l2Integral S f := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hstrip : MeasurableSet (Ioc 0 S ×ˢ (univ : Set Ω)) :=
    measurableSet_predictable_Ioc_prod 0 S MeasurableSet.univ
  have hres : (ℱ.predictableMeasure P T).restrict (Ioc 0 S ×ˢ univ) =
      ℱ.predictableMeasure P S := by
    rw [ℱ.predictableMeasure_restrict, min_eq_left hST]
  obtain ⟨E, hE⟩ : ∃ E : Lp ℝ 2 (ℱ.predictableMeasure P S) →ₗᵢ[ℝ]
      Lp ℝ 2 (ℱ.predictableMeasure P T),
      ∀ u, E u =ᵐ[ℱ.predictableMeasure P T] (Ioc 0 S ×ˢ univ).indicator u := by
    -- Transport the map and its representative identity together, so the casts
    -- between L² spaces with equal measures do not enter the subsequent argument.
    rw [← hres]
    have hex : ∃ E : Lp ℝ 2 ((ℱ.predictableMeasure P T).restrict (Ioc 0 S ×ˢ univ))
        →ₗᵢ[ℝ] Lp ℝ 2 ((ℱ.predictableMeasure P T).restrict univ),
        ∀ u, E u =ᵐ[(ℱ.predictableMeasure P T).restrict univ]
          (Ioc 0 S ×ˢ univ).indicator u :=
      ⟨extendByZeroLpₗᵢ ℝ _ hstrip (subset_univ _),
        fun u ↦ coeFn_extendByZeroLpₗᵢ ℝ hstrip (subset_univ _) u⟩
    rw [Measure.restrict_univ] at hex
    exact hex
  -- The two integral maps agree on rectangles within S, hence on all of L²(S).
  have hmaps : (hW.l2Integral T).toContinuousLinearMap.comp E.toContinuousLinearMap =
      (hW.l2Integral S).toContinuousLinearMap := by
    apply hW.l2Integral_unique
    intro s t hst ht A hA
    let u : Lp ℝ 2 (ℱ.predictableMeasure P S) :=
      indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s t hA)
        (measure_ne_top _ _) 1
    let v : Lp ℝ 2 (ℱ.predictableMeasure P T) :=
      indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s t hA)
        (measure_ne_top _ _) 1
    have huv : E u = v := by
      apply Lp.ext
      have hu₀ : u =ᵐ[ℱ.predictableMeasure P S]
          (Ioc s t ×ˢ A).indicator (fun _ ↦ (1 : ℝ)) := indicatorConstLp_coeFn
      have hu₁ : u =ᵐ[(ℱ.predictableMeasure P T).restrict (Ioc 0 S ×ˢ univ)]
          (Ioc s t ×ˢ A).indicator (fun _ ↦ (1 : ℝ)) := by
        rw [hres]
        exact hu₀
      have hu := (ae_eq_restrict_iff_indicator_ae_eq hstrip).mp hu₁
      filter_upwards [hE u, hu, indicatorConstLp_coeFn (p := 2) (c := (1 : ℝ))
        (hs := measurableSet_predictable_Ioc_prod s t hA)
        (hμs := measure_ne_top (ℱ.predictableMeasure P T) _)] with p hp hpu hpv
      rw [hp, hpu, indicator_indicator, hpv]
      congr 1
      ext p
      simp only [mem_inter_iff, mem_prod, mem_Ioc, mem_univ, and_true]
      constructor
      · tauto
      · rintro ⟨⟨hps, hpt⟩, hpA⟩
        exact ⟨⟨bot_le.trans_lt hps, hpt.trans ht⟩, ⟨hps, hpt⟩, hpA⟩
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
    rw [huv]
    exact hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod_of_le hst.le (ht.trans hST) hA 1
  have hEq : E f = g := Lp.ext ((hE f).trans hfg.symm)
  have h := congrArg (fun J : Lp ℝ 2 (ℱ.predictableMeasure P S) →L[ℝ] Lp ℝ 2 P ↦ J f)
    hmaps
  simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    hEq] using h

/-- Split a completed Brownian integral at a deterministic intermediate horizon.
If `g` represents the restriction of `f` to `(0,S]`, the terminal integral is the sum
of its value up to `S` and the integral of `f` cut off to `(S,T]`. The complementary
indicator's value at time zero is immaterial. The equality is in sample-space L²,
including when either horizon is zero. -/
theorem l2Integral_eq_add_restrict (hW : IsFilteredPreBrownianReal ℱ W P)
    {S T : ℝ≥0} (hST : S ≤ T)
    (f : Lp ℝ 2 (ℱ.predictableMeasure P T))
    (g : Lp ℝ 2 (ℱ.predictableMeasure P S))
    (hfg : f =ᵐ[ℱ.predictableMeasure P S] g) :
    hW.l2Integral T f = hW.l2Integral S g +
      hW.l2Integral T (((Lp.memLp f).indicator
        (measurableSet_predictable_Ioc_prod (𝓕 := ℱ) 0 S
          (s := univ) MeasurableSet.univ).compl.nullMeasurableSet).toLp
            ((Ioc 0 S ×ˢ univ)ᶜ.indicator f)) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hstrip : MeasurableSet (Ioc 0 S ×ˢ (univ : Set Ω)) :=
    measurableSet_predictable_Ioc_prod 0 S MeasurableSet.univ
  let k := ((Lp.memLp f).indicator hstrip.compl.nullMeasurableSet).toLp
    ((Ioc 0 S ×ˢ univ)ᶜ.indicator f)
  have hres : (ℱ.predictableMeasure P T).restrict (Ioc 0 S ×ˢ univ) =
      ℱ.predictableMeasure P S := by
    rw [ℱ.predictableMeasure_restrict, min_eq_left hST]
  have hfg' : f =ᵐ[(ℱ.predictableMeasure P T).restrict (Ioc 0 S ×ˢ univ)] g := by
    rw [hres]
    exact hfg
  have hsub : f - k =ᵐ[ℱ.predictableMeasure P T] (Ioc 0 S ×ˢ univ).indicator g := by
    filter_upwards [Lp.coeFn_sub f k, MemLp.coeFn_toLp
      ((Lp.memLp f).indicator hstrip.compl.nullMeasurableSet),
      (ae_eq_restrict_iff_indicator_ae_eq hstrip).mp hfg'] with p hp hkp hfgp
    rw [hp, Pi.sub_apply, hkp, ← hfgp]
    by_cases hpS : p ∈ Ioc 0 S ×ˢ (univ : Set Ω) <;> simp [hpS]
  have h := hW.l2Integral_eq_of_ae_eq_indicator hST g (f - k) hsub
  rw [map_sub] at h
  exact sub_eq_iff_eq_add.mp h

end TauCeti.Probability.IsFilteredPreBrownianReal

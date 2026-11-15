/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.L2

/-!
# Deterministic restriction of the completed Brownian integral

Extending a predictable L² integrand by zero from a shorter horizon to a longer one does
not change its Brownian integral. Consequently a terminal integral splits into the integral
up to an intermediate time and the integral of the remaining integrand. These are equalities
of L² random variables, not conditional-expectation identities or pathwise version selections.
They allow finite-horizon integral constructions to be compared before selecting a process.

The proof uses predictable-rectangle density through `l2Integral_unique`, and the predictable
horizon operators `MeasureTheory.Filtration.predictableMeasureExtendLp` and
`MeasureTheory.Filtration.predictableMeasureRestrictLp`. Their construction uses the existing
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

/-- The completed integral commutes with zero-extension between deterministic horizons,
as an equality of linear isometries. -/
theorem l2Integral_comp_predictableMeasureExtendLp (hW : IsFilteredPreBrownianReal ℱ W P)
    {S T : ℝ≥0} (hST : S ≤ T) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    (hW.l2Integral T).comp (ℱ.predictableMeasureExtendLp P ℝ hST) = hW.l2Integral S := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  apply LinearIsometry.toContinuousLinearMap_injective
  apply hW.l2Integral_unique
  intro s t hst ht A hA
  simp only [LinearIsometry.coe_comp, LinearIsometry.coe_toContinuousLinearMap,
    Function.comp_apply]
  rw [ℱ.predictableMeasureExtendLp_indicatorConstLp_Ioc_prod P hST ht hA]
  exact hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod_of_le hst.le (ht.trans hST) hA 1

/-- Extending an integrand by zero preserves its completed Brownian integral. -/
@[simp]
theorem l2Integral_predictableMeasureExtendLp (hW : IsFilteredPreBrownianReal ℱ W P)
    {S T : ℝ≥0} (hST : S ≤ T) (f : Lp ℝ 2 (ℱ.predictableMeasure P S)) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    hW.l2Integral T (ℱ.predictableMeasureExtendLp P ℝ hST f) = hW.l2Integral S f := by
  exact congrArg (fun J : Lp ℝ 2 (ℱ.predictableMeasure P S) →ₗᵢ[ℝ] Lp ℝ 2 P ↦ J f)
    (hW.l2Integral_comp_predictableMeasureExtendLp hST)

/-- A representative identity for the longer horizon recognises a zero-extension.
No values at time zero are prescribed. -/
theorem l2Integral_eq_of_ae_eq_indicator (hW : IsFilteredPreBrownianReal ℱ W P)
    {S T : ℝ≥0} (hST : S ≤ T)
    (f : Lp ℝ 2 (ℱ.predictableMeasure P S))
    (g : Lp ℝ 2 (ℱ.predictableMeasure P T))
    (hfg : g =ᵐ[ℱ.predictableMeasure P T] (Ioc 0 S ×ˢ univ).indicator f) :
    hW.l2Integral T g = hW.l2Integral S f := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have hEq : ℱ.predictableMeasureExtendLp P ℝ hST f = g :=
    Lp.ext ((ℱ.coeFn_predictableMeasureExtendLp P hST f).trans hfg.symm)
  rw [← hEq, hW.l2Integral_predictableMeasureExtendLp hST]

/-- An integrand agreeing with `f` on the shorter horizon and vanishing afterwards
has the same integral as `f`. The premises use each class only under its own horizon's
measure, so no cross-measure representative transport is required of callers. -/
theorem l2Integral_eq_of_ae_eq_of_ae_eq_zero (hW : IsFilteredPreBrownianReal ℱ W P)
    {S T : ℝ≥0} (hST : S ≤ T)
    (f : Lp ℝ 2 (ℱ.predictableMeasure P S))
    (g : Lp ℝ 2 (ℱ.predictableMeasure P T))
    (hfg : g =ᵐ[ℱ.predictableMeasure P S] f)
    (hg : ∀ᵐ p ∂ℱ.predictableMeasure P T, S < p.1 → g p = 0) :
    hW.l2Integral T g = hW.l2Integral S f := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hstrip := measurableSet_predictable_Ioc_prod (𝓕 := ℱ) 0 S MeasurableSet.univ
  have hfg' : g =ᵐ[(ℱ.predictableMeasure P T).restrict (Ioc 0 S ×ˢ univ)] f := by
    rw [ℱ.predictableMeasure_restrict_of_le P hST]
    exact hfg
  have htime := ae_restrict_mem
    (μ := ℱ.predictableMeasure P T)
    (measurableSet_predictable_Ioc_prod (𝓕 := ℱ) 0 T MeasurableSet.univ)
  rw [ℱ.predictableMeasure_restrict_of_le P le_rfl] at htime
  apply hW.l2Integral_eq_of_ae_eq_indicator hST f g
  filter_upwards [(ae_eq_restrict_iff_indicator_ae_eq hstrip).mp hfg', hg, htime]
    with p hp hz hpt
  by_cases hpS : p ∈ Ioc 0 S ×ˢ (univ : Set Ω)
  · simpa only [indicator_of_mem hpS] using hp
  · rw [indicator_of_notMem hpS]
    exact hz (lt_of_not_ge fun hle ↦ hpS ⟨⟨hpt.1.1, hle⟩, mem_univ _⟩)

/-- Split a completed Brownian integral using classes for its initial and complementary
parts. All hypotheses are a.e. statements, independent of choices of representatives;
the complementary indicator's value at time zero is immaterial. -/
theorem l2Integral_eq_add_of_ae_eq_indicator_compl (hW : IsFilteredPreBrownianReal ℱ W P)
    {S T : ℝ≥0} (hST : S ≤ T)
    (f : Lp ℝ 2 (ℱ.predictableMeasure P T))
    (g : Lp ℝ 2 (ℱ.predictableMeasure P S))
    (k : Lp ℝ 2 (ℱ.predictableMeasure P T))
    (hfg : f =ᵐ[ℱ.predictableMeasure P S] g)
    (hk : k =ᵐ[ℱ.predictableMeasure P T] (Ioc 0 S ×ˢ univ)ᶜ.indicator f) :
    hW.l2Integral T f = hW.l2Integral S g + hW.l2Integral T k := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hstrip := measurableSet_predictable_Ioc_prod (𝓕 := ℱ) 0 S MeasurableSet.univ
  have hfg' : f =ᵐ[(ℱ.predictableMeasure P T).restrict (Ioc 0 S ×ˢ univ)] g := by
    rw [ℱ.predictableMeasure_restrict_of_le P hST]
    exact hfg
  have hsub : f - k =ᵐ[ℱ.predictableMeasure P T] (Ioc 0 S ×ˢ univ).indicator g := by
    filter_upwards [Lp.coeFn_sub f k, hk,
      (ae_eq_restrict_iff_indicator_ae_eq hstrip).mp hfg'] with p hp hkp hfgp
    rw [hp, Pi.sub_apply, hkp, ← hfgp]
    by_cases hpS : p ∈ Ioc 0 S ×ˢ (univ : Set Ω) <;> simp [hpS]
  have h := hW.l2Integral_eq_of_ae_eq_indicator hST g (f - k) hsub
  rw [map_sub] at h
  exact sub_eq_iff_eq_add.mp h

/-- Split any completed Brownian integral into its restriction to `S` and its remainder.
The formula uses only bundled horizon operators, including when either horizon is zero. -/
theorem l2Integral_eq_add_l2Integral_sub (hW : IsFilteredPreBrownianReal ℱ W P)
    {S T : ℝ≥0} (hST : S ≤ T) (f : Lp ℝ 2 (ℱ.predictableMeasure P T)) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    hW.l2Integral T f =
      hW.l2Integral S (ℱ.predictableMeasureRestrictLp P hST f) +
        hW.l2Integral T (f - ℱ.predictableMeasureExtendLp P ℝ hST
          (ℱ.predictableMeasureRestrictLp P hST f)) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  rw [map_sub, hW.l2Integral_predictableMeasureExtendLp hST]
  exact (add_sub_cancel _ _).symm

end TauCeti.Probability.IsFilteredPreBrownianReal

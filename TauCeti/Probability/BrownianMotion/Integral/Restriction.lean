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
up to an intermediate time and the integral of the remaining integrand. For `BrownianIntegrable`
integrands, this yields the `L²` increment norms `eLpNorm_l2Integral_toPredictableLp_sub_of_le`
and `norm_l2Integral_toPredictableLp_sub_sq_of_le`. These are equalities of L² random variables,
not conditional-expectation identities or pathwise version selections.
They allow finite-horizon integral constructions to be compared before selecting a process.

The proof uses predictable-rectangle density through `l2Integral_unique`, and the predictable
horizon operators `MeasureTheory.Filtration.predictableMeasureExtendLp` and
`MeasureTheory.Filtration.predictableMeasureRestrictLp`. The extension uses the existing
linear isometry `TauCeti.extendByZeroLpₗᵢ` between restricted measures; restriction uses
`MeasureTheory.LpToLpRestrictCLM`.

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
@[simp]
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
  rw [ℱ.predictableMeasureExtendLp_indicatorConstLp_Ioc_prod_of_le P hST ht hA]
  exact hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod_of_le hst.le (ht.trans hST) hA 1

/-- Extending an integrand by zero preserves its completed Brownian integral. -/
@[simp]
theorem l2Integral_predictableMeasureExtendLp (hW : IsFilteredPreBrownianReal ℱ W P)
    {S T : ℝ≥0} (hST : S ≤ T) (f : Lp ℝ 2 (ℱ.predictableMeasure P S)) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    hW.l2Integral T (ℱ.predictableMeasureExtendLp P ℝ hST f) = hW.l2Integral S f := by
  exact congrArg (fun J : Lp ℝ 2 (ℱ.predictableMeasure P S) →ₗᵢ[ℝ] Lp ℝ 2 P ↦ J f)
    (hW.l2Integral_comp_predictableMeasureExtendLp hST)

/-- An integrand represented on `T` by the zero-extension of `f` has the same completed
Brownian integral as `f`. No values at time zero are prescribed. -/
theorem l2Integral_eq_of_ae_eq_indicator (hW : IsFilteredPreBrownianReal ℱ W P)
    {S T : ℝ≥0} (hST : S ≤ T)
    (f : Lp ℝ 2 (ℱ.predictableMeasure P S))
    (g : Lp ℝ 2 (ℱ.predictableMeasure P T))
    (hfg : g =ᵐ[ℱ.predictableMeasure P T] (Ioc 0 S ×ˢ univ).indicator f) :
    hW.l2Integral T g = hW.l2Integral S f := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  rw [← ℱ.predictableMeasureExtendLp_eq_of_ae_eq_indicator P (𝕜 := ℝ) hST hfg,
    hW.l2Integral_predictableMeasureExtendLp hST]

/-- An integrand agreeing with `f` on the shorter horizon and vanishing afterwards
has the same completed Brownian integral as `f`. The representative of `f` is used only
under the shorter-horizon measure; `hfg` compares `g` with it under that measure.
Longer-horizon a.e. identities for `g` descend via `predictableMeasure_mono`. -/
theorem l2Integral_eq_of_ae_eq_of_ae_eq_zero (hW : IsFilteredPreBrownianReal ℱ W P)
    {S T : ℝ≥0} (hST : S ≤ T)
    (f : Lp ℝ 2 (ℱ.predictableMeasure P S))
    (g : Lp ℝ 2 (ℱ.predictableMeasure P T))
    (hfg : g =ᵐ[ℱ.predictableMeasure P S] f)
    (hg : ∀ᵐ p ∂ℱ.predictableMeasure P T, S < p.1 → g p = 0) :
    hW.l2Integral T g = hW.l2Integral S f := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  rw [← ℱ.predictableMeasureExtendLp_eq_of_ae_eq_of_ae_eq_zero P (𝕜 := ℝ) hST hfg hg,
    hW.l2Integral_predictableMeasureExtendLp hST]

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
  rw [ℱ.eq_predictableMeasureExtendLp_add_of_ae_eq_indicator_compl P (𝕜 := ℝ) hST hfg hk,
    map_add, hW.l2Integral_predictableMeasureExtendLp hST]

/-- Split any completed Brownian integral into its restriction to `S` and its remainder.
The formula uses only bundled horizon operators, including when either horizon is zero. -/
theorem l2Integral_eq_add_l2Integral_sub (hW : IsFilteredPreBrownianReal ℱ W P)
    {S T : ℝ≥0} (hST : S ≤ T) (f : Lp ℝ 2 (ℱ.predictableMeasure P T)) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    hW.l2Integral T f =
      hW.l2Integral S (ℱ.predictableMeasureRestrictLp P ℝ hST f) +
        hW.l2Integral T (f - ℱ.predictableMeasureExtendLp P ℝ hST
          (ℱ.predictableMeasureRestrictLp P ℝ hST f)) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  rw [map_sub, hW.l2Integral_predictableMeasureExtendLp hST]
  exact (add_sub_cancel _ _).symm

private theorem l2Integral_indicator_Ioc_prod_univ_eq_sub
    (hW : IsFilteredPreBrownianReal ℱ W P)
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) {s t : ℝ≥0} (hst : s ≤ t) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    hW.l2Integral t ((hH.indicator_Ioc_prod s t (@MeasurableSet.univ Ω (ℱ s))).toPredictableLp t) =
      hW.l2Integral t (hH.toPredictableLp t) - hW.l2Integral s (hH.toPredictableLp s) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hmem : ∀ᵐ p ∂ℱ.predictableMeasure P t, p ∈ Ioc 0 t ×ˢ univ := by
    have hb := ae_restrict_mem (μ := ℱ.predictableMeasure P t)
      (measurableSet_predictable_Ioc_prod 0 t (𝓕 := ℱ) MeasurableSet.univ)
    simpa only [ℱ.predictableMeasure_restrict, min_self] using hb
  have hind : (hH.indicator_Ioc_prod s t (@MeasurableSet.univ Ω (ℱ s))).toPredictableLp t =
      hH.toPredictableLp t - ℱ.predictableMeasureExtendLp P ℝ hst (hH.toPredictableLp s) := by
    apply Lp.ext
    filter_upwards
      [(hH.indicator_Ioc_prod s t (@MeasurableSet.univ Ω (ℱ s))).coeFn_toPredictableLp t,
      Lp.coeFn_sub (hH.toPredictableLp t)
        (ℱ.predictableMeasureExtendLp P ℝ hst (hH.toPredictableLp s)),
      hH.coeFn_toPredictableLp t,
      ℱ.coeFn_predictableMeasureExtendLp_of_ae_eq P (𝕜 := ℝ) hst (hH.coeFn_toPredictableLp s),
      hmem] with ⟨u, ω⟩ h1 hsub ht hs hu
    rw [h1, hsub]
    dsimp only [Pi.sub_apply]
    rw [ht, hs]
    simp only [Function.uncurry_apply_pair, Set.indicator, Set.mem_prod, Set.mem_Ioc,
      Set.mem_univ, and_true, hu.1.1, hu.1.2, true_and]
    by_cases hsu : s < u
    · simp [hsu, not_le_of_gt hsu]
    · simp [hsu, not_lt.mp hsu]
  rw [hind, map_sub, hW.l2Integral_predictableMeasureExtendLp hst]

/-- For `s ≤ t`, the sample-space `L²` distance between `hW.l2Integral t (hH.toPredictableLp t)`
and `hW.l2Integral s (hH.toPredictableLp s)` equals the ambient time-product `L²` norm of `H`
restricted to `(s, t]`. -/
theorem eLpNorm_l2Integral_toPredictableLp_sub_of_le (hW : IsFilteredPreBrownianReal ℱ W P)
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) {s t : ℝ≥0} (hst : s ≤ t) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    eLpNorm (fun ω ↦ hW.l2Integral t (hH.toPredictableLp t) ω -
        hW.l2Integral s (hH.toPredictableLp s) ω) 2 P =
      eLpNorm (fun p : ℝ≥0 × Ω ↦ (Ioc s t).indicator (fun u ↦ H u p.2) p.1) 2
        ((timeMeasure t).prod P) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have hdiff := hW.l2Integral_indicator_Ioc_prod_univ_eq_sub hH hst
  have hzero := hW.eLpNorm_l2Integral_sub_l2Integral
    (hH.indicator_Ioc_prod s t (@MeasurableSet.univ Ω (ℱ s))) BrownianIntegrable.zero t
  rw [BrownianIntegrable.toPredictableLp_zero, map_zero] at hzero
  refine (eLpNorm_congr_ae ?_).trans (hzero.trans ?_)
  · filter_upwards [Lp.coeFn_sub (hW.l2Integral t (hH.toPredictableLp t))
      (hW.l2Integral s (hH.toPredictableLp s)), Lp.coeFn_zero ℝ 2 P] with ω hsub hz
    have hω := congrArg (fun f : Lp ℝ 2 P ↦ f ω) hdiff
    rw [hω, hsub, hz]
    simp
  · congr 1
    ext ⟨u, ω⟩
    by_cases hu : u ∈ Ioc s t <;> simp [hu]

/-- For `s ≤ t`, the squared `Lp ℝ 2 P` norm of the increment
`hW.l2Integral t (hH.toPredictableLp t) - hW.l2Integral s (hH.toPredictableLp s)` equals the
expected square integral of `H` over `(s, t]`. -/
theorem norm_l2Integral_toPredictableLp_sub_sq_of_le (hW : IsFilteredPreBrownianReal ℱ W P)
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) {s t : ℝ≥0} (hst : s ≤ t) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    ‖hW.l2Integral t (hH.toPredictableLp t) -
        hW.l2Integral s (hH.toPredictableLp s)‖ ^ 2 =
      ∫ p in Ioc s t ×ˢ Set.univ, H p.1 p.2 ^ 2 ∂(timeMeasure t).prod P := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have hdiff := hW.l2Integral_indicator_Ioc_prod_univ_eq_sub hH hst
  rw [← hdiff]
  let f := hW.l2Integral t
    ((hH.indicator_Ioc_prod s t (@MeasurableSet.univ Ω (ℱ s))).toPredictableLp t)
  have hnorm : ‖f‖ ^ 2 = ∫ ω, f ω ^ 2 ∂P := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae (.of_forall fun ω ↦ ?_)
    simp [sq]
  rw [hnorm, hW.integral_sq_l2Integral_toPredictableLp
    (hH.indicator_Ioc_prod s t (@MeasurableSet.univ Ω (ℱ s))) t,
    ← integral_indicator ((measurableSet_Ioc (a := s) (b := t)).prod MeasurableSet.univ)]
  refine integral_congr_ae (.of_forall fun ⟨u, ω⟩ ↦ ?_)
  by_cases hu : u ∈ Ioc s t <;> simp [hu]

end TauCeti.Probability.IsFilteredPreBrownianReal

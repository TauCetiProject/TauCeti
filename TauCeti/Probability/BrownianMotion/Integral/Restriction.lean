/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.BrownianMotion.Integral.L2
import TauCeti.Probability.Process.Predictable.Truncation

/-!
# Deterministic restriction of the completed Brownian integral

Extending a predictable L² integrand by zero from a shorter horizon to a longer one does
not change its Brownian integral. Consequently a terminal integral splits into the integral
up to an intermediate time and the integral of the remaining integrand. These are equalities
of L² random variables, not conditional-expectation identities or pathwise version selections.
They allow finite-horizon integral constructions to be compared before selecting a process.

This module also provides the increment `L²` isometry `eLpNorm_l2Integral_sub_of_le` across
deterministic horizons `s ≤ t` and `L²(P)` time continuity `continuous_l2Integral` of the
finite-horizon integral curve `t ↦ hW.l2Integral t ...` for every `BrownianIntegrable` integrand.

The proof uses predictable-rectangle density through `l2Integral_unique`, and the predictable
horizon operators `MeasureTheory.Filtration.predictableMeasureExtendLp` and
`MeasureTheory.Filtration.predictableMeasureRestrictLp`. The extension uses the existing
linear isometry `TauCeti.extendByZeroLpₗᵢ` between restricted measures; restriction uses
`MeasureTheory.LpToLpRestrictCLM`. Continuity in `t` uses
`MeasureTheory.Filtration.continuous_toLp_indicator_Ioc_predictableMeasure`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
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

/-- Increment `L²` isometry for the finite-horizon L² Brownian integral: for `s ≤ t`, the `L²(P)`
distance between `hW.l2Integral t` and `hW.l2Integral s` of a `BrownianIntegrable` integrand
equals the `L²` norm of the integrand on `(s, t] × Ω`. -/
theorem eLpNorm_l2Integral_sub_of_le (hW : IsFilteredPreBrownianReal ℱ W P)
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) {s t : ℝ≥0} (hst : s ≤ t) :
    eLpNorm ((hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)) :
          Ω → ℝ) -
        (hW.l2Integral s ((hH.memLp_predictableMeasure s).toLp (Function.uncurry H)) : Ω → ℝ))
      2 P = eLpNorm (Function.uncurry H) 2 (((timeMeasure t).restrict (Ioc s t)).prod P) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let ft := (hH.memLp_predictableMeasure t).toLp (Function.uncurry H)
  let fs := (hH.memLp_predictableMeasure s).toLp (Function.uncurry H)
  let fsExt := ℱ.predictableMeasureExtendLp P ℝ hst fs
  let k : ℝ≥0 × Ω → ℝ := (Ioc s t ×ˢ (univ : Set Ω)).indicator (Function.uncurry H)
  have hk_pred : StronglyMeasurable[ℱ.predictable] k :=
    hH.isStronglyPredictable.indicator (measurableSet_predictable_Ioc_prod s t MeasurableSet.univ)
  have hmk : MemLp k 2 (ℱ.predictableMeasure P t) :=
    (hH.memLp_predictableMeasure t).indicator
      (measurableSet_predictable_Ioc_prod (𝓕 := ℱ) s t MeasurableSet.univ).nullMeasurableSet
  have hdiff : ft - fsExt = hmk.toLp k := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub ft fsExt, (hH.memLp_predictableMeasure t).coeFn_toLp,
      ℱ.coeFn_predictableMeasureExtendLp_of_ae_eq P (𝕜 := ℝ) hst
        (hH.memLp_predictableMeasure s).coeFn_toLp,
      hmk.coeFn_toLp, ℱ.ae_mem_Ioc_prod_predictableMeasure P t] with ⟨u, ω⟩ hsub h1 h2 hk hu
    rw [hsub, hk, Pi.sub_apply]
    dsimp only [ft, fsExt, fs]
    rw [h1, h2]
    simp only [k, indicator_apply, Set.mem_prod, Set.mem_Ioc, Set.mem_univ, and_true]
    rcases le_or_gt u s with hus | hsu
    · simp [hu.1.1, hus, hus.not_gt]
    · simp [hsu.not_ge, hsu, hu.1.2]
  have hmap : hW.l2Integral t ft - hW.l2Integral s fs = hW.l2Integral t (hmk.toLp k) := by
    rw [← hW.l2Integral_predictableMeasureExtendLp hst fs, ← map_sub, hdiff]
  refine (eLpNorm_congr_ae (Lp.coeFn_sub (hW.l2Integral t ft) (hW.l2Integral s fs)).symm).trans ?_
  rw [hmap, hW.eLpNorm_l2Integral t hk_pred hmk]
  dsimp only [k]
  rw [eLpNorm_indicator_eq_eLpNorm_restrict
    ((measurableSet_Ioc (a := s) (b := t)).prod MeasurableSet.univ).nullMeasurableSet,
    ← Measure.restrict_prod_eq_prod_univ]

/-- The finite-horizon `L²` Brownian integral defines a continuous `L²(P)`-valued curve in time
for every `BrownianIntegrable` integrand. -/
theorem continuous_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) :
    Continuous fun t : ℝ≥0 ↦
      hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  refine continuous_iff_continuousAt.2 fun t₀ ↦ ?_
  let T : ℝ≥0 := t₀ + 1
  have hT := hH.memLp_predictableMeasure T
  let trunc (t : ℝ≥0) : Lp ℝ 2 (ℱ.predictableMeasure P T) :=
    (hT.indicator (measurableSet_predictable_Ioc_prod 0 t
      (MeasurableSet.univ : MeasurableSet[ℱ 0] (univ : Set Ω))).nullMeasurableSet).toLp
      ((Ioc 0 t ×ˢ univ).indicator (Function.uncurry H))
  have hcont : ContinuousAt (fun t ↦ hW.l2Integral T (trunc t)) t₀ :=
    ((hW.l2Integral T).continuous.comp
      (ℱ.continuous_toLp_indicator_Ioc_predictableMeasure P T (by norm_num) hT)).continuousAt
  refine hcont.congr ?_
  filter_upwards [Iic_mem_nhds (lt_add_one t₀)] with t ht
  let ft := (hH.memLp_predictableMeasure t).toLp (Function.uncurry H)
  refine hW.l2Integral_eq_of_ae_eq_indicator ht ft (trunc t) ?_
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hres : ∀ᵐ p ∂ℱ.predictableMeasure P T,
      p ∈ Ioc 0 t ×ˢ (univ : Set Ω) → (ft : ℝ≥0 × Ω → ℝ) p = Function.uncurry H p := by
    rw [← ae_restrict_iff' (measurableSet_predictable_Ioc_prod (𝓕 := ℱ) 0 t MeasurableSet.univ),
      ℱ.predictableMeasure_restrict_of_le P ht]
    exact (hH.memLp_predictableMeasure t).coeFn_toLp
  filter_upwards [(hT.indicator (measurableSet_predictable_Ioc_prod 0 t
      (MeasurableSet.univ : MeasurableSet[ℱ 0] (univ : Set Ω))).nullMeasurableSet).coeFn_toLp,
    hres] with p hp hpeq
  rw [hp]
  by_cases hpt : p ∈ Ioc 0 t ×ˢ (univ : Set Ω)
  · simp [hpt, hpeq hpt]
  · simp [hpt]

end TauCeti.Probability.IsFilteredPreBrownianReal

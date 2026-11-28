/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Deterministic
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Isometry
import TauCeti.Probability.BrownianMotion.Integral.Restriction
import TauCeti.Probability.Process.Predictable.Truncation

/-!
# `L²(P)` time continuity, zero expectation, and Wiener identifications of Brownian Itô integrals

Extending `TauCeti.Probability.BrownianMotion.Integral.Ito.Isometry`, this module establishes:

* `TauCeti.Probability.IsFilteredPreBrownianReal.ae_eq_wienerIntegral_of_isItoIntegral`:
  identification of Itô integrals of deterministic `L²(timeMeasure t)` integrands with the Wiener
  integral.
* `TauCeti.Probability.IsFilteredPreBrownianReal.eLpNorm_l2Integral_sub_of_le` and
  `TauCeti.Probability.IsFilteredPreBrownianReal.continuous_l2Integral`: increment `L²` isometry
  and `L²(P)` continuity of the finite-horizon integral curve `t ↦ hW.l2Integral t ...`.
* `TauCeti.Probability.IsItoIntegral.continuous_toLp`: `L²(P)` continuity in time of any Itô
  integral of a `BrownianIntegrable` integrand.
* `TauCeti.Probability.IsItoIntegral.integral_eq_zero`: zero expectation at every horizon.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

open TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace IsFilteredPreBrownianReal

variable {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

/-- At any time `t`, an Itô integral of a deterministic integrand `f ∈ L²(timeMeasure t)` agrees
almost surely with its Wiener integral `hW.toIsPreBrownianReal.wienerIntegral t (hf.toLp f)`. -/
theorem ae_eq_wienerIntegral_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    {f : ℝ≥0 → ℝ} {I : ℝ≥0 → Ω → ℝ} {t : ℝ≥0} (hf : MemLp f 2 (timeMeasure t))
    (hI : IsItoIntegral ℱ P W (fun s _ ↦ f s) I) :
    I t =ᵐ[P] hW.toIsPreBrownianReal.wienerIntegral t (hf.toLp f) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hf_prod : MemLp (Function.uncurry fun s (_ : Ω) ↦ f s) 2 ((timeMeasure t).prod P) :=
    (hf.comp_measurePreserving (measurePreserving_fst (μ := timeMeasure t) (ν := P))).ae_eq
      (.of_forall fun _ ↦ rfl)
  have hfp := (ℱ.memLp_predictableMeasure_iff P hI.isStronglyPredictable t 2).mpr hf_prod
  have hl2 : hfp.toLp (Function.uncurry fun s (_ : Ω) ↦ f s) =
      (hf.comp_measurePreserving (ℱ.measurePreserving_fst_predictableMeasure P t)).toLp
        (fun p : ℝ≥0 × Ω ↦ f p.1) :=
    Lp.ext (hfp.coeFn_toLp.trans
      ((hf.comp_measurePreserving
        (ℱ.measurePreserving_fst_predictableMeasure P t)).coeFn_toLp.mono fun _ h ↦ h.symm))
  have hcomp := (Lp.toLp_compMeasurePreserving hf
    (ℱ.measurePreserving_fst_predictableMeasure P t)).symm
  dsimp only [Function.comp_def] at hcomp
  refine (hW.ae_eq_l2Integral_of_memLp hf_prod hI).trans ?_
  rw [hl2, hcomp, hW.l2Integral_compMeasurePreserving_fst t (hf.toLp f)]

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

end IsFilteredPreBrownianReal

namespace IsItoIntegral

variable {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω} {W H I : ℝ≥0 → Ω → ℝ}

/-- **`L²(P)` time continuity**: the `L²(P)` class `t ↦ (hI.memLp hW hH t).toLp (I t)` of a
continuous Itô integral of a `BrownianIntegrable` integrand varies continuously in `t`, without
assuming path continuity of `W`. -/
theorem continuous_toLp (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) :
    Continuous fun t : ℝ≥0 ↦ (hI.memLp hW hH t).toLp (I t) := by
  simpa only [hI.toLp_eq_l2Integral hW hH] using hW.continuous_l2Integral hH

/-- Every continuous Itô integral of a `BrownianIntegrable` integrand has expectation zero at every
horizon, without assuming path continuity of `W` or adaptation of `I`. -/
theorem integral_eq_zero (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    ∫ ω, I T ω ∂P = 0 :=
  (integral_congr_ae (hI.ae_eq_l2Integral hW hH T)).trans (hW.integral_l2Integral T _)

end IsItoIntegral

end TauCeti.Probability

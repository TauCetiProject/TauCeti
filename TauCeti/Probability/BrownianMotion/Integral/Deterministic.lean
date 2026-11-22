/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.L2
public import TauCeti.Probability.BrownianMotion.Integral.Wiener
import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreserving.Equiv

/-!
# Deterministic integrands in the predictable Brownian integral

For a Brownian motion relative to an arbitrary filtration, the predictable L² integral
of a deterministic integrand equals its Wiener integral. Deterministic time L² classes
are viewed as predictable classes using Mathlib's native pullback
`Lp.compMeasurePreserving` along the time projection, bundled as the linear isometry
`Lp.compMeasurePreservingₗᵢ` (`l2Integral_compMeasurePreserving_fst`). For a
`BrownianIntegrable` deterministic integrand `fun t _ ↦ f t`,
`l2Integral_toPredictableLp_fst` identifies `hW.l2Integral T (hH.toPredictableLp T)` with
`hW.toIsPreBrownianReal.wienerIntegral T (hf.toLp f)`, and
`ae_eq_wienerIntegral_of_ae_eq_l2Integral` transfers this equality to any modification of the
integral process. These comparisons concern the terminal L² integral at a finite horizon and
need no sample-path continuity.

The identification follows from the common elementary increment formula and continuity
of the two linear maps, using the uniqueness theorem for the Wiener integral.

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

/-- The predictable Brownian integral agrees with the Wiener integral on every
deterministic L² class, embedded by isometric pullback along the time projection. -/
@[simp]
theorem l2Integral_compMeasurePreserving_fst (hW : IsFilteredPreBrownianReal ℱ W P)
    (T : ℝ≥0) (f : Lp ℝ 2 (timeMeasure T)) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    letI : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    hW.l2Integral T
        (Lp.compMeasurePreserving Prod.fst
          (ℱ.measurePreserving_fst_predictableMeasure P T) f) =
      hW.toIsPreBrownianReal.wienerIntegral T f := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let hf := ℱ.measurePreserving_fst_predictableMeasure P T
  have hmap : (hW.l2Integral T).toContinuousLinearMap.comp
      (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst hf).toContinuousLinearMap =
      (hW.toIsPreBrownianReal.wienerIntegral T).toContinuousLinearMap := by
    apply hW.toIsPreBrownianReal.eq_wienerIntegral T
    intro t ht
    have hstep : Lp.compMeasurePreservingₗᵢ ℝ Prod.fst hf
        (indicatorConstLp 2 (measurableSet_Iic (a := t)) (measure_ne_top _ _) (1 : ℝ)) =
        indicatorConstLp 2
          (measurableSet_predictable_Ioc_prod 0 t (𝓕 := ℱ) MeasurableSet.univ)
          (measure_ne_top _ _) 1 := by
      rw [Lp.compMeasurePreservingₗᵢ_apply, Lp.indicatorConstLp_compMeasurePreserving,
        indicatorConstLp_inj _ _ _ _ one_ne_zero]
      filter_upwards [hf.quasiMeasurePreserving.ae (ae_mem_Ioc_timeMeasure T)] with p hp
      simp [hp.1]
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      hstep]
    apply Lp.ext
    filter_upwards [hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod_of_le
      (s := 0) (t := t) bot_le ht MeasurableSet.univ 1,
      hW.toIsPreBrownianReal.coeFn_toL2 t,
      hW.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω htω hzero
    simpa only [indicator_univ, one_mul, hzero, sub_zero, htω] using hω
  simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    Lp.compMeasurePreservingₗᵢ_apply] using
    congrArg (fun J : Lp ℝ 2 (timeMeasure T) →L[ℝ] Lp ℝ 2 P ↦ J f) hmap

/-- For a deterministic integrand `f` whose time-constant lifting `fun t _ ↦ f t` is
`BrownianIntegrable`, its finite-horizon predictable `L²` Brownian integral equals the
deterministic Wiener integral of `f` in `Lp ℝ 2 P`. -/
theorem l2Integral_toPredictableLp_fst (hW : IsFilteredPreBrownianReal ℱ W P)
    {f : ℝ≥0 → ℝ} {T : ℝ≥0} (hf : MemLp f 2 (timeMeasure T))
    (hH : BrownianIntegrable ℱ P (fun t _ ↦ f t)) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    hW.l2Integral T (hH.toPredictableLp T) =
      hW.toIsPreBrownianReal.wienerIntegral T (hf.toLp f) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hcomp : Lp.compMeasurePreserving Prod.fst
      (ℱ.measurePreserving_fst_predictableMeasure P T) (hf.toLp f) =
      hH.toPredictableLp T := by
    apply Lp.ext
    refine (Lp.coeFn_compMeasurePreserving (hf.toLp f)
      (ℱ.measurePreserving_fst_predictableMeasure P T)).trans ?_
    filter_upwards [(ℱ.measurePreserving_fst_predictableMeasure P T).quasiMeasurePreserving.ae
      hf.coeFn_toLp, hH.coeFn_toPredictableLp T] with ⟨t, ω⟩ h1 h2
    exact h1.trans h2.symm
  rw [← hcomp]
  exact hW.l2Integral_compMeasurePreserving_fst T (hf.toLp f)

/-- Any process agreeing almost surely at time `T` with the predictable `L²` integral of a
deterministic integrand agrees almost surely at `T` with its Wiener integral. -/
theorem ae_eq_wienerIntegral_of_ae_eq_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    {f : ℝ≥0 → ℝ} {T : ℝ≥0} (hf : MemLp f 2 (timeMeasure T))
    (hH : BrownianIntegrable ℱ P (fun t _ ↦ f t)) {I : ℝ≥0 → Ω → ℝ}
    (hI : I T =ᵐ[P] hW.l2Integral T (hH.toPredictableLp T)) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    I T =ᵐ[P] hW.toIsPreBrownianReal.wienerIntegral T (hf.toLp f) :=
  hI.trans (by rw [hW.l2Integral_toPredictableLp_fst hf hH])

end TauCeti.Probability.IsFilteredPreBrownianReal

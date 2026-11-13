/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.L2
public import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Process.ElementaryDensity
import TauCeti.Probability.Martingale.Basic

/-!
# Martingale consistency of the predictable L² Brownian integral

Conditional expectation of a terminal Brownian integral at an earlier deterministic time
is the integral of the restricted integrand. Consequently, the terminal L² maps determine
a square-integrable martingale for every predictable integrand of locally finite expected
square energy, on the original raw filtration.

The martingale has the specified integral value almost surely at each fixed time. No sample
path continuity or simultaneous-time integral identity is asserted here. In particular,
this construction does not identify arbitrary representatives of L² classes as adapted.

The proof extends the conditional identity on predictable rectangles by continuity, using
Mathlib's L² conditional expectation and the existing terminal integral isometry.

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

private theorem condExp_rectangle (hW : IsFilteredPreBrownianReal ℱ W P)
    {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[ℱ s] A) (S : ℝ≥0) :
    P[A.indicator (W t - W s) | ℱ S] =ᵐ[P]
      A.indicator (W (max s (min t S)) - W s) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have hM := (hW.martingale.const_min t).sub (hW.martingale.const_min s)
  have hmul := hM.mul_left_of_eq_zero (r := s) (a := A.indicator 1)
    (fun u hus ↦ by simp only [Pi.sub_apply, min_eq_right (hus.trans hst),
      min_eq_right hus, sub_self])
    (stronglyMeasurable_const.indicator hA)
    (fun u ↦ by
      simpa only [Pi.mul_def, ← indicator_mul_left, Pi.one_apply, one_mul] using
        (hM.integrable u).indicator (ℱ.le s _ hA))
  have hcond := hmul.condExp_ae_eq (le_max_right t S)
  dsimp only [Pi.sub_apply] at hcond
  simp only [min_eq_left (le_max_left t S), min_eq_left (hst.trans (le_max_left t S)),
    Pi.mul_def, ← indicator_mul_left, Pi.one_apply, one_mul] at hcond
  by_cases hSs : S ≤ s
  · simpa only [min_eq_right (hSs.trans hst), min_eq_right hSs, max_eq_left hSs,
      sub_self] using hcond
  · simpa only [min_eq_left (le_of_not_ge hSs),
      max_eq_right (le_min hst (le_of_not_ge hSs))] using hcond

/-- Conditioning a terminal integral on an earlier date gives the integral of its restriction.
The restricted input may be any L² class agreeing with the original input on the shorter
horizon; no choice of representatives or usual conditions on the filtration is needed. -/
theorem condExp_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    {S T : ℝ≥0} (hST : S ≤ T) (f : Lp ℝ 2 (ℱ.predictableMeasure P T))
    (g : Lp ℝ 2 (ℱ.predictableMeasure P S))
    (hfg : g =ᵐ[ℱ.predictableMeasure P S] f) :
    P[hW.l2Integral T f | ℱ S] =ᵐ[P] hW.l2Integral S g := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  -- Restriction and conditional expectation are continuous linear maps on L² classes.
  let R : Lp ℝ 2 (ℱ.predictableMeasure P T) →L[ℝ]
      Lp ℝ 2 (ℱ.predictableMeasure P S) :=
    Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
      (by simpa using ℱ.predictableMeasure_mono P hST)
  have hR (u : Lp ℝ 2 (ℱ.predictableMeasure P T)) :
      R u =ᵐ[ℱ.predictableMeasure P S] u :=
    Lp.coeFn_LpToLpOfMeasureLeSMul _ _ u
  let C : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P :=
    (lpMeas ℝ ℝ (ℱ S) 2 P).subtypeL.comp (condExpL2 ℝ ℝ (ℱ.le S))
  have hC (u : Lp ℝ 2 P) : C u =ᵐ[P] P[u | ℱ S] := by
    have hh := (Lp.memLp u).condExpL2_ae_eq_condExp (𝕜 := ℝ) (ℱ.le S)
    rw [Lp.toLp_coeFn] at hh
    exact hh
  -- It suffices to compare these maps on the dense predictable rectangles.
  have hmaps : C.comp (hW.l2Integral T).toContinuousLinearMap =
      (hW.l2Integral S).toContinuousLinearMap.comp R := by
    apply ContinuousLinearMap.ext_indicatorConstLp_Ioc_prod_predictableMeasure T
    intro s t hst ht A hA
    let u := indicatorConstLp (μ := ℱ.predictableMeasure P T) 2
      (measurableSet_predictable_Ioc_prod s t hA) (measure_ne_top _ _) (1 : ℝ)
    have hRu : R u = indicatorConstLp (μ := ℱ.predictableMeasure P S) 2
        (measurableSet_predictable_Ioc_prod s t hA) (measure_ne_top _ _) 1 := by
      apply Lp.ext
      exact (hR u).trans ((indicatorConstLp_coeFn.filter_mono
        (ae_mono (ℱ.predictableMeasure_mono P hST))).trans indicatorConstLp_coeFn.symm)
    dsimp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
    rw [hRu]
    apply Lp.ext
    refine (hC (hW.l2Integral T u)).trans ?_
    have hterminal := hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod_of_le hst.le ht hA 1
    have hshort := hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod S s t hA 1
    simp only [Set.indicator, ite_mul, one_mul, zero_mul] at hterminal hshort
    exact (condExp_congr_ae hterminal).trans
      ((condExp_rectangle hW hst.le hA S).trans hshort.symm)
  have hg : R f = g := Lp.ext ((hR f).trans hfg.symm)
  exact (hC (hW.l2Integral T f)).symm.trans
    (by simpa only [ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, hg] using
        Lp.ext_iff.mp (congrArg (fun J : Lp ℝ 2 (ℱ.predictableMeasure P T) →L[ℝ]
          Lp ℝ 2 P ↦ J f) hmaps))

/-- Predictable L² inputs on every finite horizon determine a square-integrable martingale
on the raw filtration. The chosen values agree with the terminal integral classes at each
fixed time; this asserts neither path continuity nor indistinguishability of arbitrary
representatives of those classes. Literal predictability of `H` is unnecessary: membership
in predictable L² already supplies the required a.e. measurable classes. -/
theorem exists_martingale_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H : ℝ≥0 × Ω → ℝ} (hH : ∀ t, MemLp H 2 (ℱ.predictableMeasure P t)) :
    ∃ I : ℝ≥0 → Ω → ℝ, Martingale I ℱ P ∧
      (∀ t, I t =ᵐ[P] hW.l2Integral t ((hH t).toLp H)) ∧
      ∀ t, MemLp (I t) 2 P := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let J (t : ℝ≥0) := hW.l2Integral t ((hH t).toLp H)
  let I (t : ℝ≥0) := P[J t | ℱ t]
  have hI (t : ℝ≥0) : I t =ᵐ[P] J t :=
    hW.condExp_l2Integral le_rfl _ _ Filter.EventuallyEq.rfl
  have hrestrict {s t : ℝ≥0} (hst : s ≤ t) :
      (hH s).toLp H =ᵐ[ℱ.predictableMeasure P s] (hH t).toLp H :=
    (hH s).coeFn_toLp.trans (((hH t).coeFn_toLp.filter_mono
      (ae_mono (ℱ.predictableMeasure_mono P hst))).symm)
  refine ⟨I, ⟨fun _ ↦ stronglyMeasurable_condExp, fun s t hst ↦ ?_⟩, hI, ?_⟩
  · exact (condExp_congr_ae (hI t)).trans
      ((hW.condExp_l2Integral hst _ _ (hrestrict hst)).trans (hI s).symm)
  · exact fun t ↦ (Lp.memLp (J t)).ae_eq (hI t).symm

end TauCeti.Probability.IsFilteredPreBrownianReal

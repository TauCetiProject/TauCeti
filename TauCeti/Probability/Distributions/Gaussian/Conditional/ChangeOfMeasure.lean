/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Independence.CondExp
public import TauCeti.Probability.Distributions.Tilted

/-!
# Gaussian change of measure with a known random drift

Let `Y` have law `N(0,v)` independently of a sigma algebra `m`, and let `a` be
`m`-measurable. Under the density `exp(a Y - v a²/2)`, the corrected variable
`Y - v a` again has law `N(0,v)` and is independent of `m`. The new measure agrees
with the original one on `m` and has exactly the same null sets.

No boundedness or moment assumption on `a` is necessary for this single-step
change of measure. In particular, this calculation applies to a predictable
Brownian drift frozen at the left endpoint of an interval. It does not assert
normality of the uncorrected randomly shifted variable.

The calculation uses `gaussianReal_tilted_mul` for each fixed coefficient and
`map_restrict_prodMk_eq_prod_of_indep` to freeze a coefficient on a past event.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second
  edition, Springer, 1991, §3.5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {a Y : Ω → ℝ} {v : ℝ≥0}

/-- **One-step random-drift change of law.** A past event and a corrected Gaussian
increment factor under the normalized exponential density, even for unbounded
past-measurable coefficients. -/
theorem withDensity_gaussian_exp_inter_preimage (hm : m ≤ mΩ)
    (ha : Measurable[m] a) (hY : Measurable Y)
    (hind : Indep (.comap Y inferInstance) m P)
    (hlaw : HasLaw Y (gaussianReal 0 v) P)
    {A : Set Ω} (hA : MeasurableSet[m] A) {B : Set ℝ} (hB : MeasurableSet B) :
    P.withDensity (fun ω ↦ ENNReal.ofReal (exp (a ω * Y ω - v * a ω ^ 2 / 2)))
        (A ∩ (fun ω ↦ Y ω - v * a ω) ⁻¹' B) = P A * gaussianReal 0 v B := by
  have := hlaw.isProbabilityMeasure
  have ha' : Measurable a := ha.mono hm le_rfl
  let F : ℝ × ℝ → ℝ≥0∞ := fun z ↦
    ENNReal.ofReal (exp (z.1 * z.2 - v * z.1 ^ 2 / 2)) *
      B.indicator 1 (z.2 - v * z.1)
  have hF : Measurable F := by
    exact (by fun_prop : Measurable fun z : ℝ × ℝ ↦
      ENNReal.ofReal (exp (z.1 * z.2 - v * z.1 ^ 2 / 2))).mul
        ((measurable_const.indicator hB).comp (by fun_prop))
  -- For each fixed coefficient, tilt the Gaussian and translate its mean back to zero.
  have hfreeze (c : ℝ) : ∫⁻ y, F (c, y) ∂gaussianReal 0 v = gaussianReal 0 v B := by
    have hZ : ∫ y, exp (c * y) ∂gaussianReal 0 v = exp ((v : ℝ) * c ^ 2 / 2) := by
      simpa [mgf] using congrFun (mgf_id_gaussianReal (μ := 0) (v := v)) c
    have htilt : (gaussianReal 0 v).withDensity
        (fun y ↦ ENNReal.ofReal (exp (c * y - v * c ^ 2 / 2))) =
        gaussianReal (v * c) v := by
      have ht := gaussianReal_tilted_mul 0 v c
      simp only [zero_add, Measure.tilted, hZ, exp_sub] at ht ⊢
      exact ht
    have hmap : (gaussianReal (v * c) v).map (fun y ↦ y - v * c) =
        gaussianReal 0 v := by
      simpa using (gaussianReal_map_sub_const (μ := (v : ℝ) * c) (v := v) (v * c))
    calc
      _ = ∫⁻ y, B.indicator 1 (y - v * c) ∂(gaussianReal 0 v).withDensity
          (fun y ↦ ENNReal.ofReal (exp (c * y - v * c ^ 2 / 2))) := by
        exact (lintegral_withDensity_eq_lintegral_mul (gaussianReal 0 v)
          (f := fun y ↦ ENNReal.ofReal (exp (c * y - v * c ^ 2 / 2))) (by fun_prop)
          (g := fun y ↦ B.indicator 1 (y - v * c))
          ((measurable_one.indicator hB).comp (by fun_prop))).symm
      _ = ∫⁻ y, B.indicator 1 y ∂gaussianReal 0 v := by
        rw [htilt]
        exact (lintegral_map (measurable_const.indicator hB)
          (by fun_prop : Measurable fun y : ℝ ↦ y - v * c)).symm.trans
            (congrArg (fun μ : Measure ℝ ↦ ∫⁻ y, B.indicator 1 y ∂μ) hmap)
      _ = _ := lintegral_indicator_one hB
  -- Independence gives the product law even after restriction to the past event A.
  have hAB : MeasurableSet (A ∩ (fun ω ↦ Y ω - v * a ω) ⁻¹' B) :=
    (hm A hA).inter (hB.preimage (hY.sub (ha'.const_mul _)))
  calc
    _ = ∫⁻ ω in A, F (a ω, Y ω) ∂P := by
      rw [withDensity_apply _ hAB, ← lintegral_indicator hAB,
        ← lintegral_indicator (hm A hA)]
      apply lintegral_congr
      intro ω
      by_cases hωA : ω ∈ A <;> by_cases hωB : Y ω - v * a ω ∈ B <;>
        simp [F, hωA, hωB]
    _ = ∫⁻ z, F z ∂(P.restrict A).map (fun ω ↦ (a ω, Y ω)) :=
      (lintegral_map hF (ha'.prodMk hY)).symm
    _ = ∫⁻ c, ∫⁻ y, F (c, y) ∂gaussianReal 0 v ∂(P.restrict A).map a := by
      rw [map_restrict_prodMk_eq_prod_of_indep hm ha hY hind hA, hlaw.map_eq,
        lintegral_prod _ hF.aemeasurable]
    _ = P A * gaussianReal 0 v B := by
      simp only [hfreeze, lintegral_const, Measure.map_apply ha' MeasurableSet.univ,
        preimage_univ, Measure.restrict_apply_univ]
      rw [mul_comm]

/-- The one-step Gaussian density preserves the measure of every past event. -/
theorem withDensity_gaussian_exp_apply (hm : m ≤ mΩ)
    (ha : Measurable[m] a) (hY : Measurable Y)
    (hind : Indep (.comap Y inferInstance) m P)
    (hlaw : HasLaw Y (gaussianReal 0 v) P)
    {A : Set Ω} (hA : MeasurableSet[m] A) :
    P.withDensity (fun ω ↦ ENNReal.ofReal (exp (a ω * Y ω - v * a ω ^ 2 / 2))) A = P A := by
  simpa using withDensity_gaussian_exp_inter_preimage hm ha hY hind hlaw hA
    MeasurableSet.univ

/-- A Gaussian exponential with an arbitrary known random coefficient defines a
probability measure; no integrability premise on that coefficient is needed. -/
theorem isProbabilityMeasure_withDensity_gaussian_exp (hm : m ≤ mΩ)
    (ha : Measurable[m] a) (hY : Measurable Y)
    (hind : Indep (.comap Y inferInstance) m P)
    (hlaw : HasLaw Y (gaussianReal 0 v) P) :
    IsProbabilityMeasure
      (P.withDensity (fun ω ↦ ENNReal.ofReal (exp (a ω * Y ω - v * a ω ^ 2 / 2)))) := by
  have := hlaw.isProbabilityMeasure
  exact ⟨by rw [withDensity_gaussian_exp_apply hm ha hY hind hlaw MeasurableSet.univ,
    measure_univ]⟩

/-- Under the one-step density the drift-corrected variable is centered Gaussian,
including at variance zero. -/
theorem hasLaw_sub_mul_withDensity_gaussian_exp (hm : m ≤ mΩ)
    (ha : Measurable[m] a) (hY : Measurable Y)
    (hind : Indep (.comap Y inferInstance) m P)
    (hlaw : HasLaw Y (gaussianReal 0 v) P) :
    HasLaw (fun ω ↦ Y ω - v * a ω) (gaussianReal 0 v)
      (P.withDensity (fun ω ↦ ENNReal.ofReal (exp (a ω * Y ω - v * a ω ^ 2 / 2)))) := by
  have := hlaw.isProbabilityMeasure
  refine ⟨(hY.sub ((ha.mono hm le_rfl).const_mul _)).aemeasurable, Measure.ext fun B hB ↦ ?_⟩
  have hD : Measurable (fun ω ↦ Y ω - v * a ω) :=
    hY.sub ((ha.mono hm le_rfl).const_mul _)
  rw [Measure.map_apply hD hB]
  simpa using withDensity_gaussian_exp_inter_preimage hm ha hY hind hlaw
    (A := univ) MeasurableSet.univ hB

/-- The corrected Gaussian variable is independent of the entire past sigma algebra
under the changed measure, not just uncorrelated with the random drift. -/
theorem indep_sub_mul_withDensity_gaussian_exp (hm : m ≤ mΩ)
    (ha : Measurable[m] a) (hY : Measurable Y)
    (hind : Indep (.comap Y inferInstance) m P)
    (hlaw : HasLaw Y (gaussianReal 0 v) P) :
    Indep (.comap (fun ω ↦ Y ω - v * a ω) inferInstance) m
      (P.withDensity (fun ω ↦ ENNReal.ofReal (exp (a ω * Y ω - v * a ω ^ 2 / 2)))) := by
  rw [Indep_iff]
  intro B A hB hA
  obtain ⟨B, hBmeas, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hB
  have hD : Measurable (fun ω ↦ Y ω - v * a ω) :=
    hY.sub ((ha.mono hm le_rfl).const_mul _)
  rw [inter_comm, withDensity_gaussian_exp_inter_preimage hm ha hY hind hlaw hA hBmeas,
    withDensity_gaussian_exp_apply hm ha hY hind hlaw hA,
    ← (hasLaw_sub_mul_withDensity_gaussian_exp hm ha hY hind hlaw).map_eq,
    Measure.map_apply hD hBmeas, mul_comm]

end TauCeti.Probability

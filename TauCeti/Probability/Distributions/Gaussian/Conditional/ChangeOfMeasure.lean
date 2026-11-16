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
`Y - v a` again has law `N(0,v)` and is independent of `m`. The new measure is a
probability measure agreeing with the original one on `m`.

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
theorem withDensity_exp_inter_preimage_of_indep_gaussian (hm : m ≤ mΩ)
    (ha : Measurable[m] a)
    (hind : Indep (.comap Y inferInstance) m P)
    (hlaw : HasLaw Y (gaussianReal 0 v) P)
    {A : Set Ω} (hA : MeasurableSet[m] A) {B : Set ℝ} (hB : MeasurableSet B) :
    P.withDensity (fun ω ↦ ENNReal.ofReal (exp (a ω * Y ω - v * a ω ^ 2 / 2)))
        (A ∩ (fun ω ↦ Y ω - v * a ω) ⁻¹' B) = P A * gaussianReal 0 v B := by
  have := hlaw.isProbabilityMeasure
  have ha' : Measurable a := ha.mono hm le_rfl
  have hY := hlaw.aemeasurable
  -- Replace the increment only in the product-law argument; all set evaluations
  -- below use null measurability, so no pointwise measurability is needed.
  have hind' : Indep (.comap (hY.mk Y) inferInstance) m P := by
    have h : @IndepFun Ω ℝ Ω mΩ _ m Y id P := by
      simpa [IndepFun_iff_Indep] using hind
    simpa [IndepFun_iff_Indep] using h.congr hY.ae_eq_mk Filter.EventuallyEq.rfl
  have hprod : (P.restrict A).map (fun ω ↦ (a ω, Y ω)) =
      ((P.restrict A).map a).prod (P.map Y) := by
    calc
      _ = (P.restrict A).map (fun ω ↦ (a ω, hY.mk Y ω)) :=
        Measure.map_congr (by
          filter_upwards [ae_restrict_of_ae hY.ae_eq_mk] with ω hω
          exact congrArg (fun y ↦ (a ω, y)) hω)
      _ = ((P.restrict A).map a).prod (P.map (hY.mk Y)) :=
        map_restrict_prodMk_eq_prod_of_indep hm ha hY.measurable_mk hind' hA
      _ = _ := by rw [Measure.map_congr hY.ae_eq_mk]
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
  have hAB : NullMeasurableSet (A ∩ (fun ω ↦ Y ω - v * a ω) ⁻¹' B) P :=
    (hm A hA).nullMeasurableSet.inter
      ((hY.sub (ha'.aemeasurable.const_mul _)).nullMeasurableSet_preimage hB)
  calc
    _ = ∫⁻ ω in A, F (a ω, Y ω) ∂P := by
      rw [withDensity_apply₀ _ hAB, ← lintegral_indicator₀ hAB,
        ← lintegral_indicator (hm A hA)]
      apply lintegral_congr
      intro ω
      by_cases hωA : ω ∈ A <;> by_cases hωB : Y ω - v * a ω ∈ B <;>
        simp [F, hωA, hωB]
    _ = ∫⁻ z, F z ∂(P.restrict A).map (fun ω ↦ (a ω, Y ω)) :=
      (lintegral_map' hF.aemeasurable (ha'.aemeasurable.prodMk hY).restrict).symm
    _ = ∫⁻ c, ∫⁻ y, F (c, y) ∂gaussianReal 0 v ∂(P.restrict A).map a := by
      rw [hprod, hlaw.map_eq, lintegral_prod _ hF.aemeasurable]
    _ = P A * gaussianReal 0 v B := by
      simp only [hfreeze, lintegral_const, Measure.map_apply ha' MeasurableSet.univ,
        preimage_univ, Measure.restrict_apply_univ]
      rw [mul_comm]

/-- The one-step Gaussian density preserves the measure of every past event. -/
theorem withDensity_exp_apply_of_indep_gaussian (hm : m ≤ mΩ)
    (ha : Measurable[m] a)
    (hind : Indep (.comap Y inferInstance) m P)
    (hlaw : HasLaw Y (gaussianReal 0 v) P)
    {A : Set Ω} (hA : MeasurableSet[m] A) :
    P.withDensity (fun ω ↦ ENNReal.ofReal (exp (a ω * Y ω - v * a ω ^ 2 / 2))) A = P A := by
  simpa using withDensity_exp_inter_preimage_of_indep_gaussian hm ha hind hlaw hA
    MeasurableSet.univ

/-- Under the one-step density the drift-corrected variable is centered Gaussian,
including at variance zero. Only a.e. measurability of the independent coefficient
is required. -/
theorem hasLaw_sub_mul_gaussianReal_withDensity_exp_of_indep_gaussian
    (ha : AEMeasurable a P) (hind : IndepFun a Y P)
    (hlaw : HasLaw Y (gaussianReal 0 v) P) :
    HasLaw (fun ω ↦ Y ω - v * a ω) (gaussianReal 0 v)
      (P.withDensity (fun ω ↦ ENNReal.ofReal (exp (a ω * Y ω - v * a ω ^ 2 / 2)))) := by
  have := hlaw.isProbabilityMeasure
  have hQ : P.withDensity (fun ω ↦ ENNReal.ofReal (exp (a ω * Y ω - v * a ω ^ 2 / 2))) =
      P.withDensity (fun ω ↦ ENNReal.ofReal (exp (ha.mk a ω * Y ω - v * ha.mk a ω ^ 2 / 2))) :=
    withDensity_congr_ae (by filter_upwards [ha.ae_eq_mk] with ω hω; rw [hω])
  rw [hQ]
  have hind' : Indep (.comap Y inferInstance) (.comap (ha.mk a) inferInstance) P :=
    (hind.congr ha.ae_eq_mk Filter.EventuallyEq.rfl).symm
  have hD : AEMeasurable (fun ω ↦ Y ω - v * ha.mk a ω) P :=
    hlaw.aemeasurable.sub (ha.measurable_mk.aemeasurable.const_mul (v : ℝ))
  have hlaw' : HasLaw (fun ω ↦ Y ω - v * ha.mk a ω) (gaussianReal 0 v)
      (P.withDensity (fun ω ↦ ENNReal.ofReal (exp (ha.mk a ω * Y ω - v * ha.mk a ω ^ 2 / 2)))) := by
    refine ⟨hD.mono_ac (withDensity_absolutelyContinuous _ _), Measure.ext fun B hB ↦ ?_⟩
    rw [Measure.map_apply_of_aemeasurable (hD.mono_ac (withDensity_absolutelyContinuous _ _)) hB]
    simpa using withDensity_exp_inter_preimage_of_indep_gaussian
      ha.measurable_mk.comap_le (Measurable.of_comap_le le_rfl) hind' hlaw
      (A := univ) MeasurableSet.univ hB
  exact hlaw'.congr ((withDensity_absolutelyContinuous _ _).ae_eq
    (by filter_upwards [ha.ae_eq_mk] with ω hω; rw [hω]))

/-- A Gaussian exponential with an arbitrary independent random coefficient defines
a probability measure; no integrability premise on that coefficient is needed. -/
theorem isProbabilityMeasure_withDensity_exp_of_indep_gaussian
    (ha : AEMeasurable a P) (hind : IndepFun a Y P)
    (hlaw : HasLaw Y (gaussianReal 0 v) P) :
    IsProbabilityMeasure
      (P.withDensity (fun ω ↦ ENNReal.ofReal (exp (a ω * Y ω - v * a ω ^ 2 / 2)))) :=
  (hasLaw_sub_mul_gaussianReal_withDensity_exp_of_indep_gaussian ha hind hlaw).isProbabilityMeasure

/-- The corrected Gaussian variable is independent of the entire past sigma algebra
under the changed measure, not just uncorrelated with the random drift. -/
theorem indep_sub_mul_withDensity_exp_of_indep_gaussian (hm : m ≤ mΩ)
    (ha : Measurable[m] a)
    (hind : Indep (.comap Y inferInstance) m P)
    (hlaw : HasLaw Y (gaussianReal 0 v) P) :
    Indep (.comap (fun ω ↦ Y ω - v * a ω) inferInstance) m
      (P.withDensity (fun ω ↦ ENNReal.ofReal (exp (a ω * Y ω - v * a ω ^ 2 / 2)))) := by
  rw [Indep_iff]
  intro B A hB hA
  obtain ⟨B, hBmeas, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hB
  have h := hasLaw_sub_mul_gaussianReal_withDensity_exp_of_indep_gaussian
    (ha.mono hm le_rfl).aemeasurable (indep_of_indep_of_le_left hind.symm ha.comap_le) hlaw
  rw [inter_comm, withDensity_exp_inter_preimage_of_indep_gaussian hm ha hind hlaw hA hBmeas,
    withDensity_exp_apply_of_indep_gaussian hm ha hind hlaw hA,
    ← h.map_eq, Measure.map_apply_of_aemeasurable h.aemeasurable hBmeas, mul_comm]

end TauCeti.Probability

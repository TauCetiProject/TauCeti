/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Measure.Real
public import TauCeti.Probability.Distributions.FisherSnedecor.ChiSquared
public import TauCeti.Probability.Distributions.Gaussian.ChiSquared
public import TauCeti.Probability.Distributions.StudentT.Cdf

/-!
# Student t laws as Gaussian--chi-squared ratios

This file proves the classical construction of a Student t variable: divide a standard Gaussian
variable by the square root of an independent chi-squared variable divided by its degrees of
freedom. The measure-level identity is primary, and a `HasLaw` formulation records the exact
independence assumptions needed for random variables.

The proof first identifies the square of a Student t law with the Fisher--Snedecor law of
parameters `1` and `ν`.  The candidate ratio has the same squared law by the Gaussian-square and
chi-squared-ratio identities, and both laws are invariant under reflection.  Extensionality for
symmetric real probability measures then identifies them.

## Main results

* `TauCeti.Probability.studentTMeasure_map_sq` — squaring a Student t variable gives an
  `F(1, ν)` variable;
* `TauCeti.Probability.map_div_sqrt_chiSquaredMeasure` — the measure-level Gaussian--chi-squared
  ratio identity;
* `TauCeti.Probability.hasLaw_studentT_of_gaussian_chiSquared` — the corresponding random-variable
  theorem.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), ch. 28.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti

namespace Probability

/-- The square of a Student t law with `ν > 0` degrees of freedom is the Fisher--Snedecor law
with parameters `1` and `ν`. -/
@[simp]
theorem studentTMeasure_map_sq {ν : ℝ} (hν : 0 < ν) :
    (studentTMeasure ν).map (fun x : ℝ ↦ x ^ 2) = fisherSnedecorMeasure 1 ν := by
  let _ : IsProbabilityMeasure (studentTMeasure ν) :=
    isProbabilityMeasure_studentTMeasure hν
  let _ : IsProbabilityMeasure (fisherSnedecorMeasure 1 ν) :=
    isProbabilityMeasure_fisherSnedecorMeasure one_pos hν
  apply Measure.eq_of_cdf
  ext x
  rw [cdf_eq_real, map_measureReal_apply (by fun_prop) measurableSet_Iic,
    cdf_fisherSnedecorMeasure_eq one_pos hν]
  by_cases hx : x < 0
  · have hpreimage : (fun y : ℝ ↦ y ^ 2) ⁻¹' Iic x = ∅ := by
      ext y
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact fun hy ↦ (not_le_of_gt hx) ((sq_nonneg y).trans hy)
    rw [hpreimage, measureReal_empty, ite_eq_left hx.le]
  · have hx0 : 0 ≤ x := le_of_not_gt hx
    have hpreimage : (fun y : ℝ ↦ y ^ 2) ⁻¹' Iic x = Icc (-√x) √x := by
      ext y
      simp only [mem_preimage, mem_Iic, mem_Icc]
      constructor
      · exact fun hy ↦ abs_le.mp (Real.abs_le_sqrt hy)
      · intro hy
        rw [← Real.sq_sqrt hx0]
        exact sq_le_sq' hy.1 hy.2
    rw [hpreimage]
    let _ : NullSingletonClass (studentTMeasure ν) := by
      rw [studentTMeasure_def]
      infer_instance
    by_cases hxzero : x = 0
    · subst x
      simp [Measure.real]
    · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hxzero)
      have hsqrtpos : 0 < √x := Real.sqrt_pos.2 hxpos
      have hIoc :
          (studentTMeasure ν).real (Ioc (-√x) √x) =
            cdf (studentTMeasure ν) √x - cdf (studentTMeasure ν) (-√x) := by
        calc
          (studentTMeasure ν).real (Ioc (-√x) √x) =
              (cdf (studentTMeasure ν)).measure.real (Ioc (-√x) √x) := by
            rw [measure_cdf]
          _ = cdf (studentTMeasure ν) √x - cdf (studentTMeasure ν) (-√x) := by
            rw [Measure.real, StieltjesFunction.measure_Ioc, ENNReal.toReal_ofReal]
            exact sub_nonneg.mpr ((cdf (studentTMeasure ν)).mono (by linarith))
      rw [← measureReal_congr (Ioc_ae_eq_Icc (a := -√x) (b := √x)), hIoc,
        cdf_studentTMeasure_eq hν, cdf_studentTMeasure_eq hν,
        ite_eq_right (not_lt_of_ge (Real.sqrt_nonneg x)),
        ite_eq_left (neg_lt_zero.mpr hsqrtpos), ite_eq_right (not_le_of_gt hxpos), neg_sq,
        Real.sq_sqrt hx0]
      have hb : 0 < ν / 2 := by linarith
      have harg : 1 - x / (ν + x) = ν / (ν + x) := by
        field_simp
        ring
      have hFarg : 1 * x / (ν + 1 * x) = x / (ν + x) := by ring
      -- The beta reflection formula turns the symmetric Student interval into the `F(1, ν)` cdf.
      rw [hFarg, regularizedIncompleteBeta_symm one_half_pos hb (x / (ν + x)), harg]
      ring

/-- Dividing a standard Gaussian law by the square root of an independent chi-squared law,
normalised by its positive degrees of freedom `ν`, gives the Student t law with `ν` degrees of
freedom. -/
theorem map_div_sqrt_chiSquaredMeasure {ν : ℝ} (hν : 0 < ν) :
    ((gaussianReal 0 1).prod (chiSquaredMeasure ν)).map
        (fun z : ℝ × ℝ ↦ z.1 / √(z.2 / ν)) = studentTMeasure ν := by
  let μ := (gaussianReal 0 1).prod (chiSquaredMeasure ν)
  let ratio : ℝ × ℝ → ℝ := fun z ↦ z.1 / √(z.2 / ν)
  let sq : ℝ → ℝ := fun x ↦ x ^ 2
  let reflect : ℝ × ℝ → ℝ × ℝ := Prod.map (fun x : ℝ ↦ -x) id
  let _ : IsProbabilityMeasure (chiSquaredMeasure ν) :=
    isProbabilityMeasure_chiSquaredMeasure hν.le
  let _ : IsProbabilityMeasure (studentTMeasure ν) :=
    isProbabilityMeasure_studentTMeasure hν
  let _ : IsProbabilityMeasure μ := by
    dsimp only [μ]
    infer_instance
  -- The chi-squared coordinate is positive almost everywhere, so squaring the ratio may cancel
  -- its square-root denominator.
  have hpos : ∀ᵐ z ∂μ, 0 < z.2 := by
    apply Measure.quasiMeasurePreserving_snd.ae
    rw [chiSquaredMeasure_eq_gammaMeasure hν]
    exact ae_pos_gammaMeasure (ν / 2) (1 / 2)
  have hratio_sq :
      (fun z ↦ (ratio z) ^ 2) =ᵐ[μ] fun z ↦ z.1 ^ 2 / 1 / (z.2 / ν) := by
    filter_upwards [hpos] with z hz
    have hzν : 0 ≤ z.2 / ν := (div_pos hz hν).le
    simp only [ratio, div_pow, Real.sq_sqrt hzν, div_one]
  have hμ_sq : μ.map (Prod.map sq id) =
      (chiSquaredMeasure 1).prod (chiSquaredMeasure ν) := by
    rw [← Measure.map_prod_map (gaussianReal 0 1) (chiSquaredMeasure ν) (by fun_prop)
      measurable_id, gaussianReal_map_sq, Measure.map_id]
  -- Reuse the Gaussian-square and chi-squared-ratio identities to identify the squared law.
  have hratio_sq_map :
      (μ.map ratio).map sq = fisherSnedecorMeasure 1 ν := by
    calc
      (μ.map ratio).map sq = μ.map (fun z ↦ (ratio z) ^ 2) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = μ.map (fun z ↦ z.1 ^ 2 / 1 / (z.2 / ν)) := Measure.map_congr hratio_sq
      _ = (μ.map (Prod.map sq id)).map (fun z ↦ z.1 / 1 / (z.2 / ν)) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = fisherSnedecorMeasure 1 ν := by
        rw [hμ_sq, map_scaled_div_chiSquaredMeasure one_pos hν]
  have hμ_reflect : μ.map reflect = μ := by
    rw [← Measure.map_prod_map (gaussianReal 0 1) (chiSquaredMeasure ν) (by fun_prop)
      measurable_id, gaussianReal_map_neg, Measure.map_id]
    simp only [neg_zero, μ]
  -- Reflecting the Gaussian coordinate reflects the ratio without changing its source law.
  have hratio_reflect : (μ.map ratio).map (fun x ↦ -x) = μ.map ratio := by
    calc
      (μ.map ratio).map (fun x ↦ -x) = μ.map ((fun x ↦ -x) ∘ ratio) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
      _ = μ.map (ratio ∘ reflect) := by
        apply Measure.map_congr
        exact ae_of_all _ fun z ↦ by
          exact neg_div' √(z.2 / ν) z.1
      _ = (μ.map reflect).map ratio := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
      _ = μ.map ratio := by rw [hμ_reflect]
  exact TauCeti.MeasureTheory.Measure.eq_of_map_sq_eq_of_map_neg_eq_self hratio_reflect
    (studentTMeasure_map_neg ν) (hratio_sq_map.trans (studentTMeasure_map_sq hν).symm)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Z V : Ω → ℝ}

/-- If `Z` is standard Gaussian and `V` is an independent chi-squared variable with `ν > 0`
degrees of freedom, then `Z / √(V / ν)` has the Student t law with `ν` degrees of freedom. -/
theorem hasLaw_studentT_of_gaussian_chiSquared (hν : 0 < ν) (hZV : IndepFun Z V P)
    (hZ : HasLaw Z (gaussianReal 0 1) P) (hV : HasLaw V (chiSquaredMeasure ν) P) :
    HasLaw (fun ω ↦ Z ω / √(V ω / ν)) (studentTMeasure ν) P := by
  let _ : IsProbabilityMeasure P := hZ.isProbabilityMeasure
  let _ : IsProbabilityMeasure (chiSquaredMeasure ν) :=
    isProbabilityMeasure_chiSquaredMeasure hν.le
  have hpair : HasLaw (fun ω ↦ (Z ω, V ω))
      ((gaussianReal 0 1).prod (chiSquaredMeasure ν)) P :=
    hZV.hasLaw_prod hZ hV
  have hratio : HasLaw (fun z : ℝ × ℝ ↦ z.1 / √(z.2 / ν)) (studentTMeasure ν)
      ((gaussianReal 0 1).prod (chiSquaredMeasure ν)) :=
    ⟨by fun_prop, map_div_sqrt_chiSquaredMeasure hν⟩
  exact hratio.fun_comp hpair

end Probability

end TauCeti

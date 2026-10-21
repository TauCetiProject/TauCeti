/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.CDF
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import TauCeti.MeasureTheory.Measure.AtomMixture

/-!
# Mixtures with one atom

This file develops the real distribution formulas for `MeasureTheory.Measure.atomMixture`, whose
generic measure and integration API is in `TauCeti.MeasureTheory.Measure.AtomMixture`. For a
probability measure, the results compute the cdf, mean, variance, moment-generating function, and
characteristic function. These formulas allow atomic and continuous parts to be handled without
pretending that the whole mixture has a density.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal unitInterval

namespace TauCeti.Probability

/-! ### Distribution and moment formulas -/

/-- The cdf of an atom mixture is the corresponding convex combination of the step cdf and the
cdf of the original law. -/
theorem cdf_atomMixture (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ)
    (w : unitInterval) (x : ℝ) :
    cdf (μ.atomMixture c w) x =
      (w : ℝ) * (if c ≤ x then 1 else 0) + (1 - (w : ℝ)) * cdf μ x := by
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def, Measure.atomMixture_apply _ _ _
    measurableSet_Iic]
  simp only [Set.indicator_apply, Set.mem_Iic, Pi.one_apply]
  rw [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (unitInterval.nonneg w),
    ENNReal.toReal_ofReal (sub_nonneg.mpr (unitInterval.le_one w))]
  · split_ifs <;> simp
  all_goals finiteness

end TauCeti.Probability

namespace TauCeti.Probability

/-- The mean of an atom mixture is the convex combination of the component means. -/
theorem integral_id_atomMixture (μ : Measure ℝ) (c : ℝ) (w : unitInterval)
    (hμ : Integrable id μ) :
    ∫ x, x ∂μ.atomMixture c w =
      (w : ℝ) * c + (1 - (w : ℝ)) * ∫ x, x ∂μ := by
  simpa only [id_eq, smul_eq_mul] using μ.integral_atomMixture c w id hμ

/-- The second raw moment of an atom mixture is the convex combination of the component second
moments. -/
theorem integral_sq_atomMixture (μ : Measure ℝ) (c : ℝ) (w : unitInterval)
    (hμ : Integrable (fun x => x ^ 2) μ) :
    ∫ x, x ^ 2 ∂μ.atomMixture c w =
      (w : ℝ) * c ^ 2 + (1 - (w : ℝ)) * ∫ x, x ^ 2 ∂μ := by
  simpa only [smul_eq_mul] using μ.integral_atomMixture c w (fun x => x ^ 2) hμ

/-- The variance of an atom mixture is the within-component variance plus the variance caused by
separating the atom from the component mean. -/
theorem variance_id_atomMixture (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ)
    (w : unitInterval) (hμ : MemLp id 2 μ) :
    variance id (μ.atomMixture c w) =
      (1 - (w : ℝ)) * variance id μ +
        (w : ℝ) * (1 - (w : ℝ)) * (c - ∫ x, x ∂μ) ^ 2 := by
  have hdirac : MemLp id 2 (Measure.dirac c) := memLp_dirac (by simp)
  have hmix : MemLp id 2 (μ.atomMixture c w) := by
    rw [Measure.atomMixture_def]
    exact (hdirac.smul_measure (by simp)).add_measure (hμ.smul_measure (by simp))
  rw [variance_eq_sub hmix, variance_eq_sub hμ]
  simp only [Pi.pow_apply, id_eq]
  rw [integral_id_atomMixture _ _ _
    (hμ.integrable one_le_two), integral_sq_atomMixture _ _ _ hμ.integrable_sq]
  ring

private theorem mgf_atomMixture_of_integrable (μ : Measure ℝ) (c : ℝ)
    (w : unitInterval) (t : ℝ)
    (hμ : Integrable (fun x => Real.exp (t * x)) μ) :
    mgf id (μ.atomMixture c w) t =
      (w : ℝ) * Real.exp (t * c) + (1 - (w : ℝ)) * mgf id μ t := by
  simpa [mgf] using μ.integral_atomMixture c w (fun x => Real.exp (t * x)) hμ

/-- Away from the pure-atom endpoint, an atom mixture has an exponential moment exactly when its
base component does. -/
theorem integrable_exp_mul_id_atomMixture_iff (μ : Measure ℝ) (c : ℝ)
    {w : unitInterval} (hw : w ≠ 1) (t : ℝ) :
    Integrable (fun x => Real.exp (t * x)) (μ.atomMixture c w) ↔
      Integrable (fun x => Real.exp (t * x)) μ := by
  have hwlt : (w : ℝ) < 1 := unitInterval.lt_one_iff_ne_one.mpr hw
  have hcoeff : ENNReal.ofReal (1 - (w : ℝ)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hwlt)
  rw [Measure.atomMixture_def, integrable_add_measure,
    integrable_smul_measure hcoeff ENNReal.ofReal_ne_top]
  exact and_iff_right ((integrable_dirac (by simp)).smul_measure (by simp))

/-- The exact exponential-integrability domain of an atom mixture.  A pure atom has every
exponential moment; otherwise the domain is that of the base component. -/
theorem integrableExpSet_id_atomMixture (μ : Measure ℝ) (c : ℝ) (w : unitInterval) :
    integrableExpSet id (μ.atomMixture c w) =
      if w = 1 then Set.univ else integrableExpSet id μ := by
  by_cases hw : w = 1
  · subst w
    ext t
    simp only [Measure.atomMixture_one, integrableExpSet, Set.mem_ofPred_eq]
    exact iff_true_intro (integrable_dirac (by finiteness))
  · simp only [hw, ↓reduceIte]
    ext t
    exact integrable_exp_mul_id_atomMixture_iff μ c hw t

/-- The moment-generating function of an atom mixture is the convex combination of the component
moment-generating functions throughout the mixture's exact exponential-integrability domain. -/
theorem mgf_id_atomMixture (μ : Measure ℝ) (c : ℝ) (w : unitInterval) (t : ℝ)
    (ht : t ∈ integrableExpSet id (μ.atomMixture c w)) :
    mgf id (μ.atomMixture c w) t =
      (w : ℝ) * Real.exp (t * c) + (1 - (w : ℝ)) * mgf id μ t := by
  by_cases hw : w = 1
  · subst w
    simp [mgf, Measure.atomMixture_def]
  · exact mgf_atomMixture_of_integrable μ c w t
      ((integrable_exp_mul_id_atomMixture_iff μ c hw t).mp ht)

/-- The cumulant-generating function of an atom mixture is the logarithm of the weighted sum of
component mgfs, rather than a mixture of their cumulant-generating functions. -/
theorem cgf_id_atomMixture (μ : Measure ℝ) (c : ℝ) (w : unitInterval) (t : ℝ)
    (ht : t ∈ integrableExpSet id (μ.atomMixture c w)) :
    cgf id (μ.atomMixture c w) t =
      Real.log ((w : ℝ) * Real.exp (t * c) + (1 - (w : ℝ)) * mgf id μ t) := by
  rw [cgf, mgf_id_atomMixture μ c w t ht]

/-- The characteristic function of an atom mixture is the convex combination of the component
characteristic functions. -/
theorem charFun_atomMixture (μ : Measure ℝ) [IsFiniteMeasure μ] (c : ℝ)
    (w : unitInterval) (t : ℝ) :
    charFun (μ.atomMixture c w) t =
      (w : ℝ) * Complex.exp (t * c * Complex.I) +
        (1 - (w : ℝ)) * charFun μ t := by
  have hμ : Integrable (fun x : ℝ => Complex.exp (t * x * Complex.I)) μ := by
    refine (integrable_const (1 : ℝ)).mono (by fun_prop) ?_
    filter_upwards with x
    convert le_rfl
    simp [← Complex.ofReal_mul]
  simpa [charFun_apply_real] using
    μ.integral_atomMixture c w (fun x : ℝ => Complex.exp (t * x * Complex.I)) hμ

end TauCeti.Probability

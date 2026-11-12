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
public import TauCeti.Probability.Distributions.Dirac

/-!
# Mixtures with one atom

This file develops the real distribution formulas for `MeasureTheory.Measure.atomMixture`, whose
generic measure and integration API is in `TauCeti.MeasureTheory.Measure.AtomMixture`. For a
probability measure, the results compute the cdf, mean, variance, moment-generating function, and
characteristic function. They also compute the quantile: above the mixture's cdf at the atom it is
the base quantile at the level obtained by removing and rescaling the added weight, and when the
base law has no mass below the atom, it stays at the atom through the combined mass there. These
formulas allow atomic and continuous parts to be handled without pretending that the whole
mixture has a density.

The formulas live in `MeasureTheory.Measure` and support dot notation on the base measure,
for example `μ.cdf_atomMixture` and `μ.mgf_id_atomMixture`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal unitInterval

namespace MeasureTheory.Measure

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

/-- The cdf at the added atom is the combined mass of the new atom and the base law's atom there,
provided the base law has no mass below that point. -/
theorem cdf_atomMixture_atom (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ)
    (hμ : μ (Iio c) = 0) (w : unitInterval) :
    cdf (μ.atomMixture c w) c =
      (w : ℝ) + (1 - (w : ℝ)) * μ.real {c} := by
  have hμreal : μ.real (Iio c) = 0 := by simp [Measure.real, hμ]
  rw [cdf_atomMixture, ite_eq_left le_rfl, mul_one, cdf_eq_real, ← Iio_union_right,
    measureReal_union (s₁ := Iio c) (s₂ := {c}) (by simp)
      (measurableSet_singleton c),
    hμreal, zero_add]

/-- If the base law has no mass below the added atom, the cdf of the atom mixture vanishes strictly
below the atom. -/
theorem cdf_atomMixture_of_lt (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ)
    (hμ : μ (Iio c) = 0) (w : unitInterval) {x : ℝ} (hx : x < c) :
    cdf (μ.atomMixture c w) x = 0 := by
  rw [cdf_atomMixture, ite_eq_right hx.not_ge, cdf_eq_zero_of_lt_of_measure_Iio_eq_zero μ hμ hx]
  simp

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
  rw [μ.integral_id_atomMixture _ _ (hμ.integrable one_le_two),
    μ.integral_sq_atomMixture _ _ hμ.integrable_sq]
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
    exact μ.integrable_exp_mul_id_atomMixture_iff c hw t

/-- The moment-generating function of an atom mixture is the convex combination of the component
moment-generating functions throughout the mixture's exact exponential-integrability domain. -/
theorem mgf_id_atomMixture (μ : Measure ℝ) (c : ℝ) (w : unitInterval) (t : ℝ)
    (ht : t ∈ integrableExpSet id (μ.atomMixture c w)) :
    mgf id (μ.atomMixture c w) t =
      (w : ℝ) * Real.exp (t * c) + (1 - (w : ℝ)) * mgf id μ t := by
  by_cases hw : w = 1
  · subst w
    simp [mgf, Measure.atomMixture_def]
  · exact μ.mgf_atomMixture_of_integrable c w t
      ((μ.integrable_exp_mul_id_atomMixture_iff c hw t).mp ht)

/-- The cumulant-generating function of an atom mixture is the logarithm of the weighted sum of
component mgfs, rather than a mixture of their cumulant-generating functions. -/
theorem cgf_id_atomMixture (μ : Measure ℝ) (c : ℝ) (w : unitInterval) (t : ℝ)
    (ht : t ∈ integrableExpSet id (μ.atomMixture c w)) :
    cgf id (μ.atomMixture c w) t =
      Real.log ((w : ℝ) * Real.exp (t * c) + (1 - (w : ℝ)) * mgf id μ t) := by
  rw [cgf, μ.mgf_id_atomMixture c w t ht]

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

/-! ### Quantiles at a lower support boundary -/

section Quantile

open TauCeti.Probability

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {c : ℝ} {w : unitInterval} {u : ℝ}

/-- Up to the combined atom at a lower support boundary, the quantile of an atom mixture is that
boundary point. -/
theorem quantile_atomMixture_eq_atom (hμ : μ (Iio c) = 0)
    (hu : 0 < u)
    (hle : u ≤ (w : ℝ) + (1 - (w : ℝ)) * μ.real {c}) :
    (μ.atomMixture c w).quantile u = c := by
  have hu_one : u ≤ 1 := hle.trans (cdf_atomMixture_atom μ c hμ w ▸ cdf_le_one _ c)
  calc
    (μ.atomMixture c w).quantile u = (dirac c).quantile u :=
      quantile_eq_of_le_cdf_iff _ _ fun x => by
        by_cases hx : c ≤ x
        · rw [TauCeti.Probability.cdf_dirac, ite_eq_left hx]
          constructor
          · exact fun _ => hu_one
          · exact fun _ => hle.trans <| by
              rw [← cdf_atomMixture_atom μ c hμ w]
              exact monotone_cdf _ hx
        · rw [TauCeti.Probability.cdf_dirac, ite_eq_right hx,
            cdf_atomMixture_of_lt μ c hμ w (lt_of_not_ge hx)]
    _ = c := quantile_dirac c hu hu_one

/-- Above the mixture's cdf at the added atom, remove the added weight and rescale the probability
level to obtain the quantile of the base law. -/
theorem quantile_atomMixture_of_lt (hu : u ≤ 1)
    (hlt : (w : ℝ) + (1 - (w : ℝ)) * cdf μ c < u) :
    (μ.atomMixture c w).quantile u =
      μ.quantile ((u - (w : ℝ)) / (1 - (w : ℝ))) := by
  have hw : w ≠ 1 := by
    intro hw
    subst w
    norm_num at hlt
    exact (not_lt_of_ge hu) hlt
  have hden : 0 < 1 - (w : ℝ) := sub_pos.mpr (unitInterval.lt_one_iff_ne_one.mpr hw)
  apply quantile_eq_of_le_cdf_iff
  intro x
  rw [μ.cdf_atomMixture, div_le_iff₀ hden]
  by_cases hx : c ≤ x
  · rw [ite_eq_left hx, mul_one]
    constructor <;> intro h <;> nlinarith
  · have hFx : cdf μ x ≤ cdf μ c := monotone_cdf μ (lt_of_not_ge hx).le
    rw [ite_eq_right hx, mul_zero, zero_add]
    have := unitInterval.nonneg w
    constructor <;> intro h <;> nlinarith

/-- The quantile of an atom mixture at a lower support boundary: it is the boundary point through
the combined atom there and otherwise is the rescaled quantile of the base law. This includes the
pure-atom endpoint `w = 1`. -/
theorem quantile_atomMixture (hμ : μ (Iio c) = 0) (w : unitInterval)
    (hu : u ∈ Ioc 0 1) :
    (μ.atomMixture c w).quantile u =
      if u ≤ (w : ℝ) + (1 - (w : ℝ)) * μ.real {c} then c
      else μ.quantile ((u - (w : ℝ)) / (1 - (w : ℝ))) := by
  split_ifs with h
  · exact quantile_atomMixture_eq_atom hμ hu.1 h
  · have hcdf : cdf μ c = μ.real {c} := by simpa using cdf_atomMixture_atom μ c hμ 0
    exact quantile_atomMixture_of_lt hu.2 (hcdf ▸ lt_of_not_ge h)

end Quantile

end MeasureTheory.Measure

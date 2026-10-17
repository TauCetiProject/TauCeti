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
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# Mixtures with one atom

This file defines `MeasureTheory.Measure.atomMixture μ c w`, the convex mixture of a measure
`μ` with a point mass at `c`.  The weight `w` belongs to the unit interval and is the mass assigned
to the distinguished atom.

The main results give the characteristic measure identities: evaluation on measurable sets,
singleton masses, measurability in all three parameters, and the decomposition of a mixture with
an absolutely continuous component.  For a probability measure, they also compute the cdf, mean,
variance, moment-generating function, and characteristic function.  These formulas allow atomic
and continuous parts to be handled without pretending that the whole mixture has a density.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal unitInterval

namespace MeasureTheory.Measure

/-- The mixture assigning weight `w` to the atom at `c` and weight `1 - w` to `μ`. -/
def atomMixture {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (c : α) (w : unitInterval) : Measure α :=
  ENNReal.ofReal (w : ℝ) • Measure.dirac c +
    ENNReal.ofReal (1 - (w : ℝ)) • μ

/-- Evaluation of an atom mixture on a measurable set. -/
theorem atomMixture_apply {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (c : α) (w : unitInterval) {s : Set α}
    (hs : MeasurableSet s) :
    atomMixture μ c w s =
      ENNReal.ofReal (w : ℝ) * s.indicator 1 c +
        ENNReal.ofReal (1 - (w : ℝ)) * μ s := by
  simp [atomMixture, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hs]

/-- The mass of an atom mixture at a singleton. -/
theorem atomMixture_singleton {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) (c : α) (w : unitInterval) :
    atomMixture μ c w {c} =
      ENNReal.ofReal (w : ℝ) + ENNReal.ofReal (1 - (w : ℝ)) * μ {c} := by
  rw [atomMixture_apply _ _ _ (measurableSet_singleton c)]
  simp

/-- Away from the distinguished atom, an atom mixture rescales the original singleton mass. -/
theorem atomMixture_singleton_of_ne {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) {c x : α} (hcx : c ≠ x)
    (w : unitInterval) :
    atomMixture μ c w {x} = ENNReal.ofReal (1 - (w : ℝ)) * μ {x} := by
  rw [atomMixture_apply _ _ _ (measurableSet_singleton x)]
  simp [hcx]

/-- Weight zero leaves the original measure unchanged. -/
@[simp]
theorem atomMixture_zero {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (c : α) : atomMixture μ c 0 = μ := by
  simp [atomMixture]

/-- Weight one gives the distinguished point mass. -/
@[simp]
theorem atomMixture_one {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (c : α) : atomMixture μ c 1 = Measure.dirac c := by
  simp [atomMixture]

/-- An atom mixture of a probability measure is a probability measure. -/
instance isProbabilityMeasure_atomMixture {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (c : α) (w : unitInterval) :
    IsProbabilityMeasure (atomMixture μ c w) := by
  constructor
  rw [atomMixture]
  simp only [Measure.coe_add, Pi.add_apply, Measure.smul_apply, Measure.dirac_apply' _
    MeasurableSet.univ, measure_univ, smul_eq_mul, mul_one]
  rw [Set.indicator_of_mem (Set.mem_univ c)]
  simp only [Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_add (unitInterval.nonneg w) (sub_nonneg.mpr (unitInterval.le_one w))]
  simp

/-- Atom mixtures vary measurably with a measurable family of measures, atoms, and weights. -/
@[fun_prop]
theorem measurable_atomMixture {β α : Type*} [MeasurableSpace β] [MeasurableSpace α]
    {μ : β → Measure α} {c : β → α} {w : β → unitInterval} (hμ : Measurable μ)
    (hc : Measurable c) (hw : Measurable w) :
    Measurable fun b => atomMixture (μ b) (c b) (w b) := by
  refine Measure.measurable_measure.2 fun s hs => ?_
  simp_rw [atomMixture_apply _ _ _ hs]
  exact ((ENNReal.measurable_ofReal.comp (measurable_subtype_coe.comp hw)).mul
      (measurable_one.indicator hs |>.comp hc)).add
    ((ENNReal.measurable_ofReal.comp
      (measurable_const.sub (measurable_subtype_coe.comp hw))).mul
      ((Measure.measurable_coe hs).comp hμ))

/-- If the non-atomic component has density `f`, the same component in the mixture has density
`(1 - w) f`.  The atom remains separate. -/
theorem atomMixture_withDensity {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ≥0∞) (c : α) (w : unitInterval) :
    atomMixture (μ.withDensity f) c w =
      ENNReal.ofReal (w : ℝ) • Measure.dirac c +
        μ.withDensity (fun x => ENNReal.ofReal (1 - (w : ℝ)) * f x) := by
  rw [atomMixture, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  rfl

end MeasureTheory.Measure

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

/-- Integrability is preserved when a point mass is mixed into a measure. -/
theorem Integrable.atomMixture {α E : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [NormedAddCommGroup E] {f : α → E} {μ : Measure α} (hf : Integrable f μ)
    (c : α) (w : unitInterval) : Integrable f (μ.atomMixture c w) := by
  rw [Measure.atomMixture]
  exact (integrable_dirac (by simp)).smul_measure (by simp) |>.add_measure
    (hf.smul_measure (by simp))

/-- The mean of an atom mixture is the convex combination of the component means. -/
theorem integral_id_atomMixture (μ : Measure ℝ) (c : ℝ) (w : unitInterval)
    (hμ : Integrable id μ) :
    ∫ x, x ∂μ.atomMixture c w =
      (w : ℝ) * c + (1 - (w : ℝ)) * ∫ x, x ∂μ := by
  rw [Measure.atomMixture, integral_add_measure]
  · simp [ENNReal.toReal_ofReal (unitInterval.nonneg w),
      ENNReal.toReal_ofReal (sub_nonneg.mpr (unitInterval.le_one w))]
  · exact (integrable_dirac (by simp)).smul_measure (by simp)
  · exact hμ.smul_measure (by simp)

/-- The second raw moment of an atom mixture is the convex combination of the component second
moments. -/
theorem integral_sq_atomMixture (μ : Measure ℝ) (c : ℝ) (w : unitInterval)
    (hμ : Integrable (fun x => x ^ 2) μ) :
    ∫ x, x ^ 2 ∂μ.atomMixture c w =
      (w : ℝ) * c ^ 2 + (1 - (w : ℝ)) * ∫ x, x ^ 2 ∂μ := by
  rw [Measure.atomMixture, integral_add_measure]
  · simp [ENNReal.toReal_ofReal (unitInterval.nonneg w),
      ENNReal.toReal_ofReal (sub_nonneg.mpr (unitInterval.le_one w))]
  · exact (integrable_dirac (by simp)).smul_measure (by simp)
  · exact hμ.smul_measure (by simp)

/-- The variance of an atom mixture is the within-component variance plus the variance caused by
separating the atom from the component mean. -/
theorem variance_id_atomMixture (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ)
    (w : unitInterval) (hμ : MemLp id 2 μ) :
    variance id (μ.atomMixture c w) =
      (1 - (w : ℝ)) * variance id μ +
        (w : ℝ) * (1 - (w : ℝ)) * (c - ∫ x, x ∂μ) ^ 2 := by
  have hdirac : MemLp id 2 (Measure.dirac c) := memLp_dirac (by simp)
  have hmix : MemLp id 2 (μ.atomMixture c w) := by
    rw [Measure.atomMixture]
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
  rw [Measure.atomMixture, mgf_add_measure]
  · simp [mgf, ENNReal.toReal_ofReal (unitInterval.nonneg w),
      ENNReal.toReal_ofReal (sub_nonneg.mpr (unitInterval.le_one w))]
  · exact (integrable_dirac (by simp)).smul_measure (by simp)
  · exact hμ.smul_measure (by simp)

/-- Away from the pure-atom endpoint, an atom mixture has an exponential moment exactly when its
non-atomic component does. -/
theorem integrable_exp_mul_id_atomMixture_iff (μ : Measure ℝ) (c : ℝ)
    {w : unitInterval} (hw : w ≠ 1) (t : ℝ) :
    Integrable (fun x => Real.exp (t * x)) (μ.atomMixture c w) ↔
      Integrable (fun x => Real.exp (t * x)) μ := by
  have hwlt : (w : ℝ) < 1 := unitInterval.lt_one_iff_ne_one.mpr hw
  have hcoeff : ENNReal.ofReal (1 - (w : ℝ)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hwlt)
  rw [Measure.atomMixture, integrable_add_measure,
    integrable_smul_measure hcoeff ENNReal.ofReal_ne_top]
  exact and_iff_right ((integrable_dirac (by simp)).smul_measure (by simp))

/-- The exact exponential-integrability domain of an atom mixture.  A pure atom has every
exponential moment; otherwise the domain is that of the non-atomic component. -/
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
    simp [mgf, Measure.atomMixture]
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
  rw [charFun_apply_real, Measure.atomMixture, integral_add_measure]
  · simp [charFun_apply_real, ENNReal.toReal_ofReal (unitInterval.nonneg w),
      ENNReal.toReal_ofReal (sub_nonneg.mpr (unitInterval.le_one w))]
  · exact (integrable_dirac (by simp)).smul_measure (by simp)
  · have hμ : Integrable (fun x : ℝ => Complex.exp (t * x * Complex.I)) μ := by
      refine (integrable_const (1 : ℝ)).mono (by fun_prop) ?_
      filter_upwards with x
      convert le_rfl
      simp [← Complex.ofReal_mul]
    exact hμ.smul_measure (by simp)

end TauCeti.Probability

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Probability.Kernel.WithDensity

/-!
# Measures weighted by a nonnegative function

This file defines the probability law obtained by weighting a measure by a nonnegative function
and dividing by the total weight. The construction is totalized to the zero measure when the
normalizing integral is zero or infinite.

The main results compute its density, integrals, and iterated weightings. They also show that a
jointly measurable family of weights applied to a kernel gives a measurable family of measures.
-/

public section

open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- The measure obtained by weighting `μ` by `w` and normalizing its total mass.

If the total weight is zero or infinite, this is the zero measure. -/
noncomputable def weighted (μ : Measure α) (w : α → ℝ≥0) : Measure α :=
  (∫⁻ x, (w x : ℝ≥0∞) ∂μ)⁻¹ • μ.withDensity fun x => w x

/-- The definition of a normalized weighted measure. -/
theorem weighted_def (μ : Measure α) (w : α → ℝ≥0) :
    μ.weighted w = (∫⁻ x, (w x : ℝ≥0∞) ∂μ)⁻¹ • μ.withDensity fun x => w x :=
  (rfl)

/-- Weighting is unchanged by replacing a weight almost everywhere. -/
theorem weighted_congr {μ : Measure α} {w v : α → ℝ≥0} (h : w =ᵐ[μ] v) :
    μ.weighted w = μ.weighted v := by
  have hcoe : (fun x => (w x : ℝ≥0∞)) =ᵐ[μ] fun x => (v x : ℝ≥0∞) :=
    h.mono fun x hx => congrArg ((↑) : ℝ≥0 → ℝ≥0∞) hx
  rw [weighted_def, weighted_def, lintegral_congr_ae hcoe, withDensity_congr_ae hcoe]

/-- A weighted measure can equivalently put the normalizing constant inside its density. -/
theorem weighted_eq_withDensity (μ : Measure α) {w : α → ℝ≥0} (hw : AEMeasurable w μ) :
    μ.weighted w = μ.withDensity fun x =>
      (∫⁻ y, (w y : ℝ≥0∞) ∂μ)⁻¹ * w x := by
  let w' := hw.mk w
  have hww' : w =ᵐ[μ] w' := hw.ae_eq_mk
  have hcoe : (fun x => (w x : ℝ≥0∞)) =ᵐ[μ] fun x => (w' x : ℝ≥0∞) :=
    hww'.mono fun x hx => congrArg ((↑) : ℝ≥0 → ℝ≥0∞) hx
  calc
    μ.weighted w = μ.weighted w' := weighted_congr hww'
    _ = μ.withDensity (fun x => (∫⁻ y, (w' y : ℝ≥0∞) ∂μ)⁻¹ * w' x) := by
      rw [weighted_def, ← withDensity_smul _ hw.measurable_mk.coe_nnreal_ennreal]
      rfl
    _ = μ.withDensity (fun x => (∫⁻ y, (w y : ℝ≥0∞) ∂μ)⁻¹ * w x) := by
      apply withDensity_congr_ae
      have hlintegral : (∫⁻ y, (w y : ℝ≥0∞) ∂μ) = ∫⁻ y, (w' y : ℝ≥0∞) ∂μ :=
        lintegral_congr_ae hcoe
      filter_upwards [hww'] with x hx
      rw [hlintegral, hx]

/-- The mass assigned by a weighted measure to a measurable set. -/
theorem weighted_apply (μ : Measure α) (w : α → ℝ≥0) {s : Set α} (hs : MeasurableSet s) :
    μ.weighted w s = (∫⁻ x, (w x : ℝ≥0∞) ∂μ)⁻¹ * ∫⁻ x in s, (w x : ℝ≥0∞) ∂μ := by
  rw [weighted_def, Measure.smul_apply, smul_eq_mul, withDensity_apply _ hs]

/-- A zero total weight gives the zero measure. -/
@[simp]
theorem weighted_eq_zero_of_lintegral_eq_zero {μ : Measure α} {w : α → ℝ≥0}
    (h : ∫⁻ x, (w x : ℝ≥0∞) ∂μ = 0) : μ.weighted w = 0 := by
  have hdensity : μ.withDensity (fun x => (w x : ℝ≥0∞)) = 0 := by
    rw [← measure_univ_eq_zero, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ, h]
  rw [weighted_def, h, hdensity]
  exact smul_zero _

/-- An infinite total weight gives the zero measure. -/
@[simp]
theorem weighted_eq_zero_of_lintegral_eq_top {μ : Measure α} {w : α → ℝ≥0}
    (h : ∫⁻ x, (w x : ℝ≥0∞) ∂μ = ∞) : μ.weighted w = 0 := by
  rw [weighted_def, h]
  simp

/-- Weighting by the zero function gives the zero measure. -/
theorem weighted_zero (μ : Measure α) : μ.weighted 0 = 0 := by
  apply weighted_eq_zero_of_lintegral_eq_zero
  simp

/-- Weighting a probability measure by the constant-one function leaves it unchanged. -/
@[simp]
theorem weighted_one (μ : Measure α) [IsProbabilityMeasure μ] : μ.weighted 1 = μ := by
  rw [weighted_def]
  simp

/-- A positive finite total weight makes the weighted measure a probability measure. -/
theorem isProbabilityMeasure_weighted {μ : Measure α} {w : α → ℝ≥0}
    (hpos : 0 < ∫⁻ x, (w x : ℝ≥0∞) ∂μ)
    (hfin : ∫⁻ x, (w x : ℝ≥0∞) ∂μ ≠ ∞) : IsProbabilityMeasure (μ.weighted w) := by
  constructor
  rw [weighted_apply μ w MeasurableSet.univ, Measure.restrict_univ,
    ENNReal.inv_mul_cancel hpos.ne' hfin]

/-- A weighting is always either zero or a probability measure. -/
theorem isZeroOrProbabilityMeasure_weighted {μ : Measure α} {w : α → ℝ≥0} :
    IsZeroOrProbabilityMeasure (μ.weighted w) := by
  rcases eq_or_ne (∫⁻ x, (w x : ℝ≥0∞) ∂μ) 0 with hzero | hzero
  · rw [weighted_eq_zero_of_lintegral_eq_zero hzero]
    infer_instance
  rcases eq_or_ne (∫⁻ x, (w x : ℝ≥0∞) ∂μ) ∞ with htop | htop
  · rw [weighted_eq_zero_of_lintegral_eq_top htop]
    infer_instance
  have hpos : 0 < ∫⁻ x, (w x : ℝ≥0∞) ∂μ := (pos_iff_ne_zero.mpr hzero)
  have := isProbabilityMeasure_weighted hpos htop
  infer_instance

/-- A weighted measure is absolutely continuous with respect to its base measure. -/
theorem weighted_absolutelyContinuous {μ : Measure α} {w : α → ℝ≥0} : μ.weighted w ≪ μ := by
  rw [weighted_def]
  exact (withDensity_absolutelyContinuous _ _).smul_left _

/-- The Radon--Nikodym derivative of a weighted measure is its normalized weight. -/
theorem rnDeriv_weighted (μ : Measure α) [SigmaFinite μ] {w : α → ℝ≥0}
    (hw : AEMeasurable w μ) :
    (μ.weighted w).rnDeriv μ =ᵐ[μ] fun x =>
      (∫⁻ y, (w y : ℝ≥0∞) ∂μ)⁻¹ * w x := by
  rw [weighted_eq_withDensity μ hw]
  exact rnDeriv_withDensity₀ μ
    (measurable_const.aemeasurable.mul hw.coe_nnreal_ennreal)

/-- Integrability under a valid weighted law is weighted integrability under its base measure. -/
theorem integrable_weighted_iff {μ : Measure α} {w : α → ℝ≥0} (hw : AEMeasurable w μ)
    (hpos : 0 < ∫⁻ x, (w x : ℝ≥0∞) ∂μ)
    (hfin : ∫⁻ x, (w x : ℝ≥0∞) ∂μ ≠ ∞)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : α → E} :
    Integrable g (μ.weighted w) ↔ Integrable (fun x => w x • g x) μ := by
  rw [weighted_def, integrable_inv_smul_measure hpos.ne' hfin,
    integrable_withDensity_iff_integrable_smul₀ hw]

/-- Integration against a weighted law is weighted integration divided by the total weight.

This formula also covers a zero or infinite normalizing constant, when `μ.weighted w`
is the zero measure. -/
theorem integral_weighted {μ : Measure α} {w : α → ℝ≥0} (hw : AEMeasurable w μ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : α → E) :
    ∫ x, g x ∂μ.weighted w =
      (∫⁻ x, (w x : ℝ≥0∞) ∂μ).toReal⁻¹ • ∫ x, w x • g x ∂μ := by
  rw [weighted_def, integral_smul_measure, integral_withDensity_eq_integral_smul₀ hw,
    ENNReal.toReal_inv]

/-- The nonnegative integral against a weighted law is the base integral of the product divided by
the total weight. This also covers a zero or infinite total weight. -/
theorem lintegral_weighted {μ : Measure α} {w : α → ℝ≥0} (hw : AEMeasurable w μ)
    (g : α → ℝ≥0∞) :
    ∫⁻ x, g x ∂μ.weighted w =
      (∫⁻ x, (w x : ℝ≥0∞) ∂μ)⁻¹ * ∫⁻ x, (w x : ℝ≥0∞) * g x ∂μ := by
  rw [weighted_def, lintegral_smul_measure, smul_eq_mul,
    lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hw.coe_nnreal_ennreal (by simp)]
  rfl

/-- If reweighting `μ` by `w` gives a positive finite multiple of a probability measure `ν`, then
`ν` is the weighted law of `μ`. -/
theorem weighted_eq_of_withDensity_eq_smul {μ ν : Measure α} [IsProbabilityMeasure ν]
    {w : α → ℝ≥0} {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞)
    (h : (μ.withDensity fun x => (w x : ℝ≥0∞)) = c • ν) : μ.weighted w = ν := by
  have hZ : ∫⁻ x, (w x : ℝ≥0∞) ∂μ = c := by
    rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, h, smul_apply,
      measure_univ, smul_eq_mul, mul_one]
  rw [weighted_def, hZ, h, smul_smul, ENNReal.inv_mul_cancel hc0 hc, one_smul]

/-- Multiplying a weight by a positive constant does not change the weighted law. -/
theorem weighted_const_smul {μ : Measure α} {w : α → ℝ≥0} {c : ℝ≥0} (hc : c ≠ 0) :
    μ.weighted (c • w) = μ.weighted w := by
  have hfun : (fun x => ((c * w x : ℝ≥0) : ℝ≥0∞)) =
      fun x => (c : ℝ≥0∞) * (w x : ℝ≥0∞) := by
    funext x
    simp
  have hsmul : (fun x => (c : ℝ≥0∞) * (w x : ℝ≥0∞)) =
      (c : ℝ≥0∞) • fun x => (w x : ℝ≥0∞) := by
    rfl
  rw [weighted_def, weighted_def]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hfun, lintegral_const_mul' _ _ (by simp), hsmul,
    withDensity_smul' (c : ℝ≥0∞) _ (by simp)]
  rw [smul_smul]
  congr 1
  rw [ENNReal.mul_inv (Or.inl (by exact_mod_cast hc)) (Or.inl (by simp))]
  calc
    (c : ℝ≥0∞)⁻¹ * (∫⁻ x, (w x : ℝ≥0∞) ∂μ)⁻¹ * c =
        (c : ℝ≥0∞)⁻¹ * c * (∫⁻ x, (w x : ℝ≥0∞) ∂μ)⁻¹ := by ac_rfl
    _ = (∫⁻ x, (w x : ℝ≥0∞) ∂μ)⁻¹ := by
      rw [ENNReal.inv_mul_cancel (by exact_mod_cast hc) (by simp), one_mul]

/-- Successive weightings multiply their weights when the first weighting is a probability law. -/
theorem weighted_weighted {μ : Measure α} {w v : α → ℝ≥0} (hw : AEMeasurable w μ)
    (hwpos : 0 < ∫⁻ x, (w x : ℝ≥0∞) ∂μ)
    (hwfin : ∫⁻ x, (w x : ℝ≥0∞) ∂μ ≠ ∞) :
    (μ.weighted w).weighted v = μ.weighted fun x => w x * v x := by
  rw [weighted_def, weighted_def, weighted_def,
    lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _
      hw.coe_nnreal_ennreal (by simp)]
  rw [withDensity_smul_measure]
  have hdensity :
      (μ.withDensity fun x => (w x : ℝ≥0∞)).withDensity (fun x => (v x : ℝ≥0∞)) =
        μ.withDensity fun x => ((w x * v x : ℝ≥0) : ℝ≥0∞) := by
    ext s hs
    rw [withDensity_apply _ hs, withDensity_apply _ hs,
      setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _
        hw.coe_nnreal_ennreal.restrict _ hs (by simp)]
    rfl
  rw [hdensity]
  have hfun : ((fun x => (w x : ℝ≥0∞)) * fun x => (v x : ℝ≥0∞)) =
      fun x => ((w x * v x : ℝ≥0) : ℝ≥0∞) := by
    funext x
    simp [Pi.mul_apply]
  rw [hfun]
  rw [smul_smul]
  let Z := ∫⁻ x, (w x : ℝ≥0∞) ∂μ
  let W := ∫⁻ x, ((w x * v x : ℝ≥0) : ℝ≥0∞) ∂μ
  -- The nested scalar actions use different scalar-tower paths, so expose their product
  -- before cancelling the first normalizing constant.
  change ((Z⁻¹ * W)⁻¹ * Z⁻¹) • μ.withDensity (fun x => ((w x * v x : ℝ≥0) : ℝ≥0∞)) =
    W⁻¹ • μ.withDensity fun x => ((w x * v x : ℝ≥0) : ℝ≥0∞)
  congr 1
  rw [ENNReal.mul_inv (Or.inl (by simpa using hwfin))
    (Or.inl (by simpa using hwpos.ne')), inv_inv]
  calc
    Z * W⁻¹ * Z⁻¹ = Z * Z⁻¹ * W⁻¹ := by ac_rfl
    _ = W⁻¹ := by rw [ENNReal.mul_inv_cancel hwpos.ne' hwfin, one_mul]

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- A jointly measurable family of weights applied to an s-finite kernel gives a measurable
family of weighted measures. -/
theorem measurable_weighted (κ : Kernel β α) [IsSFiniteKernel κ] {w : β → α → ℝ≥0}
    (hw : Measurable (Function.uncurry w)) :
    Measurable fun b => (κ b).weighted (w b) := by
  have hZ : Measurable fun b => ∫⁻ x, (w b x : ℝ≥0∞) ∂κ b :=
    hw.coe_nnreal_ennreal.lintegral_kernel_prod_right'
  have hρ : Measurable (Function.uncurry fun b x =>
      (∫⁻ y, (w b y : ℝ≥0∞) ∂κ b)⁻¹ * (w b x : ℝ≥0∞)) :=
    (hZ.comp measurable_fst).inv.mul hw.coe_nnreal_ennreal
  have h : (fun b => (κ b).weighted (w b)) = Kernel.withDensity κ fun b x =>
      (∫⁻ y, (w b y : ℝ≥0∞) ∂κ b)⁻¹ * (w b x : ℝ≥0∞) := by
    funext b
    rw [Kernel.withDensity_apply _ hρ, Measure.weighted_eq_withDensity]
    exact (hw.comp measurable_prodMk_left).aemeasurable
  rw [h]
  exact (Kernel.withDensity κ _).measurable

end ProbabilityTheory.Kernel

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The weighted measures of a fixed s-finite measure vary measurably with a jointly measurable
family of weights. -/
theorem measurable_weighted_const (μ : Measure α) [SFinite μ] {w : β → α → ℝ≥0}
    (hw : Measurable (Function.uncurry w)) : Measurable fun b => μ.weighted (w b) :=
  Kernel.measurable_weighted (Kernel.const β μ) hw

end MeasureTheory.Measure

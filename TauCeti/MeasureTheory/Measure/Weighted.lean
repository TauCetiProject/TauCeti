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
  have hcoe : (fun x => (w x : ℝ≥0∞)) =ᵐ[μ] fun x => (v x : ℝ≥0∞) := h.fun_comp _
  rw [weighted_def, weighted_def, lintegral_congr_ae hcoe, withDensity_congr_ae hcoe]

/-- The mass assigned by a weighted measure to a measurable set. -/
theorem weighted_apply (μ : Measure α) (w : α → ℝ≥0) {s : Set α} (hs : MeasurableSet s) :
    μ.weighted w s = (∫⁻ x, (w x : ℝ≥0∞) ∂μ)⁻¹ * ∫⁻ x in s, (w x : ℝ≥0∞) ∂μ := by
  rw [weighted_def, _root_.smul_apply, smul_eq_mul, withDensity_apply _ hs]

/-- A weighted measure can equivalently put the normalizing constant inside its density. -/
theorem weighted_eq_withDensity (μ : Measure α) {w : α → ℝ≥0} (hw : AEMeasurable w μ) :
    μ.weighted w = μ.withDensity fun x =>
      (∫⁻ y, (w y : ℝ≥0∞) ∂μ)⁻¹ * w x := by
  ext s hs
  rw [weighted_apply μ w hs, withDensity_apply _ hs,
    lintegral_const_mul'' _ hw.coe_nnreal_ennreal.restrict]

/-- A zero total weight gives the zero measure. -/
@[simp]
theorem weighted_eq_zero_of_lintegral_eq_zero {μ : Measure α} {w : α → ℝ≥0}
    (h : ∫⁻ x, (w x : ℝ≥0∞) ∂μ = 0) : μ.weighted w = 0 := by
  ext s hs
  rw [weighted_apply μ w hs, nonpos_iff_eq_zero.1 ((setLIntegral_le_lintegral s _).trans h.le),
    mul_zero, zero_apply]

/-- An infinite total weight gives the zero measure. -/
@[simp]
theorem weighted_eq_zero_of_lintegral_eq_top {μ : Measure α} {w : α → ℝ≥0}
    (h : ∫⁻ x, (w x : ℝ≥0∞) ∂μ = ∞) : μ.weighted w = 0 := by
  simp [weighted_def, h]

/-- Weighting by the zero function gives the zero measure. -/
theorem weighted_zero (μ : Measure α) : μ.weighted 0 = 0 :=
  weighted_eq_zero_of_lintegral_eq_zero (by simp)

/-- Weighting a probability measure by the constant-one function leaves it unchanged. -/
@[simp]
theorem weighted_one (μ : Measure α) [IsProbabilityMeasure μ] : μ.weighted 1 = μ := by
  simp [weighted_def]

/-- A weighted measure is a probability measure exactly when the total weight is positive and
finite. -/
theorem isProbabilityMeasure_weighted_iff {μ : Measure α} {w : α → ℝ≥0} :
    IsProbabilityMeasure (μ.weighted w) ↔
      0 < ∫⁻ x, (w x : ℝ≥0∞) ∂μ ∧ ∫⁻ x, (w x : ℝ≥0∞) ∂μ ≠ ∞ := by
  refine ⟨fun h => ⟨pos_iff_ne_zero.2 fun h0 => ?_, fun htop => ?_⟩, fun h => ⟨?_⟩⟩
  · exact IsProbabilityMeasure.ne_zero _ (weighted_eq_zero_of_lintegral_eq_zero h0)
  · exact IsProbabilityMeasure.ne_zero _ (weighted_eq_zero_of_lintegral_eq_top htop)
  · rw [weighted_apply μ w MeasurableSet.univ, Measure.restrict_univ,
      ENNReal.inv_mul_cancel h.1.ne' h.2]

/-- A weighting is always either zero or a probability measure. -/
instance isZeroOrProbabilityMeasure_weighted {μ : Measure α} {w : α → ℝ≥0} :
    IsZeroOrProbabilityMeasure (μ.weighted w) := by
  rw [isZeroOrProbabilityMeasure_iff, weighted_apply μ w MeasurableSet.univ, restrict_univ]
  generalize ∫⁻ x, (w x : ℝ≥0∞) ∂μ = Z
  rcases eq_or_ne Z 0 with rfl | h0
  · simp
  rcases eq_or_ne Z ∞ with rfl | htop
  · simp
  exact Or.inr (ENNReal.inv_mul_cancel h0 htop)

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
  exact rnDeriv_withDensity₀ μ (aemeasurable_const.mul hw.coe_nnreal_ennreal)

/-- For an almost-everywhere measurable weight `w` with finite total weight, integrability under
the weighted law is weighted integrability under its base measure. A zero total weight is allowed:
then the weighted law is zero and `w = 0` almost everywhere, so both sides hold. -/
theorem integrable_weighted_iff {μ : Measure α} {w : α → ℝ≥0} (hw : AEMeasurable w μ)
    (hfin : ∫⁻ x, (w x : ℝ≥0∞) ∂μ ≠ ∞)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : α → E} :
    Integrable g (μ.weighted w) ↔ Integrable (fun x => w x • g x) μ := by
  have := isFiniteMeasure_withDensity hfin
  rw [← integrable_withDensity_iff_integrable_smul₀ hw,
    ← integrable_average (μ := μ.withDensity fun x => (w x : ℝ≥0∞)), weighted_def,
    withDensity_apply _ MeasurableSet.univ, restrict_univ]

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
  simp only [Pi.mul_apply]

/-- If reweighting `μ` by `w` gives a positive finite multiple of a probability measure `ν`, then
`ν` is the weighted law of `μ`. -/
theorem weighted_eq_of_withDensity_eq_smul {μ ν : Measure α} [IsProbabilityMeasure ν]
    {w : α → ℝ≥0} {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞)
    (h : (μ.withDensity fun x => (w x : ℝ≥0∞)) = c • ν) : μ.weighted w = ν := by
  have hZ : ∫⁻ x, (w x : ℝ≥0∞) ∂μ = c := by
    simpa [h] using (withDensity_apply (μ := μ) (fun x => (w x : ℝ≥0∞)) .univ).symm
  rw [weighted_def, hZ, h, smul_smul, ENNReal.inv_mul_cancel hc0 hc, one_smul]

/-- Multiplying a weight by a positive constant does not change the weighted law. -/
theorem weighted_const_smul {μ : Measure α} {w : α → ℝ≥0} {c : ℝ≥0} (hc : c ≠ 0) :
    μ.weighted (c • w) = μ.weighted w := by
  ext s hs
  simp only [weighted_apply μ _ hs, Pi.smul_apply, smul_eq_mul, ENNReal.coe_mul,
    lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← ENNReal.div_eq_inv_mul]
  exact ENNReal.mul_div_mul_left _ _ (by simpa using hc) ENNReal.coe_ne_top

/-- Successive weightings multiply their weights when the first total weight is finite. -/
theorem weighted_weighted {μ : Measure α} {w v : α → ℝ≥0} (hw : AEMeasurable w μ)
    (hwfin : ∫⁻ x, (w x : ℝ≥0∞) ∂μ ≠ ∞) :
    (μ.weighted w).weighted v = μ.weighted fun x => w x * v x := by
  rcases eq_or_ne (∫⁻ x, (w x : ℝ≥0∞) ∂μ) 0 with h0 | h0
  · -- A zero total weight forces `w = 0` almost everywhere, so both sides are zero.
    have hwv : (fun x => w x * v x) =ᵐ[μ] 0 := by
      filter_upwards [(lintegral_eq_zero_iff' hw.coe_nnreal_ennreal).1 h0] with x hx
      simp_all
    rw [weighted_congr hwv, weighted_zero, weighted_eq_zero_of_lintegral_eq_zero h0]
    exact weighted_eq_zero_of_lintegral_eq_zero (lintegral_zero_measure _)
  ext s hs
  -- Integrals against `μ.weighted w` are `Z⁻¹` times the `w`-weighted integrals against `μ`.
  rw [weighted_apply _ _ hs, weighted_apply _ _ hs, ← lintegral_indicator hs,
    lintegral_weighted hw, lintegral_weighted hw, ← lintegral_indicator hs]
  simp only [ENNReal.coe_mul, Set.indicator_mul_right]
  -- Cancel the common factor `Z⁻¹ = (∫⁻ x, w x ∂μ)⁻¹`.
  rw [ENNReal.mul_inv (.inl (ENNReal.inv_ne_zero.2 hwfin)) (.inl (ENNReal.inv_ne_top.2 h0)),
    inv_inv, mul_mul_mul_comm, ENNReal.mul_inv_cancel h0 hwfin, one_mul]

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

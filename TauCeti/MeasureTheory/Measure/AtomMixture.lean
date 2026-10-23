/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Convex

/-!
# Mixtures with one atom

This file defines `MeasureTheory.Measure.atomMixture μ c w`, the convex mixture of a measure
`μ` with a point mass at `c`. The weight `w` belongs to the unit interval and is the weight of
the added Dirac component.

The main results give the characteristic measure identities: evaluation on measurable sets,
singleton masses, probability preservation, measurability in all three parameters, decomposition
of a mixture with an absolutely continuous component, and integration against the mixture.
-/

public section

noncomputable section

open MeasureTheory Set

open scoped ENNReal unitInterval

namespace MeasureTheory.Measure

/-- The mixture assigning weight `w` to the atom at `c` and weight `1 - w` to `μ`. -/
def atomMixture {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (c : α) (w : unitInterval) : Measure α :=
  ENNReal.ofReal (w : ℝ) • Measure.dirac c +
    ENNReal.ofReal (1 - (w : ℝ)) • μ

/-- An atom mixture is the weighted sum of its Dirac and base components. -/
theorem atomMixture_def {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (c : α) (w : unitInterval) :
    atomMixture μ c w = ENNReal.ofReal (w : ℝ) • Measure.dirac c +
      ENNReal.ofReal (1 - (w : ℝ)) • μ := (rfl)

/-- Evaluation of an atom mixture on a measurable set. -/
@[simp]
theorem atomMixture_apply {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (c : α) (w : unitInterval) {s : Set α}
    (hs : MeasurableSet s) :
    atomMixture μ c w s =
      ENNReal.ofReal (w : ℝ) * s.indicator 1 c +
        ENNReal.ofReal (1 - (w : ℝ)) * μ s := by
  simp [atomMixture, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hs]

/-- The mass of an atom mixture at a singleton. -/
@[simp]
theorem atomMixture_singleton {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (c : α) (w : unitInterval) :
    atomMixture μ c w {c} =
      ENNReal.ofReal (w : ℝ) + ENNReal.ofReal (1 - (w : ℝ)) * μ {c} := by
  simp [atomMixture]

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
  rw [atomMixture]
  apply TauCeti.MeasureTheory.isProbabilityMeasure_smul_add_smul
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
  have hμs : Measurable fun b => μ b s := (Measure.measurable_coe hs).comp hμ
  fun_prop

/-- If the base component has density `f`, the same component in the mixture has density
`(1 - w) f`. The atom remains separate. -/
theorem atomMixture_withDensity {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ≥0∞) (c : α) (w : unitInterval) :
    atomMixture (μ.withDensity f) c w =
      ENNReal.ofReal (w : ℝ) • Measure.dirac c +
        μ.withDensity (fun x => ENNReal.ofReal (1 - (w : ℝ)) * f x) := by
  rw [atomMixture, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  rfl

end MeasureTheory.Measure

/-- Integrability is preserved when a point mass is mixed into a measure. -/
theorem Integrable.atomMixture {α E : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [SeminormedAddGroup E] {f : α → E} {μ : Measure α} (hf : Integrable f μ)
    (c : α) (w : unitInterval) : Integrable f (μ.atomMixture c w) := by
  rw [Measure.atomMixture]
  exact (integrable_dirac (by simp)).smul_measure (by simp) |>.add_measure
    (hf.smul_measure (by simp))

namespace MeasureTheory.Measure

/-- Integrating against an atom mixture gives the corresponding convex combination. -/
theorem integral_atomMixture {α E : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) (c : α) (w : unitInterval) (f : α → E) (hf : Integrable f μ) :
    ∫ x, f x ∂μ.atomMixture c w =
      (w : ℝ) • f c + (1 - (w : ℝ)) • ∫ x, f x ∂μ := by
  rw [Measure.atomMixture, integral_add_measure]
  · simp [ENNReal.toReal_ofReal (unitInterval.nonneg w),
      ENNReal.toReal_ofReal (sub_nonneg.mpr (unitInterval.le_one w))]
  · exact (integrable_dirac (by simp)).smul_measure (by simp)
  · exact hf.smul_measure (by simp)

end MeasureTheory.Measure

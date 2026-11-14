/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Convex
public import TauCeti.MeasureTheory.Measure.Support
import TauCeti.MeasureTheory.Measure.Dirac

/-!
# Mixtures with one atom

This file defines `MeasureTheory.Measure.atomMixture μ c w`, the convex mixture of a measure
`μ` with a point mass at `c`. The weight `w` belongs to the unit interval and is the weight of
the added Dirac component.

The main results give the characteristic measure identities: evaluation on measurable sets,
singleton masses, probability preservation, measurability in all three parameters, decomposition
of a mixture with an absolutely continuous component, pushforward along measurable maps, and
integration against the mixture. Its topological support is the union of the supports of the
components with positive weight, including the two pure-component boundaries.
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
  simp [atomMixture, _root_.add_apply, _root_.smul_apply, Measure.dirac_apply' _ hs]

/-- The mass of an atom mixture at a singleton. -/
-- Evaluate a singleton before expanding the mixture measure.
@[simp↓]
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

/-- The support of an atom mixture contains exactly the supports of its positive-weight
components. In a non-T₁ space the support of the atom is the closure of its singleton. -/
theorem support_atomMixture {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) (c : α) (w : unitInterval) :
    (μ.atomMixture c w).support =
      if w = 0 then μ.support else if w = 1 then closure {c} else closure {c} ∪ μ.support := by
  by_cases hw0 : w = 0
  · simp [hw0]
  by_cases hw1 : w = 1
  · simp [hw1]
  have hrest : ENNReal.ofReal (1 - (w : ℝ)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr
      (unitInterval.coe_lt_one.mpr (unitInterval.lt_one_iff_ne_one.mpr hw1)))
  rw [ite_eq_right hw0, ite_eq_right hw1, atomMixture_def, support_add,
    support_smul_measure _ _ (ENNReal.ofReal_ne_zero_iff.mpr
      (unitInterval.pos_iff_ne_zero.mpr hw0)),
    support_smul_measure _ _ hrest, support_dirac]

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

/-- Pushing an atom mixture forward along a measurable map mixes the image measure with the point
mass at the image of the atom. -/
theorem map_atomMixture {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (c : α) (w : unitInterval) {f : α → β} (hf : Measurable f) :
    (μ.atomMixture c w).map f = (μ.map f).atomMixture (f c) w := by
  rw [atomMixture_def, atomMixture_def, Measure.map_add _ _ hf,
    Measure.map_smul _ hf.aemeasurable, Measure.map_smul _ hf.aemeasurable, map_dirac' hf]

/-- The real-valued evaluation of an atom mixture of a finite measure on a measurable set. -/
theorem atomMixture_real_apply {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (c : α) (w : unitInterval) {s : Set α}
    (hs : MeasurableSet s) :
    (atomMixture μ c w).real s =
      (w : ℝ) * s.indicator 1 c + (1 - (w : ℝ)) * μ.real s := by
  have hw := unitInterval.nonneg w
  have hw' := sub_nonneg.mpr (unitInterval.le_one w)
  by_cases hc : c ∈ s
  · rw [measureReal_def, atomMixture_apply _ _ _ hs, indicator_of_mem hc, Pi.one_apply, mul_one,
      ENNReal.toReal_add (by simp) (by finiteness)]
    simp [measureReal_def, hc, hw, hw']
  · simp [measureReal_def, atomMixture_apply _ _ _ hs, hc, hw']

/-- The real mass of an atom mixture of a finite measure at the distinguished atom. -/
@[simp]
theorem atomMixture_real_singleton {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (c : α) (w : unitInterval) :
    (atomMixture μ c w).real {c} = (w : ℝ) + (1 - (w : ℝ)) * μ.real {c} := by
  rw [measureReal_def, atomMixture_singleton, ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (unitInterval.nonneg w),
    ENNReal.toReal_ofReal (sub_nonneg.mpr (unitInterval.le_one w)), measureReal_def]

/-- Away from the distinguished atom, an atom mixture of a finite measure rescales the original
real singleton mass. -/
theorem atomMixture_real_singleton_of_ne {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ] {c x : α} (hcx : c ≠ x)
    (w : unitInterval) :
    (atomMixture μ c w).real {x} = (1 - (w : ℝ)) * μ.real {x} := by
  simp [atomMixture_real_apply _ _ _ (measurableSet_singleton x), hcx]

end MeasureTheory.Measure

/-- Integrability is preserved when a point mass is mixed into a measure. -/
theorem Integrable.atomMixture {α E : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [SeminormedAddGroup E] {f : α → E} {μ : Measure α} (hf : Integrable f μ)
    (c : α) (w : unitInterval) : Integrable f (μ.atomMixture c w) := by
  rw [Measure.atomMixture]
  exact (integrable_dirac (by simp)).smul_measure (by simp) |>.add_measure
    (hf.smul_measure (by simp))

namespace MeasureTheory.Measure

/-- Away from the pure-atom endpoint, a function is integrable for an atom mixture exactly when it
is integrable for the base component: the atom itself never obstructs integrability. -/
theorem integrable_atomMixture_iff {α E : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [SeminormedAddGroup E] (μ : Measure α) (c : α) {w : unitInterval} (hw : w ≠ 1) {f : α → E} :
    Integrable f (μ.atomMixture c w) ↔ Integrable f μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ Integrable.atomMixture h c w⟩
  rw [atomMixture_def] at h
  exact (integrable_smul_measure (ENNReal.ofReal_ne_zero_iff.2 <| sub_pos.2 <|
    unitInterval.lt_one_iff_ne_one.2 hw) ENNReal.ofReal_ne_top).1 h.right_of_add_measure

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

/-- Integrating a function that vanishes at the atom against an atom mixture gives `1 - w` times
its integral against the base component. This is an identity of Bochner integrals: when `f` is not
integrable for `μ`, both sides are `0` (at `w = 1` because the mixture is the point mass at `c`). -/
theorem integral_atomMixture_of_eq_zero {α E : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α) (c : α)
    (w : unitInterval) {f : α → E} (hf : f c = 0) :
    ∫ x, f x ∂μ.atomMixture c w = (1 - (w : ℝ)) • ∫ x, f x ∂μ := by
  by_cases hE : CompleteSpace E
  swap
  · rw [integral_of_not_completeSpace hE, integral_of_not_completeSpace hE, smul_zero]
  by_cases hμ : Integrable f μ
  · rw [integral_atomMixture μ c w f hμ, hf, smul_zero, zero_add]
  by_cases hw : w = 1
  · simp [hw, hf]
  rw [integral_undef hμ, integral_undef ((integrable_atomMixture_iff μ c hw).not.2 hμ), smul_zero]

end MeasureTheory.Measure

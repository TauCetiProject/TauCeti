/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Atom
public import TauCeti.MeasureTheory.Measure.Decomposition.Atomic
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

/-!
# Pure point, absolutely continuous and singular continuous parts of a measure

Let `X` be a space with measurable singletons, `ν` a reference measure with zero singleton masses,
such as Lebesgue measure, and `μ` an s-finite measure with a Lebesgue decomposition relative to
`ν` (for instance, `ν` σ-finite). Then `μ` splits as
`μ = atomicPart μ + ν.withDensity (μ.rnDeriv ν) + singularContinuousPart μ ν`: a part carried by
a countable set, the absolutely continuous part of the Lebesgue decomposition, and a part that is
mutually singular to `ν` and gives zero mass to every singleton. This split is unique. On a
countably separated space, such as `ℝ` with its Borel σ-algebra, the singular continuous part of a
σ-finite measure has no atoms (in the sense of `MeasureTheory.Measure.IsAtom`). For the diagonal
measures of a projection-valued measure on `ℝ` and `ν` Lebesgue measure, the three parts are the
pure point, absolutely continuous and singular continuous spectral types.

## Main definitions

* `MeasureTheory.Measure.singularContinuousPart μ ν`: the singular part, relative to `ν`, of the
  diffuse part of `μ`.

## Main results

* `MeasureTheory.Measure.not_isAtom_singularContinuousPart`: the singular continuous part of a
  σ-finite measure on a countably separated space has no atoms.
* `MeasureTheory.Measure.atomicPart_add_withDensity_rnDeriv_add_singularContinuousPart`: the
  pure point, absolutely continuous and singular continuous split.
* `eq_atomicPart_and_eq_withDensity_rnDeriv_and_eq_singularContinuousPart_of_eq_add` (in
  `MeasureTheory.Measure`): its uniqueness.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, Graduate Studies in Mathematics 99,
  AMS 2009, Section 3.3.
-/

public section

noncomputable section

open MeasureTheory MeasurableSpace Set
open scoped ENNReal

namespace MeasureTheory.Measure

variable {X : Type*} [MeasurableSpace X] {μ ν : Measure X}

/-- The **singular continuous part** of `μ` relative to `ν`: the part of the diffuse part of `μ`
that is mutually singular to `ν`. -/
def singularContinuousPart (μ ν : Measure X) : Measure X :=
  (diffusePart μ).singularPart ν

/-- The singular continuous part is the singular part of the diffuse part. -/
theorem singularContinuousPart_def (μ ν : Measure X) :
    singularContinuousPart μ ν = (diffusePart μ).singularPart ν := (rfl)

/-- The singular continuous part is mutually singular to the reference measure. -/
theorem mutuallySingular_singularContinuousPart (μ ν : Measure X) :
    singularContinuousPart μ ν ⟂ₘ ν :=
  mutuallySingular_singularPart _ _

/-- The singular continuous part does not exceed the diffuse part. -/
theorem singularContinuousPart_le_diffusePart (μ ν : Measure X) :
    singularContinuousPart μ ν ≤ diffusePart μ :=
  singularPart_le _ _

/-- The singular continuous part does not exceed the measure. -/
theorem singularContinuousPart_le (μ ν : Measure X) : singularContinuousPart μ ν ≤ μ :=
  (singularContinuousPart_le_diffusePart μ ν).trans (diffusePart_le μ)

/-- The singular continuous part is absolutely continuous with respect to the measure. -/
theorem singularContinuousPart_absolutelyContinuous (μ ν : Measure X) :
    singularContinuousPart μ ν ≪ μ :=
  (singularContinuousPart_le μ ν).absolutelyContinuous

/-- The singular continuous part of a measure that is absolutely continuous with respect to the
reference measure vanishes. -/
theorem singularContinuousPart_eq_zero_of_ac (h : μ ≪ ν) : singularContinuousPart μ ν = 0 :=
  singularPart_eq_zero_of_ac ((diffusePart_absolutelyContinuous μ).trans h)

/-- The zero measure has zero singular continuous part. -/
@[simp]
theorem singularContinuousPart_zero (ν : Measure X) : singularContinuousPart 0 ν = 0 :=
  singularContinuousPart_eq_zero_of_ac (.zero ν)

/-- Relative to the zero measure, the singular continuous part is the diffuse part. -/
@[simp]
theorem singularContinuousPart_zero_right (μ : Measure X) :
    singularContinuousPart μ 0 = diffusePart μ :=
  singularPart_zero_right _

/-- A measure has zero singular continuous part relative to itself. -/
@[simp]
theorem singularContinuousPart_self (μ : Measure X) : singularContinuousPart μ μ = 0 :=
  singularContinuousPart_eq_zero_of_ac .rfl

/-- A measure with a density relative to `ν` has zero singular continuous part relative to `ν`. -/
@[simp]
theorem singularContinuousPart_withDensity (ν : Measure X) (f : X → ℝ≥0∞) :
    singularContinuousPart (ν.withDensity f) ν = 0 :=
  singularContinuousPart_eq_zero_of_ac (withDensity_absolutelyContinuous ν f)

/-- The singular continuous part of a finite measure is finite. -/
instance singularContinuousPart_isFiniteMeasure (μ ν : Measure X) [IsFiniteMeasure μ] :
    IsFiniteMeasure (singularContinuousPart μ ν) := by
  rw [singularContinuousPart_def]
  infer_instance

/-- The singular continuous part of a σ-finite measure is σ-finite. -/
instance singularContinuousPart_sigmaFinite (μ ν : Measure X) [SigmaFinite μ] :
    SigmaFinite (singularContinuousPart μ ν) := by
  rw [singularContinuousPart_def]
  infer_instance

/-- The singular continuous part has a Lebesgue decomposition relative to the reference measure. -/
instance singularContinuousPart_haveLebesgueDecomposition (μ ν : Measure X) :
    HaveLebesgueDecomposition (singularContinuousPart μ ν) ν := by
  rw [singularContinuousPart_def]
  infer_instance

/-- When singletons are measurable, the singular continuous part gives zero mass to every
singleton. -/
instance singularContinuousPart_nullSingletonClass [MeasurableSingletonClass X]
    (μ ν : Measure X) : NullSingletonClass (singularContinuousPart μ ν) :=
  ⟨fun x ↦ (singularPart_le (diffusePart μ) ν).absolutelyContinuous
    (diffusePart_apply_singleton μ x)⟩

/-- For a measure with zero singleton masses, the singular continuous part is the singular part. -/
theorem singularContinuousPart_eq_singularPart [NullSingletonClass μ] (ν : Measure X) :
    singularContinuousPart μ ν = μ.singularPart ν := by
  have : (positiveSingletons μ)ᶜ = univ := eq_univ_of_forall fun x ↦ by simp
  rw [singularContinuousPart_def, diffusePart_def, this, restrict_univ]

/-- The singular continuous part of a σ-finite measure on a countably separated space has no
atoms. -/
theorem not_isAtom_singularContinuousPart [CountablySeparated X] (μ ν : Measure X)
    [SigmaFinite μ] (s : Set X) : ¬ (singularContinuousPart μ ν).IsAtom s :=
  have := measurableSingletonClass_of_countablySeparated (α := X)
  not_isAtom_of_nullSingletonClass s

/-- **Pure point, absolutely continuous and singular continuous decomposition.** On a space with
measurable singletons, an s-finite measure `μ` having a Lebesgue decomposition relative to a
measure `ν` with zero singleton masses is the sum of its atomic part, the absolutely continuous
part of its Lebesgue decomposition, and its singular continuous part. -/
theorem atomicPart_add_withDensity_rnDeriv_add_singularContinuousPart [MeasurableSingletonClass X]
    (μ ν : Measure X) [SFinite μ] [NullSingletonClass ν] [HaveLebesgueDecomposition μ ν] :
    atomicPart μ + ν.withDensity (μ.rnDeriv ν) + singularContinuousPart μ ν = μ := by
  have hA := measurableSet_positiveSingletons μ
  have hat : atomicPart μ = (μ.singularPart ν).restrict (positiveSingletons μ) := by
    rw [← singularPart_eq_self.2 (mutuallySingular_atomicPart μ ν), atomicPart_def,
      singularPart_restrict μ ν hA]
  rw [singularContinuousPart_def, diffusePart_def, singularPart_restrict μ ν hA.compl, hat,
    add_right_comm, restrict_add_restrict_compl hA, singularPart_add_rnDeriv]

/-- **Uniqueness of the pure point, absolutely continuous and singular continuous split.**
Relative to a measure `ν` with zero singleton masses, if `μ = a + ν.withDensity f + s`, where `a`
is carried by a countable set, `f` is measurable, and `s` is mutually singular to `ν` and gives
zero mass to every singleton, then `a`, `ν.withDensity f` and `s` are the atomic, absolutely
continuous and singular continuous parts of `μ`. -/
theorem eq_atomicPart_and_eq_withDensity_rnDeriv_and_eq_singularContinuousPart_of_eq_add
    [NullSingletonClass ν] {a s : Measure X} {f : X → ℝ≥0∞} {S : Set X} (hS : S.Countable)
    (ha : a Sᶜ = 0) (hf : Measurable f) (hs : s ⟂ₘ ν) [NullSingletonClass s]
    (h : μ = a + ν.withDensity f + s) :
    a = atomicPart μ ∧ ν.withDensity f = ν.withDensity (μ.rnDeriv ν) ∧
      s = singularContinuousPart μ ν := by
  have : NullSingletonClass (ν.withDensity f + s) := ⟨fun x ↦ by simp⟩
  obtain ⟨ha', hd⟩ := eq_atomicPart_and_eq_diffusePart_of_eq_add hS ha (h.trans (add_assoc _ _ _))
  have haν : a ⟂ₘ ν := .mk ha (hS.measure_zero ν) (by simp)
  refine ⟨ha', eq_withDensity_rnDeriv hf (haν.add_left hs) ?_, ?_⟩
  · rw [h, add_right_comm]
  · exact eq_singularPart hf hs (hd.symm.trans (add_comm _ _))

end MeasureTheory.Measure

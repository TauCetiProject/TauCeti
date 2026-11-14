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
public import Mathlib.Order.Filter.CountableSeparatingOn

/-!
# Pure point, absolutely continuous and singular continuous parts of a measure

Every atom of a σ-finite measure on a countably separated measurable space, such as `ℝ` with its
Borel σ-algebra, is concentrated on one of its points. Hence a σ-finite measure with zero mass on
every singleton has no atoms (in the sense of `MeasureTheory.Measure.IsAtom`), and the diffuse
part `MeasureTheory.Measure.diffusePart μ` of a σ-finite measure is atomless.

Relative to a reference measure `ν` with zero singleton masses, such as Lebesgue measure, an
s-finite measure `μ` splits as
`μ = atomicPart μ + ν.withDensity (μ.rnDeriv ν) + singularContinuousPart μ ν`: a part carried by
a countable set, the absolutely continuous part of the Lebesgue decomposition, and a part that is
mutually singular to `ν` and gives zero mass to every singleton. This split is unique. For the
diagonal measures of a projection-valued measure on `ℝ` and `ν` Lebesgue measure, the three parts
are the pure point, absolutely continuous and singular continuous spectral types.

## Main definitions

* `MeasureTheory.Measure.singularContinuousPart μ ν`: the singular part, relative to `ν`, of the
  diffuse part of `μ`.

## Main results

* `MeasureTheory.Measure.IsAtom.exists_measure_diff_singleton_eq_zero`: an atom of a σ-finite
  measure on a countably separated space is concentrated on one of its points.
* `MeasureTheory.Measure.not_isAtom_of_nullSingletonClass`: such a measure with zero singleton
  masses has no atoms.
* `MeasureTheory.Measure.atomicPart_add_withDensity_rnDeriv_add_singularContinuousPart`: the
  pure point, absolutely continuous and singular continuous split.
* `MeasureTheory.Measure.eq_of_eq_add_withDensity_add`: its uniqueness.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, Graduate Studies in Mathematics 99,
  AMS 2009, Section 3.3.
-/

public section

noncomputable section

open MeasureTheory MeasurableSpace Set Filter
open scoped ENNReal

namespace MeasureTheory.Measure

variable {X : Type*} [MeasurableSpace X] {μ ν : Measure X}

/-- An atom of a σ-finite measure has finite mass. -/
private theorem IsAtom.measure_ne_top [SigmaFinite μ] {s : Set X} (hs : μ.IsAtom s) :
    μ s ≠ ∞ := by
  rw [isAtom_iff] at hs
  obtain ⟨n, hn⟩ : ∃ n, μ (s ∩ spanningSets μ n) ≠ 0 := by
    by_contra! h
    refine hs.2.1.ne' (measure_mono_null (fun x hx ↦ ?_) (measure_iUnion_null h))
    obtain ⟨n, hn⟩ := mem_iUnion.1 (iUnion_spanningSets μ ▸ mem_univ x)
    exact mem_iUnion.2 ⟨n, hx, hn⟩
  rcases hs.2.2 (hs.1.inter (measurableSet_spanningSets μ n)) inter_subset_left with h0 | heq
  · exact absurd h0 hn
  · exact heq ▸ ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top μ n)).ne

/-- **Atoms are points.** An atom of a σ-finite measure on a countably separated measurable space
is concentrated on one of its points. -/
theorem IsAtom.exists_measure_diff_singleton_eq_zero [CountablySeparated X] [SigmaFinite μ]
    {s : Set X} (hs : μ.IsAtom s) : ∃ x ∈ s, μ (s \ {x}) = 0 := by
  have hfin := hs.measure_ne_top
  rw [isAtom_iff] at hs
  have hl : ∀ U, MeasurableSet U → U ∈ ae (μ.restrict s) ∨ Uᶜ ∈ ae (μ.restrict s) := by
    intro U hU
    rw [mem_ae_iff, mem_ae_iff, compl_compl, restrict_apply hU.compl, restrict_apply hU,
      ← sdiff_eq_compl_inter]
    rcases hs.2.2 (hU.inter hs.1) inter_subset_right with h0 | heq
    · exact Or.inr h0
    · refine Or.inl ?_
      have hadd := measure_inter_add_sdiff (μ := μ) s hU
      rw [inter_comm, heq] at hadd
      exact (ENNReal.add_right_inj hfin).1 (hadd.trans (add_zero _).symm)
  have : HasCountableSeparatingOn X MeasurableSet s :=
    HasCountableSeparatingOn.mono (fun _ h ↦ h) (subset_univ s)
  obtain ⟨x, hxs, hx⟩ := exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating
    MeasurableSet (ae_restrict_mem hs.1) (nonempty_of_measure_ne_zero hs.2.1.ne') hl
  refine ⟨x, hxs, ?_⟩
  rwa [mem_ae_iff, restrict_apply' hs.1, ← sdiff_eq_compl_inter] at hx

/-- A σ-finite measure on a countably separated measurable space with zero mass on every singleton
has no atoms. -/
theorem not_isAtom_of_nullSingletonClass [CountablySeparated X] [SigmaFinite μ]
    [NullSingletonClass μ] (s : Set X) : ¬ μ.IsAtom s := fun hs ↦ by
  obtain ⟨x, -, hx⟩ := hs.exists_measure_diff_singleton_eq_zero
  exact (isAtom_iff.1 hs).2.1.ne'
    (measure_mono_null (subset_sdiff_union s {x}) (measure_union_null hx (measure_singleton x)))

/-- The diffuse part of a σ-finite measure on a countably separated space has no atoms. -/
theorem not_isAtom_diffusePart [CountablySeparated X] (μ : Measure X) [SigmaFinite μ]
    (s : Set X) : ¬ (diffusePart μ).IsAtom s :=
  have := measurableSingletonClass_of_countablySeparated (α := X)
  not_isAtom_of_nullSingletonClass s

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

/-- The singular continuous part does not exceed the measure. -/
theorem singularContinuousPart_le (μ ν : Measure X) : singularContinuousPart μ ν ≤ μ :=
  (singularPart_le _ _).trans (diffusePart_le μ)

/-- The singular continuous part gives zero mass to every singleton. -/
instance singularContinuousPart_nullSingletonClass [MeasurableSingletonClass X]
    (μ ν : Measure X) : NullSingletonClass (singularContinuousPart μ ν) :=
  ⟨fun x ↦ measure_mono_null (fun _ ↦ id)
    (nonpos_iff_eq_zero.1 ((singularPart_le _ ν {x}).trans (diffusePart_apply_singleton μ x).le))⟩

/-- The singular continuous part of a σ-finite measure on a countably separated space has no
atoms. -/
theorem not_isAtom_singularContinuousPart [CountablySeparated X] (μ ν : Measure X)
    [SigmaFinite μ] (s : Set X) : ¬ (singularContinuousPart μ ν).IsAtom s :=
  have := measurableSingletonClass_of_countablySeparated (α := X)
  have : SigmaFinite (singularContinuousPart μ ν) := by
    rw [singularContinuousPart_def]
    infer_instance
  not_isAtom_of_nullSingletonClass s

/-- The atomic part of an s-finite measure is mutually singular to every measure with zero
singleton masses. -/
theorem mutuallySingular_atomicPart [MeasurableSingletonClass X] (μ ν : Measure X) [SFinite μ]
    [NullSingletonClass ν] : atomicPart μ ⟂ₘ ν :=
  ⟨(positiveSingletons μ)ᶜ, (measurableSet_positiveSingletons μ).compl,
    atomicPart_apply_compl μ, by
      rw [compl_compl]
      exact (countable_positiveSingletons μ).measure_zero ν⟩

/-- **Pure point, absolutely continuous and singular continuous decomposition.** Relative to a
measure `ν` with zero singleton masses, an s-finite measure is the sum of its atomic part, the
absolutely continuous part of its Lebesgue decomposition, and its singular continuous part. -/
theorem atomicPart_add_withDensity_rnDeriv_add_singularContinuousPart [MeasurableSingletonClass X]
    (μ ν : Measure X) [SFinite μ] [NullSingletonClass ν] [HaveLebesgueDecomposition μ ν] :
    atomicPart μ + ν.withDensity (μ.rnDeriv ν) + singularContinuousPart μ ν = μ := by
  have hA := measurableSet_positiveSingletons μ
  have hw : (ν.withDensity (μ.rnDeriv ν)).restrict (positiveSingletons μ) = 0 :=
    restrict_eq_zero.2 (withDensity_absolutelyContinuous ν _
      ((countable_positiveSingletons μ).measure_zero ν))
  have hres (A : Set X) : μ.restrict A =
      (μ.singularPart ν).restrict A + (ν.withDensity (μ.rnDeriv ν)).restrict A := by
    rw [← restrict_add, singularPart_add_rnDeriv]
  have hat : atomicPart μ = (μ.singularPart ν).restrict (positiveSingletons μ) := by
    rw [atomicPart_def, hres, hw, add_zero]
  rw [singularContinuousPart_def, diffusePart_def, singularPart_restrict μ ν hA.compl, hat,
    add_right_comm, restrict_add_restrict_compl hA, singularPart_add_rnDeriv]

/-- **Uniqueness of the pure point, absolutely continuous and singular continuous split.** If
`μ = a + ν.withDensity f + s`, where `a` is carried by a countable set, `f` is measurable, and `s`
is mutually singular to `ν` with zero singleton masses, then `a`, `ν.withDensity f` and `s` are the
atomic, absolutely continuous and singular continuous parts of `μ`. -/
theorem eq_of_eq_add_withDensity_add [NullSingletonClass ν] {a s : Measure X} {f : X → ℝ≥0∞}
    {S : Set X} (hS : S.Countable) (ha : a Sᶜ = 0) (hf : Measurable f) (hs : s ⟂ₘ ν)
    [NullSingletonClass s] (h : μ = a + ν.withDensity f + s) :
    a = atomicPart μ ∧ ν.withDensity f = ν.withDensity (μ.rnDeriv ν) ∧
      s = singularContinuousPart μ ν := by
  have : NullSingletonClass (ν.withDensity f + s) := ⟨fun x ↦ by simp⟩
  obtain ⟨ha', hd⟩ := eq_atomicPart_and_eq_diffusePart_of_eq_add hS ha (h.trans (add_assoc _ _ _))
  have haν : a ⟂ₘ ν := .mk ha (hS.measure_zero ν) (by simp)
  refine ⟨ha', eq_withDensity_rnDeriv hf (haν.add_left hs) ?_, ?_⟩
  · rw [h, add_right_comm]
  · exact eq_singularPart hf hs (hd.symm.trans (add_comm _ _))

end MeasureTheory.Measure

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Basic
public import Mathlib.MeasureTheory.Measure.Complex

/-!
# Polarized complex measures of a projection-valued measure

A normalized projection-valued measure `P` carries a finite diagonal positive measure
`P.diag ξ` for every vector `ξ`. Complex polarization produces a genuine complex vector measure
`P.polarizedComplexMeasure ψ ξ` whose value on a measurable set `B` is
`⟪ψ, P.proj B hB ξ⟫_ℂ`. Its dependence on `ψ` is conjugate-linear and on `ξ` linear.

The construction uses Mathlib's signed-measure and complex-measure conversions: countable
additivity comes from the existing diagonal measures, not a second PVM construction.

## Provenance

Adapted from the four-term polarization formula in the maintained Kitware DKPS formalization
(AIQ-Kitware, Apache-2.0):
https://github.com/AIQ-Kitware/aiq-dkps-formalization
(`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Polarization.lean`).

The underlying `ProjValMeasure` diagonal measures were originally adapted from Adam Bornemann's
Spectra (Apache-2.0); see `ProjValMeasure/Basic.lean` for the retained notices.
-/

public section

open MeasureTheory
open scoped InnerProductSpace

namespace TauCeti
namespace ProjValMeasure

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A finite diagonal measure, embedded as a complex vector measure. -/
noncomputable def diagComplex (P : ProjValMeasure X H) (v : H) : ComplexMeasure X :=
  (@Measure.toSignedMeasure X _ (P.diag v) (P.diag_finite v)).toComplexMeasure 0

@[simp]
theorem diagComplex_apply (P : ProjValMeasure X H) (v : H) (B : Set X)
    (hB : MeasurableSet B) :
    diagComplex P v B = (((P.diag v) B).toReal : ℂ) := by
  unfold diagComplex
  rw [SignedMeasure.toComplexMeasure_apply,
    Measure.toSignedMeasure_apply_measurable hB, measureReal_def]
  rfl

/-- The polarized complex measure associated to a pair of vectors. -/
noncomputable def polarizedComplexMeasure (P : ProjValMeasure X H) (ψ ξ : H) :
    ComplexMeasure X :=
  (1 / 4 : ℂ) •
    (diagComplex P (ξ + ψ) + Complex.I • diagComplex P (ξ + Complex.I • ψ) -
      diagComplex P (ξ - ψ) - Complex.I • diagComplex P (ξ - Complex.I • ψ))

/-- Polarization evaluates to the matrix element of the PVM projection. -/
@[simp]
theorem polarizedComplexMeasure_apply (P : ProjValMeasure X H) (ψ ξ : H)
    (B : Set X) (hB : MeasurableSet B) :
    P.polarizedComplexMeasure ψ ξ B = ⟪ψ, P.proj B hB ξ⟫_ℂ := by
  have hpol := ContinuousLinearMap.inner_polarization (P.proj B hB) ψ ξ
  rw [P.inner_proj B hB (ξ + ψ), P.inner_proj B hB (ξ + Complex.I • ψ),
    P.inner_proj B hB (ξ - ψ), P.inner_proj B hB (ξ - Complex.I • ψ)] at hpol
  simpa only [polarizedComplexMeasure, _root_.smul_apply, _root_.add_apply,
    _root_.sub_apply,
    diagComplex_apply P (ξ + ψ) B hB,
    diagComplex_apply P (ξ + Complex.I • ψ) B hB,
    diagComplex_apply P (ξ - ψ) B hB,
    diagComplex_apply P (ξ - Complex.I • ψ) B hB,
    smul_eq_mul] using hpol

/-- On the diagonal, the polarized measure recovers the PVM's positive scalar measure. -/
theorem polarizedComplexMeasure_diag (P : ProjValMeasure X H) (ξ : H)
    (B : Set X) (hB : MeasurableSet B) :
    P.polarizedComplexMeasure ξ ξ B = (((P.diag ξ) B).toReal : ℂ) := by
  rw [P.polarizedComplexMeasure_apply ξ ξ B hB, P.inner_proj B hB ξ]

/-- Polarizing against the zero vector in the first argument yields zero. -/
@[simp]
theorem polarizedComplexMeasure_zero_left (P : ProjValMeasure X H) (v : H) :
    P.polarizedComplexMeasure 0 v = 0 := by
  ext B hB
  rw [P.polarizedComplexMeasure_apply (0 : H) v B hB]
  simp

/-- Polarizing against the zero vector in the second argument yields zero. -/
@[simp]
theorem polarizedComplexMeasure_zero_right (P : ProjValMeasure X H) (u : H) :
    P.polarizedComplexMeasure u 0 = 0 := by
  ext B hB
  rw [P.polarizedComplexMeasure_apply u (0 : H) B hB]
  simp

/-- The complex measure is additive in its first (conjugate-linear) argument. -/
theorem polarizedComplexMeasure_add_left (P : ProjValMeasure X H) (ψ ψ' ξ : H) :
    P.polarizedComplexMeasure (ψ + ψ') ξ =
      P.polarizedComplexMeasure ψ ξ + P.polarizedComplexMeasure ψ' ξ := by
  ext B hB
  have heval (u v : H) :
      P.polarizedComplexMeasure u v B = ⟪u, P.proj B hB v⟫_ℂ :=
    P.polarizedComplexMeasure_apply u v B hB
  simp only [heval, _root_.add_apply, inner_add_left]

/-- The complex measure is additive in its second (linear) argument. -/
theorem polarizedComplexMeasure_add_right (P : ProjValMeasure X H) (ψ ξ ξ' : H) :
    P.polarizedComplexMeasure ψ (ξ + ξ') =
      P.polarizedComplexMeasure ψ ξ + P.polarizedComplexMeasure ψ ξ' := by
  ext B hB
  have heval (u v : H) :
      P.polarizedComplexMeasure u v B = ⟪u, P.proj B hB v⟫_ℂ :=
    P.polarizedComplexMeasure_apply u v B hB
  simp only [heval, _root_.add_apply, map_add, inner_add_right]

/-- The first argument of the polarized complex measure is conjugate-homogeneous. -/
theorem polarizedComplexMeasure_smul_left (P : ProjValMeasure X H) (c : ℂ) (ψ ξ : H) :
    P.polarizedComplexMeasure (c • ψ) ξ =
      (star c) • P.polarizedComplexMeasure ψ ξ := by
  ext B hB
  have heval (u v : H) :
      P.polarizedComplexMeasure u v B = ⟪u, P.proj B hB v⟫_ℂ :=
    P.polarizedComplexMeasure_apply u v B hB
  simp only [heval, _root_.smul_apply, inner_smul_left, starRingEnd_apply, smul_eq_mul]

/-- The second argument of the polarized complex measure is homogeneous. -/
theorem polarizedComplexMeasure_smul_right (P : ProjValMeasure X H) (c : ℂ) (ψ ξ : H) :
    P.polarizedComplexMeasure ψ (c • ξ) =
      c • P.polarizedComplexMeasure ψ ξ := by
  ext B hB
  have heval (u v : H) :
      P.polarizedComplexMeasure u v B = ⟪u, P.proj B hB v⟫_ℂ :=
    P.polarizedComplexMeasure_apply u v B hB
  simp only [heval, _root_.smul_apply, map_smul, inner_smul_right, smul_eq_mul]

end ProjValMeasure
end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Matrix.Scaling
public import TauCeti.InformationTheory.KullbackLeibler.Finite

/-!
# Finite matrix entropy and measure-theoretic relative entropy

A nonnegative matrix and a finite measure on a product of finite spaces encode the
same masses. For a strictly positive reference matrix, Mathlib's
`InformationTheory.klDiv π R` is `Matrix.relEntropy P K` plus the difference of the
total masses of `R` and `π`. Thus the two objectives agree when those masses agree,
and differ by a constant when the plan mass is prescribed.

The identity connects the objective minimized by finite Sinkhorn scaling to the
measure-theoretic Schrödinger objective. The finite-atom KL formula is proved in
`TauCeti/InformationTheory/KullbackLeibler/Finite.lean`.
-/

public section

open MeasureTheory InformationTheory Matrix
open scoped ENNReal

namespace TauCeti

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- For finite measures on a finite product with strictly positive reference masses,
KL divergence is matrix entropy plus Mathlib's finite-measure mass correction.
The plan is encoded by its singleton masses; no separate nonnegativity assumption on
`P` is needed. -/
theorem klDiv_eq_ofReal_relEntropy_add_mass_correction_of_real_singleton
    (π R : Measure (ι × κ)) [IsFiniteMeasure π] [IsFiniteMeasure R]
    (P K : Matrix ι κ ℝ)
    (hπ : ∀ i j, π.real {(i, j)} = P i j)
    (hR : ∀ i j, R.real {(i, j)} = K i j)
    (hK : ∀ i j, 0 < K i j) :
    klDiv π R = ENNReal.ofReal
      (Matrix.relEntropy P K + R.real Set.univ - π.real Set.univ) := by
  have hRpos : ∀ q : ι × κ, R {q} ≠ 0 := by
    rintro ⟨i, j⟩ hzero
    have h := hK i j
    rw [← hR i j] at h
    simp [Measure.real, hzero] at h
  rw [klDiv_eq_ofReal_sum_log_singleton hRpos]
  have hsum :
      (∑ q : ι × κ, π.real {q} * Real.log (π.real {q} / R.real {q})) =
        Matrix.relEntropy P K := by
    rw [Matrix.relEntropy_def, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hπ i j, hR i j]
    by_cases hP : P i j = 0
    · simp [hP]
    · rw [Real.log_div hP (ne_of_gt (hK i j))]
      ring
  rw [hsum]

end TauCeti

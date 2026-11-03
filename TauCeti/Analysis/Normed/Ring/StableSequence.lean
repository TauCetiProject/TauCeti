/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Stable sequences and condition numbers in normed rings

A sequence `aₙ` of elements of normed rings is *stable* (`TauCeti.IsStableSequence`) when its
members are eventually invertible and their inverses are uniformly bounded in norm. This is the
notion that governs approximation methods such as the finite-section method: a stable sequence of
approximating matrices has uniformly bounded condition numbers
`κ(aₙ) = ‖aₙ‖ ‖aₙ⁻¹‖` (`TauCeti.conditionNumber`) as soon as its norms are bounded.

Stability is invariant under `star`. The operator-level characterization of stability by
uniform lower bounds is in `TauCeti.Analysis.Normed.Operator.StableSequence`.

## Main definitions

* `TauCeti.conditionNumber a`: the condition number `‖a‖ ‖a⁻¹‖`, with value `0` at a non-unit.
* `TauCeti.IsStableSequence a`: eventual invertibility with uniformly bounded inverse norms.

## Main results

* `TauCeti.one_le_conditionNumber`: units have condition number at least one.
* `TauCeti.IsStableSequence.exists_conditionNumber_le`: a bounded stable sequence has uniformly
  bounded condition numbers.
* `TauCeti.isStableSequence_star_iff`: a sequence in normed star rings is stable exactly when the
  sequence of its stars is.

## References

* A. Böttcher and B. Silbermann, *Introduction to Large Truncated Toeplitz Matrices*,
  Section 1.4, for stability of approximating sequences.
* R. Hagen, S. Roch and B. Silbermann, *C*-Algebras and Numerical Analysis*, Section 1.2.
-/

public section

open Filter

namespace TauCeti

section ConditionNumber

variable {R : Type*} [NormedRing R]

/-- The condition number `‖a‖ ‖a⁻¹‖` of an element of a normed ring. Since `Ring.inverse` sends
non-units to zero, a non-unit has condition number `0`. -/
noncomputable def conditionNumber (a : R) : ℝ :=
  ‖a‖ * ‖Ring.inverse a‖

theorem conditionNumber_def (a : R) : conditionNumber a = ‖a‖ * ‖Ring.inverse a‖ := (rfl)

theorem conditionNumber_nonneg (a : R) : 0 ≤ conditionNumber a :=
  mul_nonneg (norm_nonneg _) (norm_nonneg _)

@[simp]
theorem conditionNumber_of_not_isUnit {a : R} (ha : ¬IsUnit a) : conditionNumber a = 0 := by
  simp [conditionNumber, Ring.inverse_non_unit a ha]

@[simp]
theorem conditionNumber_one [NormOneClass R] : conditionNumber (1 : R) = 1 := by
  simp [conditionNumber]

/-- A unit of a normed ring with `‖1‖ = 1` has condition number at least one. -/
theorem one_le_conditionNumber [NormOneClass R] {a : R} (ha : IsUnit a) :
    1 ≤ conditionNumber a := by
  calc
    (1 : ℝ) = ‖a * Ring.inverse a‖ := by rw [Ring.mul_inverse_cancel a ha, norm_one]
    _ ≤ conditionNumber a := norm_mul_le _ _

end ConditionNumber

section StableSequence

variable {R : ℕ → Type*} [∀ n, NormedRing (R n)]

/-- A sequence `aₙ` in normed rings is *stable* when, for all sufficiently large `n`, `aₙ` is
invertible and the norms `‖aₙ⁻¹‖` are bounded uniformly in `n`. -/
def IsStableSequence (a : ∀ n, R n) : Prop :=
  ∃ M : ℝ, ∀ᶠ n in atTop, IsUnit (a n) ∧ ‖Ring.inverse (a n)‖ ≤ M

theorem isStableSequence_def (a : ∀ n, R n) :
    IsStableSequence a ↔ ∃ M : ℝ, ∀ᶠ n in atTop, IsUnit (a n) ∧ ‖Ring.inverse (a n)‖ ≤ M :=
  (Iff.rfl)

/-- The members of a stable sequence are eventually invertible. -/
theorem IsStableSequence.eventually_isUnit {a : ∀ n, R n} (ha : IsStableSequence a) :
    ∀ᶠ n in atTop, IsUnit (a n) := by
  obtain ⟨M, hM⟩ := ha
  exact hM.mono fun _ h ↦ h.1

/-- A stable sequence whose norms are eventually bounded has eventually bounded condition
numbers. -/
theorem IsStableSequence.exists_conditionNumber_le {a : ∀ n, R n} (ha : IsStableSequence a)
    {C : ℝ} (hC : ∀ᶠ n in atTop, ‖a n‖ ≤ C) :
    ∃ K : ℝ, ∀ᶠ n in atTop, conditionNumber (a n) ≤ K := by
  obtain ⟨M, hM⟩ := ha
  refine ⟨C * M, (hM.and hC).mono fun n ⟨⟨_, hn⟩, hCn⟩ ↦ ?_⟩
  exact mul_le_mul hCn hn (norm_nonneg _) ((norm_nonneg _).trans hCn)

/-- A sequence in normed star rings is stable exactly when the sequence of its stars is. -/
@[simp]
theorem isStableSequence_star_iff [∀ n, StarRing (R n)] [∀ n, NormedStarGroup (R n)]
    {a : ∀ n, R n} : IsStableSequence (fun n ↦ star (a n)) ↔ IsStableSequence a := by
  simp only [IsStableSequence, isUnit_star, Ring.inverse_star, norm_star]

end StableSequence

end TauCeti

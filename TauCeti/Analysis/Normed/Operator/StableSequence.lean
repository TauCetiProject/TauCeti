/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Stable sequences, condition numbers and inverse bounds

A sequence `aₙ` of elements of normed rings is *stable* (`TauCeti.IsStableSequence`) when its
members are eventually invertible and their inverses are uniformly bounded in norm. This is the
notion that governs approximation methods such as the finite-section method: a stable sequence of
approximating matrices has uniformly bounded condition numbers
`κ(aₙ) = ‖aₙ‖ ‖aₙ⁻¹‖` (`TauCeti.conditionNumber`) as soon as its norms are bounded.

Stability is invariant under `star`. For a sequence of bounded operators, stability is
equivalent to an eventual uniform lower bound `‖x‖ ≤ M ‖Aₙ x‖` when every space is
finite-dimensional.

## Main definitions

* `TauCeti.conditionNumber a`: the condition number `‖a‖ ‖a⁻¹‖`, with value `0` at a non-unit.
* `TauCeti.IsStableSequence a`: eventual invertibility with uniformly bounded inverse norms.

## Main results

* `TauCeti.one_le_conditionNumber`: units have condition number at least one.
* `TauCeti.IsStableSequence.exists_conditionNumber_le`: a bounded stable sequence has uniformly
  bounded condition numbers.
* `TauCeti.isStableSequence_iff_exists_forall_norm_le`: for operators on finite-dimensional
  spaces, stability is an eventual uniform lower bound.
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
theorem isStableSequence_star_iff [∀ n, StarRing (R n)] [∀ n, NormedStarGroup (R n)]
    {a : ∀ n, R n} : IsStableSequence (fun n ↦ star (a n)) ↔ IsStableSequence a := by
  simp only [IsStableSequence, isUnit_star, Ring.inverse_star, norm_star]

end StableSequence

section Operator

variable {𝕜 : Type*} {E : ℕ → Type*} [NontriviallyNormedField 𝕜]
  [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace 𝕜 (E n)]

/-- The members of a stable sequence of operators are eventually uniformly bounded below. -/
theorem IsStableSequence.exists_forall_norm_le {A : ∀ n, E n →L[𝕜] E n}
    (hA : IsStableSequence A) : ∃ M : ℝ, ∀ᶠ n in atTop, ∀ x, ‖x‖ ≤ M * ‖A n x‖ := by
  obtain ⟨M, hM⟩ := hA
  refine ⟨M, hM.mono fun n ⟨hu, hn⟩ x ↦ ?_⟩
  exact (ContinuousLinearMap.norm_le_norm_ringInverse_mul_norm_apply hu x).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

/-- A sequence of operators on finite-dimensional spaces is stable exactly when its members are
eventually uniformly bounded below. -/
theorem isStableSequence_iff_exists_forall_norm_le [∀ n, FiniteDimensional 𝕜 (E n)]
    {A : ∀ n, E n →L[𝕜] E n} :
    IsStableSequence A ↔ ∃ M : ℝ, ∀ᶠ n in atTop, ∀ x, ‖x‖ ≤ M * ‖A n x‖ := by
  refine ⟨IsStableSequence.exists_forall_norm_le, fun ⟨M, hM⟩ ↦ ⟨max M 0, hM.mono fun n h ↦ ?_⟩⟩
  have h' : ∀ x, ‖x‖ ≤ max M 0 * ‖A n x‖ := fun x ↦
    (h x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hinj : Function.Injective (A n) := by
    refine (injective_iff_map_eq_zero (A n)).mpr fun x hx ↦ norm_le_zero_iff.mp ?_
    simpa [hx] using h' x
  -- The lower bound makes the algebraic inverse continuous, so no completeness is needed.
  let e : E n ≃ₗ[𝕜] E n := LinearEquiv.ofBijective (A n : E n →ₗ[𝕜] E n)
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  let e' : E n ≃L[𝕜] E n := e.toContinuousLinearEquivOfBounds ‖A n‖ (max M 0) (A n).le_opNorm
    fun y ↦ (h' (e.symm y)).trans_eq (by rw [show A n (e.symm y) = y from e.apply_symm_apply y])
  have hunit : IsUnit (A n) := ⟨(ContinuousLinearEquiv.unitsEquiv 𝕜 (E n)).symm e', rfl⟩
  exact ⟨hunit, ContinuousLinearMap.norm_ringInverse_le_of_forall_norm_le hunit
    (le_max_right _ _) h'⟩

end Operator

end TauCeti

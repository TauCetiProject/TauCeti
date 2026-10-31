/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import TauCeti.Analysis.Normed.Operator.Basic
public import TauCeti.Analysis.Normed.Ring.StableSequence

/-!
# Stable sequences of operators

A sequence of bounded operators `Aₙ` is stable (`TauCeti.IsStableSequence`) when its members are
eventually invertible with uniformly bounded inverse norms. A stable sequence of operators is
eventually uniformly bounded below, `‖x‖ ≤ M ‖Aₙ x‖`, and when every space is finite-dimensional
this lower bound is equivalent to stability.

## Main results

* `TauCeti.IsStableSequence.exists_forall_norm_le`: a stable sequence of operators is eventually
  uniformly bounded below.
* `TauCeti.isStableSequence_iff_exists_forall_norm_le`: for operators on finite-dimensional
  spaces, stability is an eventual uniform lower bound.

## References

* A. Böttcher and B. Silbermann, *Introduction to Large Truncated Toeplitz Matrices*,
  Section 1.4, for stability of approximating sequences.
-/

public section

open Filter

namespace TauCeti

section Operator

variable {𝕜 : Type*} {E : ℕ → Type*} [NontriviallyNormedField 𝕜]
  [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace 𝕜 (E n)]

/-- The members of a stable sequence of operators are eventually uniformly bounded below. -/
theorem IsStableSequence.exists_forall_norm_le {A : ∀ n, E n →L[𝕜] E n}
    (hA : IsStableSequence A) : ∃ M : ℝ, ∀ᶠ n in atTop, ∀ x, ‖x‖ ≤ M * ‖A n x‖ := by
  obtain ⟨M, hM⟩ := (isStableSequence_def _).mp hA
  refine ⟨M, hM.mono fun n ⟨hu, hn⟩ x ↦ ?_⟩
  exact (ContinuousLinearMap.norm_le_norm_ringInverse_mul_norm_apply hu x).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

/-- A sequence of operators on finite-dimensional spaces is stable exactly when its members are
eventually uniformly bounded below. -/
theorem isStableSequence_iff_exists_forall_norm_le [∀ n, FiniteDimensional 𝕜 (E n)]
    {A : ∀ n, E n →L[𝕜] E n} :
    IsStableSequence A ↔ ∃ M : ℝ, ∀ᶠ n in atTop, ∀ x, ‖x‖ ≤ M * ‖A n x‖ := by
  refine ⟨IsStableSequence.exists_forall_norm_le, fun ⟨M, hM⟩ ↦
    (isStableSequence_def _).mpr ⟨max M 0, hM.mono fun n h ↦ ?_⟩⟩
  have h' : ∀ x, ‖x‖ ≤ max M 0 * ‖A n x‖ := fun x ↦
    (h x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hinj : Function.Injective (A n) := ContinuousLinearMap.injective_of_forall_norm_le h'
  -- The lower bound makes the algebraic inverse continuous, so no completeness is needed.
  let e : E n ≃ₗ[𝕜] E n := LinearEquiv.ofBijective (A n : E n →ₗ[𝕜] E n)
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  have he : ∀ x, e x = A n x := fun x ↦ LinearEquiv.ofBijective_apply _ x
  let e' : E n ≃L[𝕜] E n := e.toContinuousLinearEquivOfBounds ‖A n‖ (max M 0) (A n).le_opNorm
    fun y ↦ (h' (e.symm y)).trans_eq (by rw [← he, e.apply_symm_apply])
  have hunit : IsUnit (A n) := ⟨(ContinuousLinearEquiv.unitsEquiv 𝕜 (E n)).symm e', rfl⟩
  exact ⟨hunit, ContinuousLinearMap.norm_ringInverse_le_of_forall_norm_le hunit
    (le_max_right _ _) h'⟩

end Operator

end TauCeti

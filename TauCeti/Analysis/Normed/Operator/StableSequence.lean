/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Stable sequences, condition numbers and inverse bounds

A sequence `aₙ` of elements of normed rings is *stable* (`TauCeti.IsStableSequence`) when its
members are eventually invertible and their inverses are uniformly bounded in norm. This is the
notion that governs approximation methods such as the finite-section method: a stable sequence of
approximating matrices has uniformly bounded condition numbers
`κ(aₙ) = ‖aₙ‖ ‖aₙ⁻¹‖` (`TauCeti.conditionNumber`) as soon as its norms are bounded.

For a sequence of bounded operators, stability is equivalent to an eventual uniform lower bound
`‖x‖ ≤ M ‖Aₙ x‖` when every space is finite-dimensional, and it passes to the adjoint sequence
on Hilbert spaces. For a single operator on a Hilbert space, a lower bound `‖x‖ ≤ M ‖T x‖`
together with injectivity of the adjoint gives invertibility with `‖T⁻¹‖ ≤ M`.

## Main definitions

* `TauCeti.conditionNumber a`: the condition number `‖a‖ ‖a⁻¹‖`, with value `0` at a non-unit.
* `TauCeti.IsStableSequence a`: eventual invertibility with uniformly bounded inverse norms.

## Main results

* `TauCeti.one_le_conditionNumber`: units have condition number at least one.
* `TauCeti.IsStableSequence.exists_conditionNumber_le`: a bounded stable sequence has uniformly
  bounded condition numbers.
* `TauCeti.isStableSequence_iff_exists_forall_norm_le`: for operators on finite-dimensional
  spaces, stability is an eventual uniform lower bound.
* `ContinuousLinearMap.ringInverse_adjoint`: inversion commutes with the adjoint.
* `TauCeti.isStableSequence_adjoint_iff`: a sequence of Hilbert-space operators is stable exactly
  when the sequence of its adjoints is.
* `ContinuousLinearMap.isUnit_and_norm_ringInverse_le_of_forall_norm_le`: an operator on a Hilbert
  space that is bounded below by `M⁻¹` and has injective adjoint is invertible with `‖T⁻¹‖ ≤ M`.

## References

* A. Böttcher and B. Silbermann, *Introduction to Large Truncated Toeplitz Matrices*,
  Section 1.4, for stability of approximating sequences.
* R. Hagen, S. Roch and B. Silbermann, *C*-Algebras and Numerical Analysis*, Section 1.2.
-/

public section

open Filter

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- An invertible operator is bounded below by the reciprocal of the norm of its inverse. -/
theorem norm_le_norm_ringInverse_mul_norm_apply {A : E →L[𝕜] E} (hA : IsUnit A) (x : E) :
    ‖x‖ ≤ ‖Ring.inverse A‖ * ‖A x‖ := by
  calc
    ‖x‖ = ‖Ring.inverse A (A x)‖ := by
      rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel A hA, one_apply_eq_self]
    _ ≤ ‖Ring.inverse A‖ * ‖A x‖ := le_opNorm _ _

/-- An invertible operator bounded below by `M⁻¹` has an inverse of norm at most `M`. -/
theorem norm_ringInverse_le_of_forall_norm_le {A : E →L[𝕜] E} (hA : IsUnit A) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ x, ‖x‖ ≤ M * ‖A x‖) : ‖Ring.inverse A‖ ≤ M := by
  refine opNorm_le_bound _ hM fun y ↦ ?_
  have hy := h (Ring.inverse A y)
  rwa [← mul_apply_eq_comp, Ring.mul_inverse_cancel A hA, one_apply_eq_self] at hy

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- An operator on a Hilbert space that is bounded below by `M⁻¹` and whose adjoint is injective
is invertible, and its inverse has norm at most `M`. -/
theorem isUnit_and_norm_ringInverse_le_of_forall_norm_le {T : E →L[𝕜] E} {M : ℝ} (hM : 0 ≤ M)
    (hT : ∀ x, ‖x‖ ≤ M * ‖T x‖) (hT' : Function.Injective (adjoint T)) :
    IsUnit T ∧ ‖Ring.inverse T‖ ≤ M := by
  have hinj : Function.Injective T := by
    refine (injective_iff_map_eq_zero T).mpr fun x hx ↦ norm_le_zero_iff.mp ?_
    simpa [hx] using hT x
  have hanti : AntilipschitzWith (Real.toNNReal M) T :=
    AddMonoidHomClass.antilipschitz_of_bound T fun x ↦ by
      simpa [Real.coe_toNNReal _ hM] using hT x
  have hclosed : IsClosed (T.range : Set E) := by
    rw [LinearMap.coe_range]
    exact hanti.isClosed_range T.uniformContinuous
  have : CompleteSpace T.range := hclosed.completeSpace_coe
  have hrange : T.range = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff, orthogonal_range, LinearMap.ker_eq_bot]
    exact hT'
  have hunit : IsUnit T := isUnit_iff_bijective.mpr ⟨hinj, LinearMap.range_eq_top.mp hrange⟩
  exact ⟨hunit, norm_ringInverse_le_of_forall_norm_le hunit hM hT⟩

/-- The adjoint of an operator on a Hilbert space is invertible exactly when the operator is. -/
@[simp]
theorem isUnit_adjoint_iff {A : E →L[𝕜] E} : IsUnit (adjoint A) ↔ IsUnit A := by
  simpa only [star_eq_adjoint] using isUnit_star (a := A)

/-- Inversion commutes with the adjoint. -/
theorem ringInverse_adjoint (A : E →L[𝕜] E) :
    Ring.inverse (adjoint A) = adjoint (Ring.inverse A) := by
  simpa only [star_eq_adjoint] using Ring.inverse_star A

end ContinuousLinearMap

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
theorem isStableSequence_iff_exists_forall_norm_le [CompleteSpace 𝕜]
    [∀ n, FiniteDimensional 𝕜 (E n)] {A : ∀ n, E n →L[𝕜] E n} :
    IsStableSequence A ↔ ∃ M : ℝ, ∀ᶠ n in atTop, ∀ x, ‖x‖ ≤ M * ‖A n x‖ := by
  refine ⟨IsStableSequence.exists_forall_norm_le, fun ⟨M, hM⟩ ↦ ⟨max M 0, hM.mono fun n h ↦ ?_⟩⟩
  have h' : ∀ x, ‖x‖ ≤ max M 0 * ‖A n x‖ := fun x ↦
    (h x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hinj : Function.Injective (A n) := by
    refine (injective_iff_map_eq_zero (A n)).mpr fun x hx ↦ norm_le_zero_iff.mp ?_
    simpa [hx] using h' x
  have : CompleteSpace (E n) := FiniteDimensional.complete 𝕜 (E n)
  have hunit : IsUnit (A n) :=
    ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.mpr <| (Module.End.isUnit_iff _).mpr
      ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  exact ⟨hunit, ContinuousLinearMap.norm_ringInverse_le_of_forall_norm_le hunit
    (le_max_right _ _) h'⟩

end Operator

section Adjoint

variable {𝕜 : Type*} {E : ℕ → Type*} [RCLike 𝕜] [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace 𝕜 (E n)] [∀ n, CompleteSpace (E n)]

/-- A sequence of Hilbert-space operators is stable exactly when the sequence of its adjoints
is. -/
theorem isStableSequence_adjoint_iff {A : ∀ n, E n →L[𝕜] E n} :
    IsStableSequence (fun n ↦ ContinuousLinearMap.adjoint (A n)) ↔ IsStableSequence A := by
  simp only [IsStableSequence, ContinuousLinearMap.isUnit_adjoint_iff,
    ContinuousLinearMap.ringInverse_adjoint, LinearIsometryEquiv.norm_map]

end Adjoint

end TauCeti

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
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

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
* `TauCeti.isStableSequence_continuousLinearEquiv_comp_iff`: stability is invariant under
  uniformly bounded invertible coordinate changes with uniformly bounded inverses.
* `TauCeti.conditionNumber_linearIsometryEquiv_comp` and
  `TauCeti.isStableSequence_linearIsometryEquiv_comp_iff`: isometric equivalences preserve
  operator condition numbers and sequence stability.

## References

* A. Böttcher, *C\*-Algebras in Numerical Analysis*, Irish Math. Soc. Bull. 45 (2000), 57–101,
  Sections 1 and 7.
* A. Böttcher and B. Silbermann, *Introduction to Large Truncated Toeplitz Matrices*,
  Section 1.4, for stability of approximating sequences.
-/

public section

open Filter

namespace TauCeti

section Operator

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

section Single

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

private theorem isUnit_continuousLinearEquiv_comp_iff (e₁ : F ≃L[𝕜] E) (e₂ : E ≃L[𝕜] F)
    (T : E →L[𝕜] E) :
    IsUnit ((e₂ : E →L[𝕜] F) ∘L T ∘L (e₁ : F →L[𝕜] E)) ↔ IsUnit T := by
  simp [← ContinuousLinearMap.isInvertible_iff_isUnit]

private theorem ringInverse_continuousLinearEquiv_comp (e₁ : F ≃L[𝕜] E) (e₂ : E ≃L[𝕜] F)
    (T : E →L[𝕜] E) :
    Ring.inverse ((e₂ : E →L[𝕜] F) ∘L T ∘L (e₁ : F →L[𝕜] E)) =
      (e₁.symm : E →L[𝕜] F) ∘L Ring.inverse T ∘L (e₂.symm : F →L[𝕜] E) := by
  simp [ContinuousLinearMap.ringInverse_eq_inverse, ContinuousLinearMap.comp_assoc]

private theorem norm_coe_linearIsometryEquiv_le (e : E ≃ₗᵢ[𝕜] F) :
    ‖(e : E →L[𝕜] F)‖ ≤ 1 := by
  rw [← e.toContinuousLinearMap_toLinearIsometry]
  exact e.toLinearIsometry.norm_toContinuousLinearMap_le

/-- Transporting an operator on both sides by linear isometric equivalences preserves its condition
number. -/
@[simp]
theorem conditionNumber_linearIsometryEquiv_comp (e₁ : F ≃ₗᵢ[𝕜] E) (e₂ : E ≃ₗᵢ[𝕜] F)
    (T : E →L[𝕜] E) :
    conditionNumber ((e₂ : E →L[𝕜] F) ∘L T ∘L (e₁ : F →L[𝕜] E)) = conditionNumber T := by
  -- `(e : E →L[𝕜] F)` is `((e : E ≃L[𝕜] F) : E →L[𝕜] F)` syntactically via
  -- `instCoeTCContinuousLinearMap`.
  rw [conditionNumber_def,
    ringInverse_continuousLinearEquiv_comp (e₁ : F ≃L[𝕜] E) (e₂ : E ≃L[𝕜] F) T,
    ← e₁.toContinuousLinearEquiv_symm, ← e₂.toContinuousLinearEquiv_symm, conditionNumber_def]
  simp only [ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

end Single

variable {E F : ℕ → Type*}
  [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace 𝕜 (E n)]
  [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace 𝕜 (F n)]

/-- The members of a stable sequence of operators are eventually uniformly bounded below. -/
theorem IsStableSequence.exists_forall_norm_le {A : ∀ n, E n →L[𝕜] E n}
    (hA : IsStableSequence A) : ∃ M : ℝ, ∀ᶠ n in atTop, ∀ x, ‖x‖ ≤ M * ‖A n x‖ := by
  obtain ⟨M, hM⟩ := (isStableSequence_def _).mp hA
  refine ⟨M, hM.mono fun n ⟨hu, hn⟩ x ↦ ?_⟩
  have hx := (ContinuousLinearMap.isInvertible_iff_isUnit.mpr hu).norm_le_norm_inverse_mul_norm x
  rw [← ContinuousLinearMap.ringInverse_eq_inverse] at hx
  exact hx.trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

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
  obtain ⟨e', he'⟩ := ContinuousLinearMap.isInvertible_of_surjective_of_forall_norm_le
    (LinearMap.injective_iff_surjective.mp hinj) h'
  have hunit : IsUnit (A n) := ⟨(ContinuousLinearEquiv.unitsEquiv 𝕜 (E n)).symm e', he'⟩
  exact ⟨hunit, ContinuousLinearMap.norm_ringInverse_le_of_forall_norm_le
    (le_max_right _ _) h'⟩

/-- Stability of an operator sequence passes across two-sided continuous linear equivalences when
the norms entering the inverse `e₁⁻¹ ∘ A⁻¹ ∘ e₂⁻¹` are eventually bounded. -/
theorem IsStableSequence.continuousLinearEquiv_comp {e₁ : ∀ n, F n ≃L[𝕜] E n}
    {e₂ : ∀ n, E n ≃L[𝕜] F n} {A : ∀ n, E n →L[𝕜] E n} (hA : IsStableSequence A)
    (he₁ : ∃ C₁ : ℝ, ∀ᶠ n in atTop, ‖((e₁ n).symm : E n →L[𝕜] F n)‖ ≤ C₁)
    (he₂ : ∃ C₂ : ℝ, ∀ᶠ n in atTop, ‖((e₂ n).symm : F n →L[𝕜] E n)‖ ≤ C₂) :
    IsStableSequence (fun n ↦ (e₂ n : E n →L[𝕜] F n) ∘L A n ∘L (e₁ n : F n →L[𝕜] E n)) := by
  obtain ⟨M, hM⟩ := (isStableSequence_def _).mp hA
  obtain ⟨C₁, hC₁⟩ := he₁
  obtain ⟨C₂, hC₂⟩ := he₂
  refine (isStableSequence_def _).mpr
    ⟨C₁ * max M 0 * C₂, (hM.and (hC₁.and hC₂)).mono fun n ⟨⟨hu, hn⟩, hn₁, hn₂⟩ ↦
      ⟨(isUnit_continuousLinearEquiv_comp_iff (e₁ n) (e₂ n) (A n)).mpr hu, ?_⟩⟩
  rw [ringInverse_continuousLinearEquiv_comp]
  have hM0 : ‖Ring.inverse (A n)‖ ≤ max M 0 := hn.trans (le_max_left _ _)
  have hC₁0 : 0 ≤ C₁ := (norm_nonneg _).trans hn₁
  refine (ContinuousLinearMap.opNorm_comp_comp_le _ _ _).trans ?_
  exact mul_le_mul (mul_le_mul hn₁ hM0 (norm_nonneg _) hC₁0) hn₂ (norm_nonneg _)
    (mul_nonneg hC₁0 (le_max_right _ _))

/-- Uniformly bounded invertible coordinate changes with uniformly bounded inverses preserve
stability of operator sequences. -/
theorem isStableSequence_continuousLinearEquiv_comp_iff {e₁ : ∀ n, F n ≃L[𝕜] E n}
    {e₂ : ∀ n, E n ≃L[𝕜] F n} {A : ∀ n, E n →L[𝕜] E n}
    (he₁ : ∃ C₁ : ℝ, ∀ᶠ n in atTop, ‖(e₁ n : F n →L[𝕜] E n)‖ ≤ C₁)
    (he₁' : ∃ C₁' : ℝ, ∀ᶠ n in atTop, ‖((e₁ n).symm : E n →L[𝕜] F n)‖ ≤ C₁')
    (he₂ : ∃ C₂ : ℝ, ∀ᶠ n in atTop, ‖(e₂ n : E n →L[𝕜] F n)‖ ≤ C₂)
    (he₂' : ∃ C₂' : ℝ, ∀ᶠ n in atTop, ‖((e₂ n).symm : F n →L[𝕜] E n)‖ ≤ C₂') :
    IsStableSequence (fun n ↦ (e₂ n : E n →L[𝕜] F n) ∘L A n ∘L (e₁ n : F n →L[𝕜] E n)) ↔
      IsStableSequence A := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.continuousLinearEquiv_comp he₁' he₂'⟩
  have h' := h.continuousLinearEquiv_comp (e₁ := fun n ↦ (e₁ n).symm)
    (e₂ := fun n ↦ (e₂ n).symm) he₁ he₂
  refine h'.congr (Eventually.of_forall fun n ↦ ?_)
  ext x
  simp

/-- Transporting a sequence of operators on both sides by linear isometric equivalences preserves
stability. -/
@[simp]
theorem isStableSequence_linearIsometryEquiv_comp_iff
    (e₁ : ∀ n, F n ≃ₗᵢ[𝕜] E n) (e₂ : ∀ n, E n ≃ₗᵢ[𝕜] F n) {A : ∀ n, E n →L[𝕜] E n} :
    IsStableSequence (fun n ↦ (e₂ n : E n →L[𝕜] F n) ∘L A n ∘L (e₁ n : F n →L[𝕜] E n)) ↔
      IsStableSequence A :=
  -- `(e : E →L[𝕜] F)` is `((e : E ≃L[𝕜] F) : E →L[𝕜] F)` syntactically via
  -- `instCoeTCContinuousLinearMap`.
  isStableSequence_continuousLinearEquiv_comp_iff
    (e₁ := fun n ↦ (e₁ n : F n ≃L[𝕜] E n))
    (e₂ := fun n ↦ (e₂ n : E n ≃L[𝕜] F n))
    ⟨1, Eventually.of_forall fun n ↦ norm_coe_linearIsometryEquiv_le (e₁ n)⟩
    ⟨1, Eventually.of_forall fun n ↦ by
      rw [← (e₁ n).toContinuousLinearEquiv_symm]
      exact norm_coe_linearIsometryEquiv_le (e₁ n).symm⟩
    ⟨1, Eventually.of_forall fun n ↦ norm_coe_linearIsometryEquiv_le (e₂ n)⟩
    ⟨1, Eventually.of_forall fun n ↦ by
      rw [← (e₂ n).toContinuousLinearEquiv_symm]
      exact norm_coe_linearIsometryEquiv_le (e₂ n).symm⟩

end Operator

end TauCeti

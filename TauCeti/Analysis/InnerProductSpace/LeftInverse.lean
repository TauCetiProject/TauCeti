/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse

/-!
# Smooth Gram left inverses

For an operator between real or complex Hilbert spaces with invertible Gram operator,
`gramLeftInverse A = (A† A)⁻¹ A†` is a left inverse. An injective operator out of a
finite-dimensional space has invertible Gram operator. Over the reals, the Gram left inverse
depends smoothly on the operator wherever its Gram operator is invertible.

For an injective differential `A` in local orthonormal frames, the normal representative
is `v ↦ v - A (gramLeftInverse A v)`. Cancellation makes this expression invariant under
adding `A u` to `v`. Its identification with orthogonal projection is developed in
`TauCeti.Analysis.InnerProductSpace.RangeProjection`.
-/

public section

open Function
open scoped ContDiff

noncomputable section

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The Gram operator `A† A` of an operator out of a finite-dimensional space is invertible
exactly when the operator is injective. -/
theorem isUnit_adjoint_comp_self_iff [FiniteDimensional 𝕜 E] (A : E →L[𝕜] F) :
    IsUnit (adjoint A ∘L A) ↔ Injective A := by
  simp only [isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot,
    ker_adjoint_comp_self, LinearMap.ker_eq_bot, coe_coe]

/-- The Gram left inverse `(A† A)⁻¹ A†`. It is zero when the Gram operator is not invertible,
in particular when `A` is not injective. -/
def gramLeftInverse (A : E →L[𝕜] F) : F →L[𝕜] E :=
  Ring.inverse (adjoint A ∘L A) ∘L adjoint A

/-- The defining Gram formula for the left inverse. -/
theorem gramLeftInverse_def (A : E →L[𝕜] F) :
    gramLeftInverse A = Ring.inverse (adjoint A ∘L A) ∘L adjoint A := (rfl)

/-- A noninvertible Gram operator gives the zero Gram left inverse. -/
theorem gramLeftInverse_of_not_isUnit {A : E →L[𝕜] F}
    (hA : ¬IsUnit (adjoint A ∘L A)) : gramLeftInverse A = 0 := by
  rw [gramLeftInverse_def, Ring.inverse_non_unit _ hA, zero_comp]

/-- A noninjective operator has zero Gram left inverse. -/
theorem gramLeftInverse_of_not_injective {A : E →L[𝕜] F} (hA : ¬Injective A) :
    gramLeftInverse A = 0 := by
  apply gramLeftInverse_of_not_isUnit
  intro h
  apply hA
  rw [← coe_coe, ← LinearMap.ker_eq_bot, ← ker_adjoint_comp_self]
  exact LinearMap.ker_eq_bot.mpr (isUnit_iff_bijective.mp h).injective

@[simp]
theorem gramLeftInverse_zero : gramLeftInverse (0 : E →L[𝕜] F) = 0 := by
  simp [gramLeftInverse_def]

/-- The Gram left inverse cancels an operator with invertible Gram operator. -/
@[simp]
theorem gramLeftInverse_comp_self {A : E →L[𝕜] F} (hA : IsUnit (adjoint A ∘L A)) :
    gramLeftInverse A ∘L A = .id 𝕜 E := by
  rw [gramLeftInverse_def, comp_assoc, ← mul_def, ← one_def]
  exact Ring.inverse_mul_cancel _ hA

/-- Applying the Gram left inverse recovers the original vector. -/
@[simp]
theorem gramLeftInverse_apply_self {A : E →L[𝕜] F} (hA : IsUnit (adjoint A ∘L A)) (v : E) :
    gramLeftInverse A (A v) = v := by
  simpa only [comp_apply, id_apply] using DFunLike.congr_fun (gramLeftInverse_comp_self hA) v

/-- The Gram left inverse vanishes on the orthogonal complement of the range. -/
theorem gramLeftInverse_apply_of_mem_orthogonal {A : E →L[𝕜] F} {v : F}
    (hv : v ∈ A.rangeᗮ) : gramLeftInverse A v = 0 := by
  rw [orthogonal_range, LinearMap.mem_ker, coe_coe] at hv
  simp only [gramLeftInverse_def, comp_apply, hv, map_zero]

/-- When the Gram operator is invertible, the kernel of its left inverse is the normal space. -/
@[simp]
theorem ker_gramLeftInverse {A : E →L[𝕜] F} (hA : IsUnit (adjoint A ∘L A)) :
    (gramLeftInverse A).ker = A.rangeᗮ := by
  ext v
  refine ⟨fun hv ↦ ?_, gramLeftInverse_apply_of_mem_orthogonal⟩
  rw [orthogonal_range, LinearMap.mem_ker]
  have hv' : Ring.inverse (adjoint A ∘L A) (adjoint A v) = 0 := by
    simpa only [LinearMap.mem_ker, coe_coe, gramLeftInverse_def, comp_apply] using hv
  have hG := DFunLike.congr_fun (Ring.mul_inverse_cancel _ hA) (adjoint A v)
  simpa only [mul_def, comp_apply, hv', map_zero, one_apply_eq_self, coe_coe] using hG.symm

/-- The Gram inverse of a bijective operator is injective. -/
theorem gramLeftInverse_injective {A : E →L[𝕜] F} (hA : Bijective A) :
    Injective (gramLeftInverse A) := by
  let e := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hA.injective) (LinearMap.range_eq_top.mpr hA.surjective)
  have hadj : Surjective (adjoint A) := by
    have h : adjoint A ∘L adjoint (e.symm : F →L[𝕜] E) = 1 := by
      rw [← adjoint_comp]
      have he : (e.symm : F →L[𝕜] E) ∘L A = 1 := by ext x; simp [e]
      rw [he, adjoint_one]
    have hright : RightInverse (adjoint (e.symm : F →L[𝕜] E)) (adjoint A) := fun x ↦ by
      simpa only [comp_apply, one_apply_eq_self] using DFunLike.congr_fun h x
    exact hright.surjective
  have hG : IsUnit (adjoint A ∘L A) := isUnit_iff_bijective.mpr
    ⟨by simpa only [coe_comp] using (A.adjoint_comp_self_injective_iff.mpr hA.injective),
      hadj.comp hA.surjective⟩
  have hleft : LeftInverse (gramLeftInverse A) A := gramLeftInverse_apply_self hG
  exact (hleft.rightInverse_of_surjective hA.surjective).injective

/-- The Gram left inverse depends continuously on an operator with invertible Gram operator. -/
theorem continuousAt_gramLeftInverse {A : E →L[𝕜] F} (hA : IsUnit (adjoint A ∘L A)) :
    ContinuousAt (gramLeftInverse : (E →L[𝕜] F) → F →L[𝕜] E) A := by
  have ha : ContinuousAt (adjoint : (E →L[𝕜] F) → F →L[𝕜] E) A :=
    adjoint.continuous.continuousAt
  have hi := NormedRing.inverse_continuousAt hA.unit
  rw [hA.unit_spec] at hi
  exact (hi.comp (f := fun B : E →L[𝕜] F ↦ adjoint B ∘L B)
    (ha.clm_comp continuousAt_id)).clm_comp ha

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The Gram left inverse depends smoothly on an operator with invertible Gram operator. -/
theorem contDiffAt_gramLeftInverse {A : E →L[ℝ] F} (hA : IsUnit (adjoint A ∘L A)) {n : ℕ∞ω} :
    ContDiffAt ℝ n (gramLeftInverse : (E →L[ℝ] F) → F →L[ℝ] E) A := by
  have ha : ContDiff ℝ n (adjoint : (E →L[ℝ] F) → F →L[ℝ] E) :=
    (adjoint : (E →L[ℝ] F) ≃ₗᵢ[ℝ] (F →L[ℝ] E)).contDiff
  exact ((ha.contDiffAt.clm_comp contDiffAt_id).inverse hA).clm_comp ha.contDiffAt

end ContinuousLinearMap

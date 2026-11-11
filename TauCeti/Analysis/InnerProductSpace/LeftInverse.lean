/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.RangeProjection

/-!
# Smooth left inverses of injective operators

For an injective operator out of a finite-dimensional real inner product space, its Gram
operator is invertible. The Gram inverse composed with the adjoint is an actual left inverse,
and depends smoothly on the operator throughout the injective locus. This construction is
useful for the tangent-coordinate projection of secants of an immersed manifold.
-/

public section

open Function
open scoped ContDiff
noncomputable section
namespace ContinuousLinearMap
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
/-- The Gram formula for the left inverse, with the native inverse junk value off its domain. -/
def gramLeftInverse (A : E →L[ℝ] F) : F →L[ℝ] E :=
  Ring.inverse (adjoint A ∘L A) ∘L adjoint A

/-- The Gram left inverse cancels every injective operator from a finite-dimensional space. -/
theorem gramLeftInverse_comp {A : E →L[ℝ] F} (hA : Injective A) :
    gramLeftInverse A ∘L A = 1 := by
  unfold gramLeftInverse
  rw [ContinuousLinearMap.comp_assoc]
  exact Ring.inverse_mul_cancel _ ((isUnit_adjoint_comp_self_iff A).mpr hA)

/-- Applying the Gram left inverse recovers the original vector. -/
theorem gramLeftInverse_apply {A : E →L[ℝ] F} (hA : Injective A) (v : E) :
    gramLeftInverse A (A v) = v := by
  exact congrArg (fun L : E →L[ℝ] E ↦ L v) (gramLeftInverse_comp hA)

/-- The Gram inverse of a bijective operator is injective. -/
theorem gramLeftInverse_injective {A : E →L[ℝ] F} (hA : Bijective A) :
    Injective (gramLeftInverse A) := by
  intro v w h
  obtain ⟨x, rfl⟩ := hA.surjective v
  obtain ⟨y, rfl⟩ := hA.surjective w
  rw [gramLeftInverse_apply hA.injective, gramLeftInverse_apply hA.injective] at h
  exact congrArg A h

/-- The Gram left inverse depends smoothly on the operator at every injective operator. -/
theorem contDiffAt_gramLeftInverse {A : E →L[ℝ] F} (hA : Injective A) {n : ℕ∞ω} :
    ContDiffAt ℝ n (gramLeftInverse : (E →L[ℝ] F) → F →L[ℝ] E) A := by
  have ha : ContDiff ℝ n (adjoint : (E →L[ℝ] F) → F →L[ℝ] E) :=
    (adjoint : (E →L[ℝ] F) ≃ₗᵢ[ℝ] (F →L[ℝ] E)).contDiff
  have hG := (isUnit_adjoint_comp_self_iff A).mpr hA
  have hi : ContDiffAt ℝ n (Ring.inverse : (E →L[ℝ] E) → E →L[ℝ] E)
      (adjoint A ∘L A) := by
    have h := contDiffAt_ringInverse ℝ (n := n) hG.unit
    rwa [hG.unit_spec] at h
  have hg : ContDiffAt ℝ n (fun B : E →L[ℝ] F ↦ adjoint B ∘L B) A :=
    ha.contDiffAt.clm_comp (contDiffAt_id (E := E →L[ℝ] F))
  have hi' : ContDiffAt ℝ n
      (fun B : E →L[ℝ] F ↦ Ring.inverse (adjoint B ∘L B)) A :=
    hi.comp (f := fun B : E →L[ℝ] F ↦ adjoint B ∘L B) A hg
  unfold gramLeftInverse
  exact hi'.clm_comp ha.contDiffAt
end ContinuousLinearMap

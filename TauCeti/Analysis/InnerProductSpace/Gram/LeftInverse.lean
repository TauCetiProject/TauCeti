/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.InnerProductSpace.Adjoint
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

## Main results

* `ContinuousLinearMap.eq_gramLeftInverse`: uniqueness among bounded left inverses vanishing
  on the orthogonal complement of the range, without a separate invertibility assumption.
* `ContinuousLinearMap.sub_apply_gramLeftInverse_mem_orthogonal_range`: the residual is
  orthogonal to the range when the Gram operator is invertible.
* `ContinuousLinearMap.gramLeftInverse_comp_equiv` and
  `ContinuousLinearMap.gramLeftInverse_comp_of_isometry`: changes of source coordinates and
  isometric changes of ambient space.
* `ContinuousLinearMap.continuousAt_gramLeftInverse` and
  `ContinuousLinearMap.contDiffAt_gramLeftInverse`: continuous and real smooth dependence on
  operators with invertible Gram operator.
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
@[simp]
theorem gramLeftInverse_of_not_isUnit {A : E →L[𝕜] F}
    (hA : ¬IsUnit (adjoint A ∘L A)) : gramLeftInverse A = 0 := by
  rw [gramLeftInverse_def, Ring.inverse_non_unit _ hA, zero_comp]

/-- A noninjective operator has zero Gram left inverse. -/
@[simp]
theorem gramLeftInverse_of_not_injective {A : E →L[𝕜] F} (hA : ¬Injective A) :
    gramLeftInverse A = 0 := by
  exact gramLeftInverse_of_not_isUnit fun h ↦
    hA (A.adjoint_comp_self_injective_iff.mp (isUnit_iff_bijective.mp h).injective)

@[simp]
theorem gramLeftInverse_zero : gramLeftInverse (0 : E →L[𝕜] F) = 0 := by
  simp [gramLeftInverse_def]

/-- The Gram left inverse cancels an operator with invertible Gram operator. -/
@[simp]
theorem gramLeftInverse_comp_self {A : E →L[𝕜] F} (hA : IsUnit (adjoint A ∘L A)) :
    gramLeftInverse A ∘L A = .id 𝕜 E := by
  rw [gramLeftInverse_def, comp_assoc, ← mul_def, ← one_def]
  exact Ring.inverse_mul_cancel _ hA

/-- Applying the Gram left inverse to `A v` recovers `v` when `A` has invertible Gram operator. -/
@[simp]
theorem gramLeftInverse_apply_self {A : E →L[𝕜] F} (hA : IsUnit (adjoint A ∘L A)) (v : E) :
    gramLeftInverse A (A v) = v := by
  simpa only [comp_apply, id_apply] using DFunLike.congr_fun (gramLeftInverse_comp_self hA) v

/-- The Gram left inverse vanishes on the orthogonal complement of the range. -/
@[simp]
theorem gramLeftInverse_apply_of_mem_orthogonal {A : E →L[𝕜] F} {v : F}
    (hv : v ∈ A.rangeᗮ) : gramLeftInverse A v = 0 := by
  rw [orthogonal_range, LinearMap.mem_ker, coe_coe] at hv
  simp only [gramLeftInverse_def, comp_apply, hv, map_zero]

/-- When `A` has invertible Gram operator, the kernel of `gramLeftInverse A` is `A.rangeᗮ`,
the orthogonal complement of the range of `A`. -/
@[simp]
theorem ker_gramLeftInverse {A : E →L[𝕜] F} (hA : IsUnit (adjoint A ∘L A)) :
    (gramLeftInverse A).ker = A.rangeᗮ := by
  rw [gramLeftInverse_def, orthogonal_range]
  exact LinearMap.ker_comp_of_ker_eq_bot _
    (LinearMap.ker_eq_bot_of_injective (isUnit_iff_bijective.mp hA.ringInverse).injective)

/-- When `A` has invertible Gram operator, subtracting its Gram component leaves a vector
orthogonal to the range of `A`. -/
theorem sub_apply_gramLeftInverse_mem_orthogonal_range {A : E →L[𝕜] F}
    (hA : IsUnit (adjoint A ∘L A)) (v : F) :
    v - A (gramLeftInverse A v) ∈ A.rangeᗮ := by
  rw [← ker_gramLeftInverse hA, LinearMap.mem_ker]
  simp [gramLeftInverse_apply_self hA]

/-- The Gram operator of a bijective bounded operator between Hilbert spaces is invertible. -/
theorem isUnit_adjoint_comp_self_of_bijective {A : E →L[𝕜] F} (hA : Bijective A) :
    IsUnit (adjoint A ∘L A) := by
  let e := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hA.injective) (LinearMap.range_eq_top.mpr hA.surjective)
  have hadj : Bijective (adjoint A) :=
    ContinuousLinearEquiv.coe_ofBijective A _ _ ▸ e.adjoint_bijective
  exact isUnit_iff_bijective.mpr (hadj.comp hA)

/-- A bounded left inverse of `A` vanishing on `A.rangeᗮ` is the Gram left inverse. -/
theorem eq_gramLeftInverse {A : E →L[𝕜] F} {L : F →L[𝕜] E}
    (hL : L ∘L A = .id 𝕜 E) (horth : ∀ v ∈ A.rangeᗮ, L v = 0) :
    L = gramLeftInverse A := by
  have hleft : LeftInverse L A := fun x ↦ DFunLike.congr_fun hL x
  have hrange : A.range = (A ∘L L - .id 𝕜 F).ker := by
    ext v
    simp only [LinearMap.mem_range, coe_coe, LinearMap.mem_ker, sub_apply, comp_apply,
      id_apply, sub_eq_zero]
    exact ⟨by rintro ⟨x, rfl⟩; rw [hleft], fun h ↦ ⟨L v, h⟩⟩
  have hclosed : IsClosed (A.range : Set F) := hrange ▸ (A ∘L L - .id 𝕜 F).isClosed_ker
  have : CompleteSpace A.range := hclosed.completeSpace_coe
  have hadj : adjoint A ∘L adjoint L = .id 𝕜 E := by
    rw [← adjoint_comp, hL, adjoint_id]
  have hG : IsUnit (adjoint A ∘L A) := by
    refine isUnit_iff_bijective.mpr ⟨A.adjoint_comp_self_injective_iff.mpr hleft.injective, ?_⟩
    intro y
    have hy : adjoint L y ∈ A.range := by
      rw [← A.range.orthogonal_orthogonal]
      exact Submodule.orthogonal_le (fun v hv ↦ horth v hv)
        (L.adjoint_apply_mem_orthogonal_ker y)
    obtain ⟨x, hx⟩ := hy
    simp only [coe_coe] at hx
    exact ⟨x, by rw [comp_apply, hx]; exact DFunLike.congr_fun hadj y⟩
  ext v
  have h := horth _ (sub_apply_gramLeftInverse_mem_orthogonal_range hG v)
  have hcancel := DFunLike.congr_fun hL (gramLeftInverse A v)
  simp only [comp_apply, id_apply] at hcancel
  simpa only [map_sub, hcancel, sub_eq_zero] using h

@[simp]
theorem gramLeftInverse_equiv (e : E ≃L[𝕜] F) :
    gramLeftInverse (e : E →L[𝕜] F) = e.symm := by
  ext v
  have hG := isUnit_adjoint_comp_self_of_bijective (A := (e : E →L[𝕜] F)) e.bijective
  simpa using gramLeftInverse_apply_self hG (e.symm v)

@[simp]
theorem gramLeftInverse_id : gramLeftInverse (.id 𝕜 E) = .id 𝕜 E := by
  simpa using gramLeftInverse_equiv (ContinuousLinearEquiv.refl 𝕜 E)

@[simp]
theorem gramLeftInverse_one : gramLeftInverse (1 : E →L[𝕜] E) = 1 :=
  gramLeftInverse_id

/-- On an invertible bounded operator the Gram left inverse is its inverse. -/
theorem IsInvertible.gramLeftInverse_eq_inverse {A : E →L[𝕜] F} (hA : A.IsInvertible) :
    gramLeftInverse A = A.inverse := by
  obtain ⟨e, rfl⟩ := hA
  rw [gramLeftInverse_equiv, inverse_equiv]

/-- The Gram left inverse of a bijective operator is bijective. -/
theorem gramLeftInverse_bijective {A : E →L[𝕜] F} (hA : Bijective A) :
    Bijective (gramLeftInverse A) := by
  let e := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hA.injective) (LinearMap.range_eq_top.mpr hA.surjective)
  rw [← ContinuousLinearEquiv.coe_ofBijective A _ _, gramLeftInverse_equiv]
  exact e.symm.bijective

/-- For an isometry the Gram left inverse is the adjoint. -/
theorem gramLeftInverse_of_isometry {A : E →L[𝕜] F} (hA : Isometry A) :
    gramLeftInverse A = adjoint A := by
  rw [gramLeftInverse_def, (isometry_iff_adjoint_comp_self A).mp hA,
    Ring.inverse_one, one_def, id_comp]

section Composition

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- Changing coordinates in the source changes the Gram left inverse by the inverse
coordinate map. -/
theorem gramLeftInverse_comp_equiv (A : E →L[𝕜] F) (e : G ≃L[𝕜] E) :
    gramLeftInverse (A ∘L (e : G →L[𝕜] E)) =
      (e.symm : E →L[𝕜] G) ∘L gramLeftInverse A := by
  have he : (e.adjointEquiv : E →L[𝕜] G) = adjoint (e : G →L[𝕜] E) := by
    ext v
    exact e.adjointEquiv_apply v
  rw [gramLeftInverse_def, adjoint_comp, comp_assoc, ← comp_assoc (adjoint A), ← he,
    ringInverse_eq_inverse, inverse_equiv_comp, inverse_comp_equiv, gramLeftInverse_def,
    ringInverse_eq_inverse]
  ext v
  simp

/-- Postcomposing with an isometry transports the Gram left inverse by the adjoint isometry. -/
theorem gramLeftInverse_comp_of_isometry (A : E →L[𝕜] F) {U : F →L[𝕜] G}
    (hU : Isometry U) :
    gramLeftInverse (U ∘L A) = gramLeftInverse A ∘L adjoint U := by
  have hG : adjoint (U ∘L A) ∘L (U ∘L A) = adjoint A ∘L A := by
    rw [adjoint_comp, comp_assoc, ← comp_assoc (adjoint U),
      (isometry_iff_adjoint_comp_self U).mp hU, one_def, id_comp]
  rw [gramLeftInverse_def, hG, adjoint_comp, gramLeftInverse_def, comp_assoc]

end Composition

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

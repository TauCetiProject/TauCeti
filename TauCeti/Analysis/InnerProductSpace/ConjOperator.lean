/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.QuaternionicStructure

/-!
# Conjugating operators by a conjugate-linear isometric equivalence

For a conjugate-linear isometric equivalence `e : E ≃ₗᵢ⋆[𝕜] F`, the map `A ↦ e ∘ A ∘ e⁻¹` sends
`𝕜`-linear operators on `E` to `𝕜`-linear operators on `F`, because the two conjugate-linearities
cancel. As a map of operators it is itself a conjugate-linear isometric equivalence
(`LinearIsometryEquiv.conjOperator`); it is unital and multiplicative, and between Hilbert spaces
it commutes with adjoints. This is the conjugate-linear counterpart of Mathlib's
`LinearIsometryEquiv.conjStarAlgEquiv`. Examples are conjugation of operators by the coordinatewise
conjugation of an orthonormal basis and by the modular conjugation of a tracial GNS space.

## Main definitions

* `LinearIsometryEquiv.conjOperator e`: the conjugate-linear isometric equivalence
  `A ↦ e ∘ A ∘ e⁻¹` of operator spaces.

## Main statements

* `LinearIsometryEquiv.conjOperator_symm`: its inverse is conjugation by `e⁻¹`.
* `LinearIsometryEquiv.conjOperator_one`, `LinearIsometryEquiv.conjOperator_mul`: it is unital
  and multiplicative.
* `LinearIsometryEquiv.conjOperator_star`: it commutes with adjoints.
-/

public section

open scoped InnerProductSpace

namespace LinearIsometryEquiv

section Normed

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Conjugation of operators by a conjugate-linear isometric equivalence**, `A ↦ e ∘ A ∘ e⁻¹`.
The two conjugate-linearities of `e` and `e⁻¹` cancel, so `e ∘ A ∘ e⁻¹` is again `𝕜`-linear, and it
has the norm of `A` because `e` is isometric. As a map of operators it is conjugate linear. -/
noncomputable def conjOperator (e : E ≃ₗᵢ⋆[𝕜] F) : (E →L[𝕜] E) ≃ₗᵢ⋆[𝕜] (F →L[𝕜] F) :=
  { e.toContinuousLinearEquiv.arrowCongrSL e.toContinuousLinearEquiv with
    norm_map' A := (ContinuousLinearMap.opNorm_linearIsometryEquiv_comp e _).trans
      (A.opNorm_comp_linearIsometryEquiv e.symm) }

variable (e : E ≃ₗᵢ⋆[𝕜] F)

/-- The operator `e ∘ A ∘ e⁻¹` acts by `x ↦ e (A (e⁻¹ x))`. -/
@[simp]
theorem conjOperator_apply (A : E →L[𝕜] E) (x : F) :
    e.conjOperator A x = e (A (e.symm x)) :=
  (rfl)

/-- The inverse of conjugation by `e` is conjugation by `e⁻¹`. -/
@[simp]
theorem conjOperator_symm : e.conjOperator.symm = e.symm.conjOperator :=
  (rfl)

/-- Conjugation by `e` fixes the identity operator. -/
@[simp]
theorem conjOperator_one : e.conjOperator 1 = 1 := by
  ext x
  simp

/-- Conjugation by `e` is multiplicative. -/
@[simp]
theorem conjOperator_mul (A B : E →L[𝕜] E) :
    e.conjOperator (A * B) = e.conjOperator A * e.conjOperator B := by
  ext x
  simp

end Normed

section InnerProduct

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F]
  (e : E ≃ₗᵢ⋆[𝕜] F)

/-- Conjugation by `e` commutes with adjoints: `e A⋆ e⁻¹ = (e A e⁻¹)⋆`, because `e` reverses the
inner product. -/
@[simp]
theorem conjOperator_star (A : E →L[𝕜] E) :
    e.conjOperator (star A) = star (e.conjOperator A) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.eq_adjoint_iff]
  intro u v
  have h (x y : E) : ⟪e x, e y⟫_𝕜 = ⟪y, x⟫_𝕜 :=
    (e.toLinearIsometry.inner_map_map_eq_conj x y).trans (inner_conj_symm y x)
  rw [conjOperator_apply, conjOperator_apply, ← e.apply_symm_apply v, h,
    ContinuousLinearMap.adjoint_inner_right, ← h, e.apply_symm_apply, e.symm_apply_apply]

end InnerProduct

end LinearIsometryEquiv

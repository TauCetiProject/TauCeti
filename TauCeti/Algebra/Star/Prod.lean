/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Prod
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.GroupWithZero.Idempotent
import TauCeti.Algebra.Group.Idempotent

/-!
# Star projections and equivalences of products

Star projections in a product are characterized coordinatewise. When each nonzero
element of the coefficient semiring cancels on the left, the square product has only
zero, one, and the two coordinate projections.
The coordinate swap is a star algebra equivalence between the two orders of a product,
lifting `Equiv.prodComm` with only the operations preserved by a star algebra equivalence.
-/

public section

/-- An element of a product is a star projection exactly when both coordinates are. -/
@[simp]
theorem Prod.isStarProjection_iff {A B : Type*} [Mul A] [Star A] [Mul B] [Star B]
    (x : A × B) : IsStarProjection x ↔ IsStarProjection x.1 ∧ IsStarProjection x.2 := by
  simp only [_root_.isStarProjection_iff, Prod.isIdempotentElem_iff, isSelfAdjoint_iff,
    Prod.ext_iff, Prod.fst_star, Prod.snd_star]
  tauto

/-- The star projections in the square of a semiring with left cancellation away from
zero are zero, one, and the two coordinate projections. -/
theorem Prod.isStarProjection_iff_eq_zero_or_one {R : Type*} [Semiring R]
    [IsLeftCancelMulZero R] [StarRing R] (x : R × R) :
    IsStarProjection x ↔ x = 0 ∨ x = (1, 0) ∨ x = (0, 1) ∨ x = 1 := by
  rw [Prod.isStarProjection_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    have h₁' := h₁.isIdempotentElem.eq_zero_or_one
    have h₂' := h₂.isIdempotentElem.eq_zero_or_one
    simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, Prod.fst_one, Prod.snd_one]
    tauto
  · rintro (rfl | rfl | rfl | rfl) <;> simp

namespace StarAlgEquiv

variable (R : Type*) {A B : Type*} [Add A] [Mul A] [Star A] [SMul R A]
  [Add B] [Mul B] [Star B] [SMul R B]

/-- Swapping the coordinates of a product preserves addition, multiplication, star, and the
scalar action. -/
def prodComm : A × B ≃⋆ₐ[R] B × A where
  __ := Equiv.prodComm A B
  map_add' x y := by rw [Equiv.toFun_as_coe, Equiv.coe_prodComm]; rfl
  map_mul' x y := by rw [Equiv.toFun_as_coe, Equiv.coe_prodComm]; rfl
  map_star' x := by rw [Equiv.toFun_as_coe, Equiv.coe_prodComm]; rfl
  map_smul' r x := by rw [Equiv.toFun_as_coe, Equiv.coe_prodComm]; rfl

/-- The star algebra equivalence of the two product orders swaps the coordinates. -/
@[simp]
theorem prodComm_apply (x : A × B) :
    (prodComm R : A × B ≃⋆ₐ[R] B × A) x = x.swap :=
  congrFun (Equiv.coe_prodComm A B) x

/-- The inverse swaps the coordinates in the reverse product order. -/
@[simp]
theorem prodComm_symm :
    (prodComm R : A × B ≃⋆ₐ[R] B × A).symm = prodComm R := by
  apply StarAlgEquiv.ext
  intro x
  rw [StarAlgEquiv.symm_apply_eq, prodComm_apply, prodComm_apply, Prod.swap_swap]

end StarAlgEquiv

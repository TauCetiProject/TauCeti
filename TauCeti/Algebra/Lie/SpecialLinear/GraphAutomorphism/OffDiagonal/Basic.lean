/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.GraphAutomorphism
public import TauCeti.Algebra.Lie.SpecialLinear.OffDiagonal

/-!
# The signed type-A action on off-diagonal matrices

The native graph automorphism preserves the zero-diagonal submodule. On its matrix-unit
basis it is the signed permutation reversing and interchanging the two indices. The signs
are defined over the integers, so their cycle products retain their meaning in characteristic two.
-/

public section

namespace TauCeti

open LieAlgebra.SpecialLinear

attribute [local instance 100] LieRing.ofAssociativeRing

variable (r : ℕ)

/-- The graph involution on off-diagonal positions reverses and interchanges the indices. -/
def typeAOffDiagonalPerm :
    Equiv.Perm {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2} where
  toFun p := ⟨(p.val.2.rev, p.val.1.rev), Fin.rev_injective.ne p.property.symm⟩
  invFun p := ⟨(p.val.2.rev, p.val.1.rev), Fin.rev_injective.ne p.property.symm⟩
  left_inv p := by apply Subtype.ext; simp
  right_inv p := by apply Subtype.ext; simp

/-- The underlying pair is reverse transpose. -/
@[simp]
theorem typeAOffDiagonalPerm_apply_val
    (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    (typeAOffDiagonalPerm r p).val = (p.val.2.rev, p.val.1.rev) :=
  (rfl)

/-- Reverse transpose has order dividing two on positions. -/
@[simp]
theorem typeAOffDiagonalPerm_apply_apply
    (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    typeAOffDiagonalPerm r (typeAOffDiagonalPerm r p) = p := by
  apply Subtype.ext
  simp

/-- Fixed off-diagonal positions are exactly the off-diagonal antidiagonal entries. -/
theorem typeAOffDiagonalPerm_eq_self_iff
    (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    typeAOffDiagonalPerm r p = p ↔ p.val.1.val + p.val.2.val = r := by
  rw [Subtype.ext_iff, typeAOffDiagonalPerm_apply_val, Prod.ext_iff]
  simp only [Fin.ext_iff, Fin.val_rev]
  have hi := p.val.1.isLt
  have hj := p.val.2.isLt
  omega

/-- The integral sign on a native off-diagonal matrix unit. -/
def typeAOffDiagonalSign
    (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) : ℤ :=
  (-1) ^ (p.val.1.val + p.val.2.val + 1)

/-- The arrow sign is the integral parity sign of the sum of its two indices plus one. -/
theorem typeAOffDiagonalSign_eq
    (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    typeAOffDiagonalSign r p = (-1 : ℤ) ^ (p.val.1.val + p.val.2.val + 1) :=
  (rfl)

/-- The integral arrow sign squares to one. -/
@[simp]
theorem typeAOffDiagonalSign_mul_self
    (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    typeAOffDiagonalSign r p * typeAOffDiagonalSign r p = 1 := by
  simp [typeAOffDiagonalSign_eq, ← mul_pow]

/-- The sign is constant along each reverse-transpose orbit. -/
@[simp]
theorem typeAOffDiagonalSign_perm
    (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    typeAOffDiagonalSign r (typeAOffDiagonalPerm r p) = typeAOffDiagonalSign r p := by
  have hmod : ((p.val.2.rev : ℕ) + (p.val.1.rev : ℕ) + 1) % 2 =
      ((p.val.1 : ℕ) + (p.val.2 : ℕ) + 1) % 2 := by
    simp only [Fin.val_rev]
    omega
  simp only [typeAOffDiagonalSign_eq, typeAOffDiagonalPerm_apply_val]
  rw [neg_one_pow_eq_pow_mod_two ((p.val.2.rev : ℕ) + (p.val.1.rev : ℕ) + 1),
    neg_one_pow_eq_pow_mod_two ((p.val.1 : ℕ) + (p.val.2 : ℕ) + 1), hmod]

/-- Every singleton has the sign determined by the parity of the rank plus one. -/
theorem typeAOffDiagonalSign_of_fixed
    (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2})
    (h : typeAOffDiagonalPerm r p = p) :
    typeAOffDiagonalSign r p = (-1 : ℤ) ^ (r + 1) := by
  rw [typeAOffDiagonalSign_eq, (typeAOffDiagonalPerm_eq_self_iff r p).mp h]

variable (A : Type*) [CommRing A]

/-- The native graph automorphism preserves zero diagonal. -/
theorem typeASpecialLinearGraphAutomorphism_mem_specialLinearOffDiagonal
    (X : sl (Fin (r + 1)) A) (hX : X ∈ specialLinearOffDiagonal (Fin (r + 1)) A) :
    typeASpecialLinearGraphAutomorphism r A X ∈ specialLinearOffDiagonal (Fin (r + 1)) A := by
  rw [mem_specialLinearOffDiagonal_iff] at hX ⊢
  intro i
  rw [coe_typeASpecialLinearGraphAutomorphism, typeAGraphLieEquiv_apply_apply, hX]
  simp

/-- The native graph equivalence maps the zero-diagonal submodule onto itself. -/
theorem map_typeASpecialLinearGraphAutomorphism_specialLinearOffDiagonal :
    (specialLinearOffDiagonal (Fin (r + 1)) A).map
      (typeASpecialLinearGraphAutomorphism r A).toLinearEquiv.toLinearMap =
        specialLinearOffDiagonal (Fin (r + 1)) A := by
  ext X
  constructor
  · rintro ⟨Y, hY, rfl⟩
    exact typeASpecialLinearGraphAutomorphism_mem_specialLinearOffDiagonal r A Y hY
  · intro hX
    exact ⟨typeASpecialLinearGraphAutomorphism r A X,
      typeASpecialLinearGraphAutomorphism_mem_specialLinearOffDiagonal r A X hX,
      typeASpecialLinearGraphAutomorphism_typeASpecialLinearGraphAutomorphism r A X⟩

/-- The restriction of the native graph automorphism to zero-diagonal matrices. -/
def typeAOffDiagonalGraphEquiv :
    specialLinearOffDiagonal (Fin (r + 1)) A ≃ₗ[A]
      specialLinearOffDiagonal (Fin (r + 1)) A :=
  (typeASpecialLinearGraphAutomorphism r A).toLinearEquiv.ofSubmodules _ _
    (map_typeASpecialLinearGraphAutomorphism_specialLinearOffDiagonal r A)

/-- The restricted map retains the actual native matrix action. -/
@[simp]
theorem typeAOffDiagonalGraphEquiv_apply
    (X : specialLinearOffDiagonal (Fin (r + 1)) A) :
    (typeAOffDiagonalGraphEquiv r A X).val = typeASpecialLinearGraphAutomorphism r A X.val :=
  (rfl)

/-- On the native matrix-unit basis the graph equivalence is the integral signed permutation. -/
theorem typeAOffDiagonalGraphEquiv_basis
    (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    typeAOffDiagonalGraphEquiv r A (specialLinearOffDiagonalBasis (Fin (r + 1)) A p) =
      (typeAOffDiagonalSign r p : A) •
        specialLinearOffDiagonalBasis (Fin (r + 1)) A (typeAOffDiagonalPerm r p) := by
  apply Subtype.ext
  simp only [typeAOffDiagonalGraphEquiv_apply, Submodule.coe_smul,
    specialLinearOffDiagonalBasis_apply, typeASpecialLinearGraphAutomorphism_single]
  simp [typeAOffDiagonalSign_eq, typeAOffDiagonalPerm, ← map_smul]

end TauCeti

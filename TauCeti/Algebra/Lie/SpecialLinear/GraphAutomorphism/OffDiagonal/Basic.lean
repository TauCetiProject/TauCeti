/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.GraphAutomorphism
public import TauCeti.Algebra.Lie.SpecialLinear.OffDiagonal
public import TauCeti.Data.Fin.DistinctPairs

import TauCeti.Data.Fin.Rev

/-!
# The signed type-A action on off-diagonal matrices

The native graph automorphism preserves the zero-diagonal submodule. On its matrix-unit
basis it is the signed permutation `TauCeti.finDistinctPairsRevSwap` reversing and interchanging
the two indices. The signs are defined over the integers, so their cycle products retain their
meaning in characteristic two.

## Main definitions

* `TauCeti.typeAOffDiagonalSign`: the integral sign `(-1) ^ (i + j + 1)` of the matrix unit at
  `(i, j)`, constant along the orbits of `TauCeti.finDistinctPairsRevSwap`.
* `TauCeti.typeAOffDiagonalGraphEquiv`: the graph automorphism restricted to the zero-diagonal
  submodule, an involutive linear equivalence.

## Main results

* `TauCeti.typeAOffDiagonalGraphEquiv_typeAOffDiagonalGraphEquiv` and
  `TauCeti.typeAOffDiagonalGraphEquiv_symm`: the restricted graph automorphism is its own
  inverse.
* `TauCeti.typeAOffDiagonalGraphEquiv_basis`: on the matrix-unit basis the restricted graph
  automorphism is the signed permutation `TauCeti.finDistinctPairsRevSwap`.
-/

public section

namespace TauCeti

open LieAlgebra.SpecialLinear

attribute [local instance 100] LieRing.ofAssociativeRing

variable (r : ℕ)

/-- The integral sign on a native off-diagonal matrix unit. -/
def typeAOffDiagonalSign
    (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) : ℤ :=
  (-1) ^ (p.val.1.val + p.val.2.val + 1)

/-- The arrow sign is the integral parity sign of the sum of its two indices plus one. -/
theorem typeAOffDiagonalSign_def
    (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    typeAOffDiagonalSign r p = (-1 : ℤ) ^ (p.val.1.val + p.val.2.val + 1) :=
  (rfl)

/-- The sign is constant along each reverse-transpose orbit. -/
@[simp]
theorem typeAOffDiagonalSign_finDistinctPairsRevSwap
    (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    typeAOffDiagonalSign r (finDistinctPairsRevSwap (r + 1) p) = typeAOffDiagonalSign r p := by
  rw [typeAOffDiagonalSign_def, typeAOffDiagonalSign_def, finDistinctPairsRevSwap_apply_val]
  exact Fin.neg_one_pow_rev_add_rev_add_one _ _

/-- Every singleton has the sign determined by the parity of the rank plus one. -/
theorem typeAOffDiagonalSign_of_fixed
    (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2})
    (h : finDistinctPairsRevSwap (r + 1) p = p) :
    typeAOffDiagonalSign r p = (-1 : ℤ) ^ (r + 1) := by
  rw [typeAOffDiagonalSign_def, (finDistinctPairsRevSwap_eq_self_iff p).mp h]

variable (A : Type*) [CommRing A]

/-- The native graph automorphism preserves zero diagonal. -/
theorem typeASpecialLinearGraphAutomorphism_mem_specialLinearOffDiagonal
    (X : sl (Fin (r + 1)) A) (hX : X ∈ specialLinearOffDiagonal (Fin (r + 1)) A) :
    typeASpecialLinearGraphAutomorphism r A X ∈ specialLinearOffDiagonal (Fin (r + 1)) A := by
  rw [mem_specialLinearOffDiagonal_iff] at hX ⊢
  intro i
  rw [coe_typeASpecialLinearGraphAutomorphism, typeAGraphLieEquiv_apply_apply, hX]
  simp

/-- The restriction of the native graph automorphism to zero-diagonal matrices, an involution. -/
def typeAOffDiagonalGraphEquiv :
    specialLinearOffDiagonal (Fin (r + 1)) A ≃ₗ[A]
      specialLinearOffDiagonal (Fin (r + 1)) A :=
  LinearEquiv.ofInvolutive
    ((typeASpecialLinearGraphAutomorphism r A).toLinearEquiv.toLinearMap.restrict
      (fun X hX ↦ by
        simpa only [LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv] using
          typeASpecialLinearGraphAutomorphism_mem_specialLinearOffDiagonal r A X hX))
    fun X ↦ by
      rw [LinearMap.restrict_apply, LinearMap.restrict_apply]
      apply Subtype.ext
      simpa only [LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv] using
        typeASpecialLinearGraphAutomorphism_typeASpecialLinearGraphAutomorphism r A X.val

/-- The restricted map retains the actual native matrix action. -/
@[simp]
theorem typeAOffDiagonalGraphEquiv_apply
    (X : specialLinearOffDiagonal (Fin (r + 1)) A) :
    (typeAOffDiagonalGraphEquiv r A X).val = typeASpecialLinearGraphAutomorphism r A X.val :=
  (rfl)

/-- The restricted graph equivalence is an involution. -/
@[simp]
theorem typeAOffDiagonalGraphEquiv_typeAOffDiagonalGraphEquiv
    (X : specialLinearOffDiagonal (Fin (r + 1)) A) :
    typeAOffDiagonalGraphEquiv r A (typeAOffDiagonalGraphEquiv r A X) = X := by
  apply Subtype.ext
  rw [typeAOffDiagonalGraphEquiv_apply, typeAOffDiagonalGraphEquiv_apply,
    typeASpecialLinearGraphAutomorphism_typeASpecialLinearGraphAutomorphism]

/-- The restricted graph equivalence is its own inverse. -/
@[simp]
theorem typeAOffDiagonalGraphEquiv_symm :
    (typeAOffDiagonalGraphEquiv r A).symm = typeAOffDiagonalGraphEquiv r A :=
  LinearEquiv.ext fun X ↦ by
    rw [LinearEquiv.symm_apply_eq, typeAOffDiagonalGraphEquiv_typeAOffDiagonalGraphEquiv]

/-- The underlying linear map of the restricted graph equivalence is the restriction of the
native graph automorphism to the zero-diagonal submodule. -/
theorem typeAOffDiagonalGraphEquiv_toLinearMap :
    (typeAOffDiagonalGraphEquiv r A).toLinearMap =
      (typeASpecialLinearGraphAutomorphism r A).toLinearEquiv.toLinearMap.restrict
        (typeASpecialLinearGraphAutomorphism_mem_specialLinearOffDiagonal r A) :=
  (rfl)

/-- On the native matrix-unit basis the graph equivalence is the integral signed permutation. -/
@[simp]
theorem typeAOffDiagonalGraphEquiv_basis
    (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    typeAOffDiagonalGraphEquiv r A (specialLinearOffDiagonalBasis (Fin (r + 1)) A p) =
      (typeAOffDiagonalSign r p : A) •
        specialLinearOffDiagonalBasis (Fin (r + 1)) A (finDistinctPairsRevSwap (r + 1) p) := by
  apply Subtype.ext
  simp only [typeAOffDiagonalGraphEquiv_apply, Submodule.coe_smul,
    specialLinearOffDiagonalBasis_apply, typeASpecialLinearGraphAutomorphism_single]
  simp [typeAOffDiagonalSign_def, ← map_smul]

end TauCeti

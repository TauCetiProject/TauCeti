/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Finsupp
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.Algebra.BigOperators.Pi

/-!
# Balanced tensor products with a finite free left module

Tensoring a right module `M` with the free left module `P → A` on a finite set `P` returns the
module `P → M` of `M`-valued functions on `P`: the identification sends `m ⊗ g` to
`fun y ↦ m · g y`, and its inverse sends `f` to `∑ x, f x ⊗ e_x` with `e_x` the coordinate
functions. It is the finite specialization of `finsuppScalarRight` through
`Finsupp.linearEquivFunOnFinite`. For `P` a point this is the unit identification
`TauCeti.BalancedTensorProduct.rid`.

The ground-ring action on `A` only needs to be compatible with its right action on `M`:
the two actions on `M` commute and form a scalar tower. An algebra structure on `A` is not
required.

## Main definitions

* `TauCeti.BalancedTensorProduct.piRight`: the linear equivalence
  `BalancedTensorProduct k A M (P → A) ≃ₗ[k] (P → M)`, with `piRight_tmul`, `piRight_tmul_single`
  and `piRight_symm_apply`.

## References

* B. Keller, *Deriving DG categories*, Section 6.1.
-/

public section

namespace TauCeti.BalancedTensorProduct

open MulOpposite

variable (k A : Type*) [CommRing k] [Ring A] [Module k A]
  (M : Type*) [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
  (P : Type*) [Fintype P]

variable [SMulCommClass k Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]

open scoped Classical in
/-- **Tensoring a right module with a finite free left module gives the functions into it**:
`m ⊗ g ↦ fun y ↦ m · g y`, with inverse `f ↦ ∑ x, f x ⊗ e_x`.  This is
`TauCeti.BalancedTensorProduct.rid` with a finite set of coordinates. -/
noncomputable def piRight : BalancedTensorProduct k A M (P → A) ≃ₗ[k] (P → M) :=
  (congr (LinearEquiv.refl k M) (Finsupp.linearEquivFunOnFinite k A P)
      (by intros; rfl) (by intros; rfl)).symm ≪≫ₗ
    finsuppScalarRight k A M P ≪≫ₗ Finsupp.linearEquivFunOnFinite k M P

open scoped Classical in
/-- `piRight` is the finite specialization of `finsuppScalarRight` through the
finite-support/function equivalences. -/
theorem piRight_eq_finsuppScalarRight :
    piRight k A M P =
      (congr (LinearEquiv.refl k M) (Finsupp.linearEquivFunOnFinite k A P)
        (by intros; rfl) (by intros; rfl)).symm ≪≫ₗ
        finsuppScalarRight k A M P ≪≫ₗ Finsupp.linearEquivFunOnFinite k M P := (rfl)

/-- A pure tensor `m ⊗ g` goes to the function `y ↦ m · g y`. -/
@[simp]
theorem piRight_tmul (m : M) (g : P → A) :
    piRight k A M P (tmul k A m g) = fun y ↦ op (g y) • m := by
  ext y
  simp only [piRight, LinearEquiv.trans_apply]
  -- Reduce the identity equivalence in the equivariance proof when matching `congr`.
  erw [congr_symm_tmul]
  simp only [LinearEquiv.refl_symm, LinearEquiv.refl_apply,
    Finsupp.linearEquivFunOnFinite_apply, finsuppScalarRight_tmul_apply,
    Finsupp.linearEquivFunOnFinite_symm_apply]

/-- A tensor with a coordinate function is the function supported at that coordinate.  Not a
`simp` lemma: `piRight_tmul` already normalizes its left-hand side. -/
theorem piRight_tmul_single [DecidableEq P] (x : P) (m : M) :
    piRight k A M P (tmul k A m (Pi.single x 1)) = Pi.single x m := by
  ext y
  simp +contextual [piRight_tmul, Pi.single_apply, apply_ite]

/-- The inverse of `piRight` sends `f` to the sum `∑ x, f x ⊗ e_x` over the coordinate
functions. -/
@[simp]
theorem piRight_symm_apply [DecidableEq P] (f : P → M) :
    (piRight k A M P).symm f = ∑ x : P, tmul k A (f x) (Pi.single x 1) := by
  rw [LinearEquiv.symm_apply_eq, map_sum]
  simp only [piRight_tmul_single]
  exact (Finset.univ_sum_single f).symm

end TauCeti.BalancedTensorProduct

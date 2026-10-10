/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basic
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.LinearAlgebra.Pi

/-!
# Balanced tensor products with a finite free left module

Tensoring a right module `M` with the free left module `P → A` on a finite set `P` returns the
module `P → M` of `M`-valued functions on `P`: the identification sends `m ⊗ g` to
`fun y ↦ m · g y`, and its inverse sends `f` to `∑ x, f x ⊗ e_x` with `e_x` the coordinate
functions.  For `P` a point this is the unit identification `TauCeti.BalancedTensorProduct.rid`.

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

variable (k A : Type*) [CommRing k] [Ring A] [Algebra k A]
  (M : Type*) [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
  (P : Type*)

/-- The bilinear map `(m, g) ↦ fun y ↦ m · g y` underlying `piRight`. -/
private noncomputable def piRightBilinear : M →ₗ[k] (P → A) →ₗ[k] (P → M) :=
  LinearMap.mk₂ k (fun m g y ↦ op (g y) • m)
    (fun m m' g ↦ by ext y; exact smul_add _ _ _)
    (fun c m g ↦ by ext y; exact (smul_comm _ _ _).symm)
    (fun m g g' ↦ by ext y; simp only [Pi.add_apply, op_add, add_smul])
    (fun c m g ↦ by ext y; simp only [Pi.smul_apply, op_smul, smul_assoc])

private theorem piRightBilinear_apply (m : M) (g : P → A) (y : P) :
    piRightBilinear k A M P m g y = op (g y) • m :=
  rfl

private theorem piRightBilinear_balanced (a : A) (m : M) (g : P → A) :
    piRightBilinear k A M P (op a • m) g = piRightBilinear k A M P m (a • g) := by
  ext y
  simp only [piRightBilinear_apply, Pi.smul_apply, smul_eq_mul, op_mul, mul_smul]

variable [Fintype P] [DecidableEq P]

/-- The inverse of `piRight`: `f ↦ ∑ x, f x ⊗ e_x`, with `e_x` the coordinate functions. -/
private noncomputable def piRightInv : (P → M) →ₗ[k] BalancedTensorProduct k A M (P → A) :=
  ∑ x : P, ((mk k A).flip (Pi.single x 1)).comp (LinearMap.proj x)

omit [IsScalarTower k Aᵐᵒᵖ M] in
private theorem piRightInv_apply (f : P → M) :
    piRightInv k A M P f = ∑ x : P, tmul k A (f x) (Pi.single x 1) := by
  simp only [piRightInv, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearMap.flip_apply, mk_apply]

/-- **Tensoring a right module with a finite free left module gives the functions into it**:
`m ⊗ g ↦ fun y ↦ m · g y`, with inverse `f ↦ ∑ x, f x ⊗ e_x`.  This is
`TauCeti.BalancedTensorProduct.rid` with a finite set of coordinates. -/
noncomputable def piRight : BalancedTensorProduct k A M (P → A) ≃ₗ[k] (P → M) :=
  LinearEquiv.ofLinearMap
    (lift (piRightBilinear k A M P) (piRightBilinear_balanced k A M P))
    (piRightInv k A M P)
    (LinearMap.ext fun f ↦ funext fun y ↦ by
      simp only [LinearMap.comp_apply, piRightInv_apply, map_sum, Finset.sum_apply, lift_tmul,
        piRightBilinear_apply, LinearMap.id_apply]
      rw [Finset.sum_eq_single y (fun x _ hx ↦ by simp [Pi.single_eq_of_ne hx.symm]) (by simp)]
      simp)
    (by
      apply hom_ext
      intro m g
      simp only [LinearMap.comp_apply, lift_tmul, piRightInv_apply, piRightBilinear_apply,
        LinearMap.id_apply]
      have hsingle : ∀ x : P, g x • Pi.single x (1 : A) = Pi.single x (g x) := fun x ↦ by
        ext y
        simp [Pi.single_apply]
      simp_rw [balance, hsingle, ← mk_apply]
      rw [← map_sum, Finset.univ_sum_single])

@[simp]
theorem piRight_tmul (m : M) (g : P → A) :
    piRight k A M P (tmul k A m g) = fun y ↦ op (g y) • m := by
  ext y
  simp [piRight, piRightBilinear_apply]

/-- A tensor with a coordinate function is the function supported at that coordinate.  Not a
`simp` lemma: `piRight_tmul` already normalizes its left-hand side. -/
theorem piRight_tmul_single (x : P) (m : M) :
    piRight k A M P (tmul k A m (Pi.single x 1)) = Pi.single x m := by
  ext y
  rw [piRight_tmul]
  by_cases hy : y = x
  · subst hy
    simp
  · simp [Pi.single_eq_of_ne hy]

@[simp]
theorem piRight_symm_apply (f : P → M) :
    (piRight k A M P).symm f = ∑ x : P, tmul k A (f x) (Pi.single x 1) := by
  simp [piRight, piRightInv_apply]

end TauCeti.BalancedTensorProduct

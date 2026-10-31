/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basic
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Balanced tensor products with free left modules

For any set `P`, tensoring a right `A`-module `M` with the free left module `P →₀ A`
gives `P →₀ M`. The equivalence sends `m ⊗ g` to the finite sum of the vectors
`single x (m · g x)`. Its inverse sends `single x m` to `m ⊗ single x 1`.
This finite-support version works without a finiteness assumption on the basis and is
used to tensor row-finite twisted free modules with coefficient modules.

## References

* B. Keller, *Deriving DG categories*, Section 6.1.
-/

public noncomputable section

namespace TauCeti.BalancedTensorProduct

open MulOpposite

variable (R A M P : Type*) [CommRing R] [Ring A] [Module R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M]
  [SMulCommClass R Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]

private def finsuppScalarRightBilinear : M →ₗ[R] (P →₀ A) →ₗ[R] (P →₀ M) :=
  LinearMap.mk₂ R (fun m g ↦ g.sum fun x a ↦ Finsupp.single x (op a • m))
    (fun m m' g ↦ by simp [smul_add, Finsupp.single_add, Finsupp.sum_add])
    (fun r m g ↦ by
      rw [Finsupp.smul_sum]
      congr 1
      funext x a
      rw [← smul_comm r, Finsupp.smul_single])
    (fun m g g' ↦ by
      exact Finsupp.sum_add_index' (by simp) (by intros; simp [add_smul, Finsupp.single_add]))
    (fun r m g ↦ by
      rw [Finsupp.sum_smul_index' (by simp)]
      simp [op_smul, smul_assoc, Finsupp.smul_sum])

private theorem finsuppScalarRightBilinear_apply (m : M) (g : P →₀ A) :
    finsuppScalarRightBilinear R A M P m g = g.sum fun x a ↦ Finsupp.single x (op a • m) :=
  (rfl)

private theorem finsuppScalarRightBilinear_single (m : M) (x : P) (a : A) :
    finsuppScalarRightBilinear R A M P m (Finsupp.single x a) = Finsupp.single x (op a • m) := by
  classical
  simp [finsuppScalarRightBilinear_apply]

private theorem finsuppScalarRightBilinear_balanced (a : A) (m : M) (g : P →₀ A) :
    finsuppScalarRightBilinear R A M P (op a • m) g =
      finsuppScalarRightBilinear R A M P m (a • g) := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g g' hg hg' => simp only [map_add, smul_add, hg, hg']
  | single x b => simp [Finsupp.smul_single, finsuppScalarRightBilinear_single, op_mul, mul_smul]

/-- Tensoring a right module with a free left module gives finite-support coefficient vectors.
The basis set may be infinite. -/
def finsuppScalarRight : BalancedTensorProduct R A M (P →₀ A) ≃ₗ[R] (P →₀ M) := by
  classical
  refine LinearEquiv.ofLinearMap
    (lift (finsuppScalarRightBilinear R A M P) (finsuppScalarRightBilinear_balanced R A M P))
    (Finsupp.lsum R fun x ↦ (mk R A).flip (Finsupp.single x 1)) ?_ ?_
  · apply Finsupp.lhom_ext'
    intro x
    ext m
    simp [LinearMap.comp_apply, Finsupp.lsum_single, finsuppScalarRightBilinear_single]
  · apply hom_ext
    intro m g
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g g' hg hg' => simp only [LinearMap.comp_apply, tmul_add, map_add] at *; rw [hg, hg']
    | single x a =>
      simp only [LinearMap.comp_apply, lift_tmul, finsuppScalarRightBilinear_single,
        Finsupp.lsum_single, LinearMap.flip_apply, mk_apply, LinearMap.id_apply]
      rw [balance, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The image of a pure tensor is the sum of its coefficient vectors. -/
@[simp]
theorem finsuppScalarRight_tmul (m : M) (g : P →₀ A) :
    finsuppScalarRight R A M P (tmul R A m g) =
      g.sum fun x a ↦ Finsupp.single x (op a • m) := by
  simp [finsuppScalarRight, finsuppScalarRightBilinear_apply]

/-- The coefficient of the image of a pure tensor is the right action on that coordinate. -/
theorem finsuppScalarRight_tmul_apply (m : M) (g : P →₀ A) (x : P) :
    finsuppScalarRight R A M P (tmul R A m g) x = op (g x) • m := by
  classical
  simp +contextual [Finsupp.sum_apply, Finsupp.single_apply]

/-- A pure tensor with one basis vector has just one coefficient. -/
theorem finsuppScalarRight_tmul_single (m : M) (x : P) (a : A) :
    finsuppScalarRight R A M P (tmul R A m (Finsupp.single x a)) =
      Finsupp.single x (op a • m) := by
  classical
  simp

/-- The inverse sends an elementary coefficient vector to its basis tensor. -/
@[simp]
theorem finsuppScalarRight_symm_single (x : P) (m : M) :
    (finsuppScalarRight R A M P).symm (Finsupp.single x m) =
      tmul R A m (Finsupp.single x 1) := by
  apply (finsuppScalarRight R A M P).injective
  simp

/-- The inverse equivalence is the finite sum over the support of a coefficient vector. -/
theorem finsuppScalarRight_symm_apply (f : P →₀ M) :
    (finsuppScalarRight R A M P).symm f = f.sum fun x m ↦ tmul R A m (Finsupp.single x 1) := by
  classical
  rw [LinearEquiv.symm_apply_eq, Finsupp.sum, map_sum]
  simp only [finsuppScalarRight_tmul_single, op_one, one_smul]
  exact (Finsupp.sum_single f).symm

end TauCeti.BalancedTensorProduct

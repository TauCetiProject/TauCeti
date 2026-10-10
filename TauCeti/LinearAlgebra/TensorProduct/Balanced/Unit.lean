/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Actions
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Algebra.Tower

/-!
# Unit identifications for balanced tensor products

Tensoring a module with the regular bimodule over a noncommutative algebra returns
the original module. The identifications send `a ⊗ n` to `a • n` and `m ⊗ a` to
`m a`. Their inverses insert `1`. These identifications preserve the outer actions
and hence are the unit identifications for composition of bimodules, before introducing
gradings or differentials. A semiring algebra over
`k` can use these identifications by installing `Algebra.semiringToRing k` locally.

The construction follows the ordinary tensor product underlying Keller,
*Deriving DG categories*, Section 6.1. Scalar actions use Mathlib's `Algebra.lsmul`.
-/

public section

namespace TauCeti.BalancedTensorProduct

open MulOpposite

variable (k A : Type*) [CommRing k] [Ring A] [Algebra k A]

section Left

variable (N : Type*) [AddCommGroup N] [Module k N] [Module A N]
  [IsScalarTower k A N]

private theorem leftAction_balanced (a b : A) (n : N) :
    (Algebra.lsmul k k N (A := A)).toLinearMap (op a • b) n =
      (Algebra.lsmul k k N (A := A)).toLinearMap b (a • n) := by
  simp only [AlgHom.toLinearMap_apply, Algebra.lsmul_apply,
    MulOpposite.smul_eq_mul_unop, unop_op, mul_smul]

/-- Tensoring the regular right module with a left module evaluates the left action. -/
noncomputable def lid : BalancedTensorProduct k A A N ≃ₗ[k] N :=
  LinearEquiv.ofLinearMap
    (lift (A := A) (Algebra.lsmul k k N (A := A)).toLinearMap
      (leftAction_balanced k A N))
    (mk k A 1)
    (by ext n; simp)
    (by
      apply hom_ext
      intro a n
      simp only [LinearMap.comp_apply, lift_tmul, AlgHom.toLinearMap_apply,
        Algebra.lsmul_apply, LinearMap.id_apply, mk_apply]
      simpa using (balance k A a (1 : A) n).symm)

@[simp]
theorem lid_tmul (a : A) (n : N) : lid k A N (tmul k A a n) = a • n := by
  simp [lid]

@[simp]
theorem lid_symm_apply (n : N) : (lid k A N).symm n = tmul k A 1 n := by
  simp [lid]

/-- The left unit identification preserves the left regular outer action. -/
@[simp]
theorem lid_smul_left (a : A) (x : BalancedTensorProduct k A A N) :
    letI := leftModule (k := k) (A := A) (M := A) (N := N) A
    lid k A N (a • x) = a • lid k A N x := by
  let _ := leftModule (k := k) (A := A) (M := A) (N := N) A
  simp only [lid, LinearEquiv.coe_ofLinearMap]
  apply lift_smul_left A
    (Algebra.lsmul k k N (A := A)).toLinearMap (leftAction_balanced k A N)
  intro a b n
  simp

/-- The left unit identification preserves any commuting outer action on the second factor. -/
@[simp]
theorem lid_smul_right (T : Type*) [Semiring T] [Module T N]
    [SMulCommClass T k N] [SMulCommClass A T N]
    (t : T) (x : BalancedTensorProduct k A A N) :
    letI := rightModule (k := k) (A := A) (M := A) (N := N) T
    lid k A N (t • x) = t • lid k A N x := by
  let _ := rightModule (k := k) (A := A) (M := A) (N := N) T
  simp only [lid, LinearEquiv.coe_ofLinearMap]
  apply lift_smul_right T
    (Algebra.lsmul k k N (A := A)).toLinearMap (leftAction_balanced k A N)
  intro t a n
  exact smul_comm a t n

end Left

section Right

variable (M : Type*) [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
  [IsScalarTower k Aᵐᵒᵖ M]

private theorem rightAction_balanced (a : A) (m : M) (b : A) :
    (((Algebra.lsmul k k M (A := Aᵐᵒᵖ)).toLinearMap.comp
      (opLinearEquiv k : A ≃ₗ[k] Aᵐᵒᵖ).toLinearMap).flip) (op a • m) b =
    (((Algebra.lsmul k k M (A := Aᵐᵒᵖ)).toLinearMap.comp
      (opLinearEquiv k : A ≃ₗ[k] Aᵐᵒᵖ).toLinearMap).flip) m (a • b) := by
  simp only [LinearMap.flip_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    coe_opLinearEquiv_toLinearMap, Algebra.lsmul_apply, smul_eq_mul, op_mul, mul_smul]

/-- Tensoring a right module with the regular left module evaluates the right action. -/
noncomputable def rid : BalancedTensorProduct k A M A ≃ₗ[k] M :=
  LinearEquiv.ofLinearMap
    (lift (A := A) (((Algebra.lsmul k k M (A := Aᵐᵒᵖ)).toLinearMap.comp
      (opLinearEquiv k : A ≃ₗ[k] Aᵐᵒᵖ).toLinearMap).flip)
      (rightAction_balanced k A M))
    ((mk k A).flip 1)
    (by ext m; simp)
    (by
      apply hom_ext
      intro m a
      simp only [LinearMap.comp_apply, lift_tmul, LinearMap.flip_apply,
        AlgHom.toLinearMap_apply, coe_opLinearEquiv_toLinearMap, Algebra.lsmul_apply,
        LinearMap.id_apply, mk_apply]
      simpa using balance k A a m (1 : A))

@[simp]
theorem rid_tmul (m : M) (a : A) : rid k A M (tmul k A m a) = op a • m := by
  simp [rid]

@[simp]
theorem rid_symm_apply (m : M) : (rid k A M).symm m = tmul k A m 1 := by
  simp [rid]

/-- The right unit identification preserves any commuting outer action on the first factor. -/
@[simp]
theorem rid_smul_left (S : Type*) [Semiring S] [Module S M]
    [SMulCommClass S k M] [SMulCommClass S Aᵐᵒᵖ M]
    (s : S) (x : BalancedTensorProduct k A M A) :
    letI := leftModule (k := k) (A := A) (M := M) (N := A) S
    rid k A M (s • x) = s • rid k A M x := by
  let _ := leftModule (k := k) (A := A) (M := M) (N := A) S
  simp only [rid, LinearEquiv.coe_ofLinearMap]
  apply lift_smul_left S
    (((Algebra.lsmul k k M (A := Aᵐᵒᵖ)).toLinearMap.comp
      (opLinearEquiv k : A ≃ₗ[k] Aᵐᵒᵖ).toLinearMap).flip) (rightAction_balanced k A M)
  intro s m a
  simpa using (smul_comm s (op a) m).symm

/-- The right unit identification preserves the right regular outer action. -/
@[simp]
theorem rid_smul_right (a : Aᵐᵒᵖ) (x : BalancedTensorProduct k A M A) :
    letI := rightModule (k := k) (A := A) (M := M) (N := A) Aᵐᵒᵖ
    rid k A M (a • x) = a • rid k A M x := by
  let _ := rightModule (k := k) (A := A) (M := M) (N := A) Aᵐᵒᵖ
  simp only [rid, LinearEquiv.coe_ofLinearMap]
  apply lift_smul_right Aᵐᵒᵖ
    (((Algebra.lsmul k k M (A := Aᵐᵒᵖ)).toLinearMap.comp
      (opLinearEquiv k : A ≃ₗ[k] Aᵐᵒᵖ).toLinearMap).flip) (rightAction_balanced k A M)
  intro a m b
  simp [MulOpposite.smul_eq_mul_unop, op_mul]

end Right

end TauCeti.BalancedTensorProduct

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Basic
public import TauCeti.Algebra.AlgebraicGroup.BaseChange.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.BaseChange

/-!
# Point actions after base change

Along any scalar tower `k → K → R`, the `R`-valued action of a base-changed point on `K ⊗[k] M`
conjugates across `cancelBaseChange` to the original `R`-valued point action on `M`; in particular,
for `R = K`, the base-valued action on `K ⊗[k] M` agrees directly with `endOfPoint M`.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w x y

variable {k : Type u} {H : Type v} {M : Type w} {K : Type x}
variable [CommSemiring k] [CommSemiring H] [HopfAlgebra k H] [CommSemiring K] [Algebra k K]
variable [AddCommMonoid M] [Module k M] [Comodule k H M]

/-- Under the base-change adjunction `AlgHom.liftEquiv` along `k → K → R`, the scalar-extended
action of the lifted point on `K ⊗[k] M` conjugates across `cancelBaseChange` to the original
point's action on `M`. -/
@[simp]
theorem cancelBaseChange_conjRingEquiv_endOfPoint_liftEquiv
    {R : Type y} [CommSemiring R] [Algebra k R] [Algebra K R] [IsScalarTower k K R]
    (f : H →ₐ[k] R) :
    let _ := Comodule.baseChange (R := k) (H := H) (M := M) K
    (TensorProduct.AlgebraTensorModule.cancelBaseChange k K R R M).conjRingEquiv
        (endOfPoint (K ⊗[k] M) (AlgHom.liftEquiv k K H R f)) =
      endOfPoint M f := by
  let _ := Comodule.baseChange (R := k) (H := H) (M := M) K
  apply TensorProduct.AlgebraTensorModule.ext
  intro r m
  rw [LinearEquiv.conjRingEquiv_apply_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    endOfPoint_tmul, baseChange_coact, baseChangeCoact_tmul, endOfPoint_tmul]
  induction coact (R := k) (C := H) m with
  | add a b ha hb => simp_all only [TensorProduct.tmul_add, map_add, smul_add]
  | tmul n h => simp [TensorProduct.smul_tmul', smul_eq_mul]

/-- Under `AlgHom.baseChangePointsMulEquiv` along `k → K → R`, the scalar-extended action of the
base-changed point on `K ⊗[k] M` conjugates across `cancelBaseChange` to the original point's
action on `M`. -/
theorem cancelBaseChange_conjRingEquiv_endOfPoint_baseChangePointsMulEquiv
    {R : Type y} [CommSemiring R] [Algebra k R] [Algebra K R] [IsScalarTower k K R]
    (g : WithConv (H →ₐ[k] R)) :
    let _ := Comodule.baseChange (R := k) (H := H) (M := M) K
    (TensorProduct.AlgebraTensorModule.cancelBaseChange k K R R M).conjRingEquiv
        (endOfPoint (K ⊗[k] M) (AlgHom.baseChangePointsMulEquiv (K := K) g).ofConv) =
      endOfPoint M g.ofConv := by
  simp

/-- The action of the base-changed point on the base-changed comodule is the original point's
scalar-extended action. -/
@[simp]
theorem basePointsRepresentation_baseChangePointsMulEquiv
    (g : WithConv (H →ₐ[k] K)) :
    let _ := Comodule.baseChange (R := k) (H := H) (M := M) K
    basePointsRepresentation (H := K ⊗[k] H) (K ⊗[k] M)
        (AlgHom.baseChangePointsMulEquiv (K := K) g) = endOfPoint M g.ofConv := by
  let _ := Comodule.baseChange (R := k) (H := H) (M := M) K
  apply TensorProduct.AlgebraTensorModule.ext
  intro s m
  rw [basePointsRepresentation_apply, endOfPoint_tmul, one_smul,
    baseChange_coact, baseChangeCoact_tmul, endOfPoint_tmul]
  induction coact (R := k) (C := H) m with
  | add a b ha hb => simp_all only [TensorProduct.tmul_add, map_add, smul_add]
  | tmul n h => simp [TensorProduct.smul_tmul', smul_eq_mul, mul_comm]

end TauCeti.Comodule

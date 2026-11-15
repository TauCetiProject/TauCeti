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

The base-valued action on a base-changed comodule agrees with the original extension-valued point
action under the base-change adjunction on points. More generally, for points valued in an algebra
`A` over an intermediate scalar extension `K`, cancelling the intermediate tensor factor identifies
the point action on `K ⊗[k] M` with the original point action on `M`.

## Main declarations

* `TauCeti.Comodule.basePointsRepresentation_baseChangePointsMulEquiv`: the `K`-point action on
  `K ⊗[k] M` agrees with the `K`-valued `endOfPoint` action on `M`.
* `TauCeti.Comodule.cancelBaseChange_comp_endOfPoint_baseChangePointsMulEquiv`: `cancelBaseChange`
  intertwines `endOfPoint` of a base-changed `A`-point on `K ⊗[k] M` with `endOfPoint` on `M`.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w x y

section BaseValue

variable {k : Type u} {H : Type v} {M : Type w} {K : Type x}
variable [CommSemiring k] [CommSemiring H] [HopfAlgebra k H] [CommSemiring K] [Algebra k K]
variable [AddCommMonoid M] [Module k M] [Comodule k H M]

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

end BaseValue

section TowerValue

variable {k : Type u} {H : Type v} {M : Type w} {K : Type x} {A : Type y}
variable [CommSemiring k] [Semiring H] [HopfAlgebra k H]
variable [CommSemiring K] [Algebra k K] [CommSemiring A] [Algebra k A] [Algebra K A]
variable [IsScalarTower k K A]
variable [AddCommMonoid M] [Module k M] [Comodule k H M]

/-- Cancelling an intermediate scalar extension intertwines the point action of a base-changed
`A`-valued point on `K ⊗[k] M` with the original point action on `M`. -/
theorem cancelBaseChange_comp_endOfPoint_baseChangePointsMulEquiv
    (g : WithConv (H →ₐ[k] A)) :
    let _ := Comodule.baseChange (R := k) (H := H) (M := M) K
    (TensorProduct.AlgebraTensorModule.cancelBaseChange k K A A M).toLinearMap ∘ₗ
        endOfPoint (K ⊗[k] M) (AlgHom.baseChangePointsMulEquiv (K := K) g).ofConv =
      endOfPoint M g.ofConv ∘ₗ
        (TensorProduct.AlgebraTensorModule.cancelBaseChange k K A A M).toLinearMap := by
  let _ := Comodule.baseChange (R := k) (H := H) (M := M) K
  apply TensorProduct.AlgebraTensorModule.ext
  intro a z
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ hz₁ hz₂ => simp only [TensorProduct.tmul_add, map_add, hz₁, hz₂]
  | tmul s m =>
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, endOfPoint_tmul,
        baseChange_coact, baseChangeCoact_tmul, map_smul]
      induction coact (R := k) (C := H) m with
      | add x y hx hy => simp_all only [TensorProduct.tmul_add, map_add, smul_add]
      | tmul n h =>
          simp [TensorProduct.smul_tmul', smul_eq_mul, mul_comm, mul_left_comm,
            Algebra.smul_def]

end TowerValue

end TauCeti.Comodule

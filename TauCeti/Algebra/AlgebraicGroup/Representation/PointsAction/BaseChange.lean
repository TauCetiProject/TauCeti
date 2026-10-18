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

The base-valued action on a base-changed comodule agrees with the original extension-valued
point action under the base-change adjunction on points.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w x

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

end TauCeti.Comodule

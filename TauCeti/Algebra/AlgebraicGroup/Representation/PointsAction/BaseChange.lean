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
conjugates across `cancelBaseChange` to the original `R`-valued point action on `M`. Consequently,
nilpotence after subtracting the identity is invariant under base change of points, and for `R = K`
the base-valued action on `K ⊗[k] M` agrees directly with `endOfPoint M`.

## Main declarations

* `TauCeti.Comodule.cancelBaseChange_conjRingEquiv_endOfPoint_liftEquiv`: conjugating the
  scalar-extended action of a lifted point across `cancelBaseChange` recovers `endOfPoint M`;
  `TauCeti.Comodule.cancelBaseChange_endOfPoint_liftEquiv` is its pointwise form.
* `TauCeti.Comodule.isNilpotent_endOfPoint_liftEquiv_sub_one_iff` and
  `TauCeti.Comodule.isNilpotent_endOfPoint_baseChangePointsMulEquiv_sub_one_iff`: nilpotence of a
  point action minus the identity is invariant under base change of points.
* `TauCeti.Comodule.basePointsRepresentation_baseChangePointsMulEquiv`: for `R = K`, the
  base-valued action on `K ⊗[k] M` agrees with `endOfPoint M`.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w x y

section Coalgebra

variable {k : Type u} {H : Type v} {M : Type w} {K : Type x}
variable [CommSemiring k] [Semiring H] [Algebra k H] [Coalgebra k H] [CommSemiring K] [Algebra k K]
variable [AddCommMonoid M] [Module k M] [Comodule k H M]

/-- Under the base-change adjunction `AlgHom.liftEquiv` along `k → K → R`, the scalar-extended
action of the lifted point on `K ⊗[k] M` conjugates across `cancelBaseChange` to the original
point's action on `M`. -/
@[simp]
theorem cancelBaseChange_conjRingEquiv_endOfPoint_liftEquiv
    {R : Type y} [CommSemiring R] [Algebra k R] [Algebra K R] [IsScalarTower k K R]
    (f : H →ₐ[k] R) :
    letI := Comodule.baseChange (R := k) (H := H) (M := M) K
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

/-- Pointwise form of `cancelBaseChange_conjRingEquiv_endOfPoint_liftEquiv`: cancelling the base
change after the scalar-extended action of the lifted point on `K ⊗[k] M` is the original point's
action on `M` after cancelling the base change. -/
@[simp]
theorem cancelBaseChange_endOfPoint_liftEquiv
    {R : Type y} [CommSemiring R] [Algebra k R] [Algebra K R] [IsScalarTower k K R]
    (f : H →ₐ[k] R) (y : R ⊗[K] (K ⊗[k] M)) :
    letI := Comodule.baseChange (R := k) (H := H) (M := M) K
    TensorProduct.AlgebraTensorModule.cancelBaseChange k K R R M
        (endOfPoint (K ⊗[k] M) (AlgHom.liftEquiv k K H R f) y) =
      endOfPoint M f (TensorProduct.AlgebraTensorModule.cancelBaseChange k K R R M y) := by
  let _ := Comodule.baseChange (R := k) (H := H) (M := M) K
  have h := LinearMap.congr_fun (cancelBaseChange_conjRingEquiv_endOfPoint_liftEquiv (K := K) f)
    (TensorProduct.AlgebraTensorModule.cancelBaseChange k K R R M y)
  rwa [LinearEquiv.conjRingEquiv_apply_apply, LinearEquiv.symm_apply_apply] at h

/-- Under `AlgHom.liftEquiv` along `k → K → R`, subtracting the identity from the scalar-extended
action on `K ⊗[k] M` is nilpotent if and only if subtracting the identity from the original action
on `M` is nilpotent. -/
@[simp]
theorem isNilpotent_endOfPoint_liftEquiv_sub_one_iff
    {R : Type y} [CommRing R] [Algebra k R] [Algebra K R] [IsScalarTower k K R]
    (f : H →ₐ[k] R) :
    letI := Comodule.baseChange (R := k) (H := H) (M := M) K
    IsNilpotent (endOfPoint (K ⊗[k] M) (AlgHom.liftEquiv k K H R f) - 1) ↔
      IsNilpotent (endOfPoint M f - 1) := by
  let _ := Comodule.baseChange (R := k) (H := H) (M := M) K
  let e := (TensorProduct.AlgebraTensorModule.cancelBaseChange k K R R M).conjRingEquiv
  rw [← IsNilpotent.map_iff (f := e) e.injective, map_sub e, map_one e]
  simp [e]

end Coalgebra

section Bialgebra

variable {k : Type u} {H : Type v} {M : Type w} {K : Type x}
variable [CommSemiring k] [Semiring H] [Bialgebra k H] [CommSemiring K] [Algebra k K]
variable [AddCommMonoid M] [Module k M] [Comodule k H M]

-- Not `@[simp]`: `AlgHom.baseChangePointsMulEquiv_apply_ofConv` simplifies the left-hand side to
-- `isNilpotent_endOfPoint_liftEquiv_sub_one_iff`; kept for direct rewriting on `WithConv` points.
/-- Under `AlgHom.baseChangePointsMulEquiv` along `k → K → R`, subtracting the identity from the
scalar-extended action on `K ⊗[k] M` is nilpotent if and only if subtracting the identity from the
original action on `M` is nilpotent. -/
theorem isNilpotent_endOfPoint_baseChangePointsMulEquiv_sub_one_iff
    {R : Type y} [CommRing R] [Algebra k R] [Algebra K R] [IsScalarTower k K R]
    (g : WithConv (H →ₐ[k] R)) :
    letI := Comodule.baseChange (R := k) (H := H) (M := M) K
    IsNilpotent
        (endOfPoint (K ⊗[k] M) (AlgHom.baseChangePointsMulEquiv (K := K) g).ofConv - 1) ↔
      IsNilpotent (endOfPoint M g.ofConv - 1) := by
  rw [AlgHom.baseChangePointsMulEquiv_apply_ofConv, isNilpotent_endOfPoint_liftEquiv_sub_one_iff]

end Bialgebra

section HopfAlgebra

variable {k : Type u} {H : Type v} {M : Type w} {K : Type x}
variable [CommSemiring k] [Semiring H] [HopfAlgebra k H] [CommSemiring K] [Algebra k K]
variable [AddCommMonoid M] [Module k M] [Comodule k H M]

/-- The action of the base-changed point on the base-changed comodule is the original point's
scalar-extended action. -/
@[simp]
theorem basePointsRepresentation_baseChangePointsMulEquiv
    (g : WithConv (H →ₐ[k] K)) :
    letI := Comodule.baseChange (R := k) (H := H) (M := M) K
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

end HopfAlgebra

end TauCeti.Comodule

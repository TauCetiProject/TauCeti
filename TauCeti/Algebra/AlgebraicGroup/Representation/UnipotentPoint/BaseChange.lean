/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Ideal

/-!
# Unipotent points under base change

Under the base-change adjunction `AlgHom.baseChangePointsMulEquiv` along `k → K → R`, unipotence of
points is reflected in general and preserved for finite-type affine groups over fields.

Reflection requires no commutativity of `H`, field, finite-type, or perfectness hypotheses: for
every finitely generated `H`-comodule `M`, subtracting the identity from the action of the
base-changed point on `K ⊗[k] M` is nilpotent if and only if subtracting the identity from the
original point's action on `M` is nilpotent
(`TauCeti.Comodule.isNilpotent_endOfPoint_liftEquiv_sub_one_iff`).

For a finite-type affine group over a field `k` and a tower of field extensions `k → K → R`, choose
a faithful finite-dimensional `H`-comodule `M` (`TauCeti.Comodule.exists_isFaithful`). Its scalar
extension `K ⊗[k] M` remains faithful over `K ⊗[k] H`, so the unipotence-ideal criterion
(`TauCeti.Comodule.unipotenceIdeal_le_ker_iff_isUnipotentPoint`, which incorporates value-field
naturality to an algebraic closure) detects unipotence of the base-changed point directly over `R`
without assuming `k`, `K`, or `R` perfect.

The formal structure parallels
`TauCeti.Algebra.AlgebraicGroup.Representation.SemisimplePoint.BaseChange`, with value-field
naturality eliminating the perfectness hypothesis required in the semisimple case.

## Main declarations

* `TauCeti.HopfAlgebra.IsUnipotentPoint.of_baseChangePointsMulEquiv`: the base-change adjunction on
  points reflects unipotence for arbitrary Hopf algebras over commutative semirings.
* `TauCeti.HopfAlgebra.IsUnipotentPoint.baseChangePointsMulEquiv`: for finite-type coordinate Hopf
  algebras over fields, the base-change adjunction preserves unipotent points.
* `TauCeti.HopfAlgebra.isUnipotentPoint_baseChangePointsMulEquiv_iff`: unipotence of field-valued
  points is invariant under the base-change adjunction, with no perfectness assumption.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti

namespace HopfAlgebra

section Reflection

universe u v w

variable {k K : Type u} {H : Type v} {R : Type w}
variable [CommSemiring k] [Semiring H] [_root_.HopfAlgebra k H]
variable [CommSemiring K] [Algebra k K]
variable [CommRing R] [Algebra k R] [Algebra K R] [IsScalarTower k K R]

/-- The base-change adjunction on `R`-valued points along `k → K → R` reflects unipotence, with no
commutativity, field, finite-type, or perfectness assumptions. -/
theorem IsUnipotentPoint.of_baseChangePointsMulEquiv
    {g : WithConv (H →ₐ[k] R)}
    (hg : IsUnipotentPoint (AlgHom.baseChangePointsMulEquiv (K := K) g)) :
    IsUnipotentPoint g := by
  rw [isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one] at hg ⊢
  intro M
  let _ := Comodule.baseChange (R := k) (H := H) (M := M) K
  exact (Comodule.isNilpotent_endOfPoint_baseChangePointsMulEquiv_sub_one_iff (K := K) (M := M)
    g).mp (hg (FGComoduleCat.of (R := K) (C := K ⊗[k] H) (K ⊗[k] M)))

end Reflection

section FieldExtension

universe u

variable {k H K R : Type u} [Field k] [CommRing H] [_root_.HopfAlgebra k H]
variable [Algebra.FiniteType k H] [Field K] [Algebra k K]
variable [Field R] [Algebra k R] [Algebra K R] [IsScalarTower k K R]

attribute [local instance 1100] Module.Free.of_divisionRing

/-- For a finite-type coordinate Hopf algebra over a field `k` and a tower of field extensions
`k → K → R`, the base-change adjunction on points preserves unipotence. Neither `k`, `K`, nor `R`
is required to be perfect. -/
theorem IsUnipotentPoint.baseChangePointsMulEquiv
    {g : WithConv (H →ₐ[k] R)} (hg : IsUnipotentPoint g) :
    IsUnipotentPoint (AlgHom.baseChangePointsMulEquiv (K := K) g) := by
  have key (N : FGComoduleCat.{u, u, u} K (K ⊗[k] H))
      (hN : Comodule.IsFaithful (k := K) (H := K ⊗[k] H) (V := N))
      (g' : WithConv (K ⊗[k] H →ₐ[K] R)) :
      IsUnipotentPoint g' ↔ _root_.IsNilpotent (Comodule.endOfPoint N g'.ofConv - 1) := by
    rw [← Comodule.unipotenceIdeal_le_ker_iff_isUnipotentPoint N hN,
      Comodule.unipotenceIdeal_le_ker_iff_isUnipotent,
      LinearMap.GeneralLinearGroup.isUnipotent_ofLinearEquiv_iff,
      Comodule.pointsAction_toLinearMap]
  obtain ⟨M, hM⟩ := Comodule.exists_isFaithful (k := k) (H := H)
  let _ := Comodule.baseChange (R := k) (H := H) (M := M) K
  rw [key (FGComoduleCat.of (R := K) (C := K ⊗[k] H) (K ⊗[k] M))
    (Comodule.IsFaithful.baseChange (K := K) hM)]
  exact (Comodule.isNilpotent_endOfPoint_baseChangePointsMulEquiv_sub_one_iff (K := K) (M := M)
    g).mpr ((isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one g).mp hg M)

/-- Unipotence of field-valued points of a finite-type affine group is invariant under the
base-change adjunction along `k → K → R`, with no perfectness assumption on the fields. -/
@[simp]
theorem isUnipotentPoint_baseChangePointsMulEquiv_iff
    (g : WithConv (H →ₐ[k] R)) :
    IsUnipotentPoint (AlgHom.baseChangePointsMulEquiv (K := K) g) ↔
      IsUnipotentPoint g :=
  ⟨IsUnipotentPoint.of_baseChangePointsMulEquiv, IsUnipotentPoint.baseChangePointsMulEquiv⟩

end FieldExtension

end HopfAlgebra

end TauCeti

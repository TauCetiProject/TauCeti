/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.TensorProduct.Finite
import TauCeti.Algebra.AlgebraicGroup.Representation.Embedding
import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Faithful
import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Naturality

/-!
# Unipotent points under base change

Under the base-change adjunction `AlgHom.baseChangePointsMulEquiv` along `k → K → R`, unipotence of
points is reflected in general and preserved for finite-type affine groups over fields.

Reflection requires no field, finite-type, or perfectness hypotheses: for every finitely generated
`H`-comodule `M`, the action of the base-changed point on `K ⊗[k] M` conjugates across
`cancelBaseChange` to the original point's action on `M`, so nilpotence after subtracting the
identity transfers directly.

For a finite-type affine group over a field `k` and a tower of field extensions `k → K → R`,
preservation reduces by value-field naturality (`isUnipotentPoint_toConv_comp_iff`) to an algebraic
closure of `R`, which is perfect. Choosing a faithful finite-dimensional `H`-comodule `M`, its
scalar extension `K ⊗[k] M` remains faithful over `K ⊗[k] H`, so the faithful-representation
criterion detects unipotence of the base-changed point without assuming `k`, `K`, or `R` perfect.

The formal structure parallels
`TauCeti.Algebra.AlgebraicGroup.Representation.SemisimplePoint.BaseChange`, with value-field
naturality eliminating the perfectness hypothesis required in the semisimple case.

## Main declarations

* `TauCeti.HopfAlgebra.IsUnipotentPoint.of_baseChangePointsMulEquiv`: the base-change adjunction on
  points reflects unipotence over arbitrary commutative rings and semirings.
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

universe u v w x

variable {k : Type u} {H : Type v} {K : Type w} {R : Type x}
variable [CommSemiring k] [CommSemiring H] [_root_.HopfAlgebra k H]
variable [CommSemiring K] [Algebra k K]
variable [CommRing R] [Algebra k R] [Algebra K R] [IsScalarTower k K R]

private theorem isNilpotent_endOfPoint_baseChangePointsMulEquiv_sub_one_iff
    {M : Type*} [AddCommMonoid M] [Module k M] [Comodule k H M]
    (g : WithConv (H →ₐ[k] R)) :
    let _ := Comodule.baseChange (R := k) (H := H) (M := M) K
    _root_.IsNilpotent
        (Comodule.endOfPoint (K ⊗[k] M)
          (AlgHom.baseChangePointsMulEquiv (K := K) g).ofConv - 1) ↔
      _root_.IsNilpotent (Comodule.endOfPoint M g.ofConv - 1) := by
  let _ := Comodule.baseChange (R := k) (H := H) (M := M) K
  let e := (TensorProduct.AlgebraTensorModule.cancelBaseChange k K R R M).conjRingEquiv
  have hsub (f : Module.End R _) : e (f - 1) = e f - 1 := by ext x; simp [e]
  have heq :
      e ((Comodule.endOfPoint (K ⊗[k] M)
          (AlgHom.baseChangePointsMulEquiv (K := K) g).ofConv : Module.End R _) - 1) =
        (Comodule.endOfPoint M g.ofConv : Module.End R _) - 1 := by
    rw [hsub]; simp [e]
  have hmap :
      _root_.IsNilpotent
          (e ((Comodule.endOfPoint (K ⊗[k] M)
            (AlgHom.baseChangePointsMulEquiv (K := K) g).ofConv : Module.End R _) - 1)) ↔
        _root_.IsNilpotent
          ((Comodule.endOfPoint (K ⊗[k] M)
            (AlgHom.baseChangePointsMulEquiv (K := K) g).ofConv : Module.End R _) - 1) :=
    IsNilpotent.map_iff e.injective
  rw [heq] at hmap
  exact hmap.symm

end Reflection

section ReflectionPoint

universe u v w

variable {k K : Type u} {H : Type v} {R : Type w}
variable [CommSemiring k] [CommSemiring H] [_root_.HopfAlgebra k H]
variable [CommSemiring K] [Algebra k K]
variable [CommRing R] [Algebra k R] [Algebra K R] [IsScalarTower k K R]

/-- The base-change adjunction on `R`-valued points along `k → K → R` reflects unipotence, with no
field, finite-type, or perfectness assumptions. -/
theorem IsUnipotentPoint.of_baseChangePointsMulEquiv
    {g : WithConv (H →ₐ[k] R)}
    (hg : IsUnipotentPoint (AlgHom.baseChangePointsMulEquiv (K := K) g)) :
    IsUnipotentPoint g := by
  rw [isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one] at hg ⊢
  intro M
  let _ := Comodule.baseChange (R := k) (H := H) (M := M) K
  exact (isNilpotent_endOfPoint_baseChangePointsMulEquiv_sub_one_iff (K := K) (M := M) g).mp
    (hg (FGComoduleCat.of (R := K) (C := K ⊗[k] H) (K ⊗[k] M)))

end ReflectionPoint

section FieldExtension

universe u

variable {k H K R : Type u} [Field k] [CommRing H] [_root_.HopfAlgebra k H]
variable [Algebra.FiniteType k H] [Field K] [Algebra k K]
variable [Field R] [Algebra k R] [Algebra K R] [IsScalarTower k K R]

private theorem isUnipotentPoint_baseChangePointsMulEquiv_of_perfectField [PerfectField R]
    {g : WithConv (H →ₐ[k] R)} (hg : IsUnipotentPoint g) :
    IsUnipotentPoint (AlgHom.baseChangePointsMulEquiv (K := K) g) := by
  obtain ⟨M, _, b, hb⟩ := Comodule.exists_isClosedImmersion_coordinateGroupSchemeHom
    (k := k) (H := H)
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let _ : Module.Free k M := Module.Free.of_basis b
  let _ : Module.Finite k M := Module.Finite.of_basis b
  have hM : Comodule.IsFaithful (k := k) (H := H) (V := M) :=
    (Comodule.isFaithful_iff_isClosedImmersion_coordinateGroupSchemeHom b).2 hb
  let _ := Comodule.baseChange (R := k) (H := H) (M := M) K
  let MK := FGComoduleCat.of (R := K) (C := K ⊗[k] H) (K ⊗[k] M)
  apply (isUnipotentPoint_iff_isUnipotent_pointsAction_of_isFaithful
    MK (Comodule.IsFaithful.baseChange (K := K) hM) _).mpr
  rw [LinearMap.GeneralLinearGroup.isUnipotent_ofLinearEquiv_iff,
    Comodule.pointsAction_toLinearMap]
  exact (isNilpotent_endOfPoint_baseChangePointsMulEquiv_sub_one_iff (K := K) (M := M) g).mpr
    ((isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one g).mp hg
      (FGComoduleCat.of (R := k) (C := H) M))

/-- For a finite-type coordinate Hopf algebra over a field `k` and a tower of field extensions
`k → K → R`, the base-change adjunction on points preserves unipotence. Neither `k`, `K`, nor `R`
is required to be perfect. -/
theorem IsUnipotentPoint.baseChangePointsMulEquiv
    {g : WithConv (H →ₐ[k] R)} (hg : IsUnipotentPoint g) :
    IsUnipotentPoint (AlgHom.baseChangePointsMulEquiv (K := K) g) := by
  let φk : R →ₐ[k] AlgebraicClosure R := IsScalarTower.toAlgHom k R (AlgebraicClosure R)
  let φK : R →ₐ[K] AlgebraicClosure R := IsScalarTower.toAlgHom K R (AlgebraicClosure R)
  have hcomp :
      toConv (φK.comp (AlgHom.baseChangePointsMulEquiv (K := K) g).ofConv) =
        AlgHom.baseChangePointsMulEquiv (K := K) (toConv (φk.comp g.ofConv)) := by
    apply WithConv.ext
    apply Algebra.TensorProduct.ext_ring
    ext x
    simp [φK, φk, Algebra.smul_def]
  rw [← isUnipotentPoint_toConv_comp_iff _ φK, hcomp]
  exact isUnipotentPoint_baseChangePointsMulEquiv_of_perfectField
    ((isUnipotentPoint_toConv_comp_iff g φk).mpr hg)

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

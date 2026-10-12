/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Frobenius.Basic
public import TauCeti.LinearAlgebra.PerfectPairing.Basis
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.A2.Basic

/-!
# Self-injectivity of the preprojective algebra of `A₂`

The preprojective algebra of `A₂` is the arrow-ideal-square-zero quotient of the doubled path
algebra. It has a basis `TauCeti.preprojectiveA2Basis` consisting of the two vertex idempotents
and the two oppositely oriented arrows. The linear functional which is one on both arrows and zero
on the vertices gives a Frobenius pairing

```text
(x, y) ↦ φ (x * y).
```

In the displayed basis its Gram matrix is a permutation matrix: each basis element has a unique
right-dual basis element. The pairing is therefore perfect over every commutative ring. Over a
field, the general Frobenius criterion proves that both regular modules are injective. Together
with finite-dimensionality from
`TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.A2.Basic`, the `A₂` preprojective algebra is
a finite-dimensional self-injective algebra over every field.

## Main definitions

* `TauCeti.preprojectiveA2FrobeniusFunctional`: the functional taking both arrows to one.
* `TauCeti.preprojectiveA2FrobeniusPairing`: multiplication followed by that functional.
* `TauCeti.preprojectiveA2RightDualIndex`: the right-dual permutation of the displayed basis.

## Main results

* `TauCeti.isPerfPair_preprojectiveA2FrobeniusPairing`: the Frobenius pairing is perfect.
* `TauCeti.moduleInjective_preprojectiveAlgebra_A2`: the `A₂` preprojective algebra is
  left self-injective.
* `TauCeti.moduleInjective_op_preprojectiveAlgebra_A2`: the `A₂` preprojective algebra is
  right self-injective.

## References

See W. Crawley-Boevey, *Quiver algebras, weighted projective lines, and the Deligne--Simpson
problem*, Section 1, for the preprojective presentation, and C. M. Ringel,
*The preprojective algebra of a quiver*, for the Frobenius property in finite Dynkin type.
-/

public section

namespace TauCeti

universe w

section CommRing

variable (k : Type w) [CommRing k]

/-- The Frobenius functional on the `A₂` preprojective algebra: it is zero on the two vertex
idempotents and one on each of the two arrows. -/
noncomputable def preprojectiveA2FrobeniusFunctional :
    preprojectiveAlgebra k preprojectiveA2Quiver →ₗ[k] k :=
  (preprojectiveA2Basis k).constr k ![0, 0, 1, 1]

@[simp]
theorem preprojectiveA2FrobeniusFunctional_basis (i : Fin 4) :
    preprojectiveA2FrobeniusFunctional k (preprojectiveA2Basis k i) = ![0, 0, 1, 1] i :=
  (preprojectiveA2Basis k).constr_basis k ![0, 0, 1, 1] i

/-- Multiplication followed by `TauCeti.preprojectiveA2FrobeniusFunctional`, the Frobenius pairing
on the `A₂` preprojective algebra. -/
noncomputable def preprojectiveA2FrobeniusPairing :
    LinearMap.BilinForm k (preprojectiveAlgebra k preprojectiveA2Quiver) :=
  (LinearMap.mul k _).compr₂ (preprojectiveA2FrobeniusFunctional k)

@[simp]
theorem preprojectiveA2FrobeniusPairing_apply
    (x y : preprojectiveAlgebra k preprojectiveA2Quiver) :
    preprojectiveA2FrobeniusPairing k x y = preprojectiveA2FrobeniusFunctional k (x * y) := by
  rw [preprojectiveA2FrobeniusPairing, LinearMap.compr₂_apply, LinearMap.mul_apply']

/-- The permutation matching each element of `TauCeti.preprojectiveA2Basis` with its right dual
for the Frobenius pairing. -/
def preprojectiveA2RightDualIndex : Equiv.Perm (Fin 4) where
  toFun
    | 0 => 3
    | 1 => 2
    | 2 => 0
    | 3 => 1
  invFun
    | 0 => 2
    | 1 => 3
    | 2 => 1
    | 3 => 0
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The right-dual permutation evaluated on the four basis indices. -/
@[simp]
theorem preprojectiveA2RightDualIndex_apply (i : Fin 4) :
    preprojectiveA2RightDualIndex i = ![3, 2, 0, 1] i := by
  fin_cases i <;> rfl

/-- The inverse of the right-dual permutation evaluated on the four basis indices. -/
@[simp]
theorem preprojectiveA2RightDualIndex_symm_apply (i : Fin 4) :
    preprojectiveA2RightDualIndex.symm i = ![2, 3, 1, 0] i := by
  fin_cases i <;> rfl

/-- **The Gram matrix of the `A₂` Frobenius pairing is a permutation matrix.** -/
theorem preprojectiveA2FrobeniusPairing_basis (i j : Fin 4) :
    preprojectiveA2FrobeniusPairing k (preprojectiveA2Basis k i)
      (preprojectiveA2Basis k j) =
        if j = preprojectiveA2RightDualIndex i then 1 else 0 := by
  rw [preprojectiveA2FrobeniusPairing_apply, preprojectiveA2Basis_mul]
  fin_cases i <;> fin_cases j <;> simp

/-- **The `A₂` Frobenius pairing is perfect.** Its Gram matrix is a permutation matrix, so no
scalar needs to be inverted and a commutative base ring suffices. -/
instance isPerfPair_preprojectiveA2FrobeniusPairing :
    (preprojectiveA2FrobeniusPairing k).IsPerfPair :=
  (preprojectiveA2Basis k).isPerfPair_of_apply_eq_ite _ preprojectiveA2RightDualIndex
    (preprojectiveA2FrobeniusPairing_basis k)

/-- **The displayed functional makes the `A₂` preprojective algebra Frobenius.** -/
theorem isFrobeniusFunctional_preprojectiveA2FrobeniusFunctional :
    (preprojectiveA2FrobeniusFunctional k).IsFrobeniusFunctional :=
  LinearMap.isFrobeniusFunctional_iff.mpr
    (isPerfPair_preprojectiveA2FrobeniusPairing k).nondegenerate

end CommRing

section Field

variable (k : Type w) [Field k]

/-- **The preprojective algebra of `A₂` is left self-injective.** -/
theorem moduleInjective_preprojectiveAlgebra_A2 :
    Module.Injective (preprojectiveAlgebra k preprojectiveA2Quiver)
      (preprojectiveAlgebra k preprojectiveA2Quiver) :=
  (isFrobeniusFunctional_preprojectiveA2FrobeniusFunctional k).moduleInjective_self

/-- **The preprojective algebra of `A₂` is right self-injective.** -/
theorem moduleInjective_op_preprojectiveAlgebra_A2 :
    Module.Injective (preprojectiveAlgebra k preprojectiveA2Quiver)ᵐᵒᵖ
      (preprojectiveAlgebra k preprojectiveA2Quiver) :=
  (isFrobeniusFunctional_preprojectiveA2FrobeniusFunctional k).moduleInjective_op_self

end Field

end TauCeti

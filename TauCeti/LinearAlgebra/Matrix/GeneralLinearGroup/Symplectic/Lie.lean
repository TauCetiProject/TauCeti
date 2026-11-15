/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic

/-!
# Linear terms of symplectic root subgroups

Each standard symplectic root subgroup has the form `1 + c X`, with `X` a single
matrix unit for a long root and a signed pair of matrix units for a short root.
`RootSubgroupIndex.tangentMatrix` records this linear term in paired coordinates.
Its parameter can be recovered from a matrix entry over any commutative ring,
including in characteristic two. These formulas identify the normalized Lie vectors
of the represented root subgroups.

The matrix conventions are those of `GLSymplecticFin.RootSubgroupIndex.hom`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §24.6.
* R. W. Carter, *Simple Groups of Lie Type* (1972), §11.3.
-/

public section

namespace TauCeti.GLSymplecticFin.RootSubgroupIndex

open Matrix

variable {m : ℕ} {R : Type*} [CommRing R]

/-- The linear term of a standard symplectic root subgroup in paired coordinates.
The difference roots have opposite signs in the two diagonal blocks; the sum roots
have symmetric entries in an off-diagonal block. -/
def tangentMatrix (root : RootSubgroupIndex m) :
    R →ₗ[R] Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R :=
  match root with
  | .positiveLong i => singleLinearMap R (.inl i) (.inr i)
  | .negativeLong i => singleLinearMap R (.inr i) (.inl i)
  | .difference i j _ =>
      singleLinearMap R (.inl i) (.inl j) - singleLinearMap R (.inr j) (.inr i)
  | .positiveSum i j _ =>
      singleLinearMap R (.inl i) (.inr j) + singleLinearMap R (.inl j) (.inr i)
  | .negativeSum i j _ =>
      singleLinearMap R (.inr i) (.inl j) + singleLinearMap R (.inr j) (.inl i)

/-- The linear term of a positive long root. -/
@[simp]
theorem tangentMatrix_positiveLong (i : Fin m) (c : R) :
    (positiveLong i).tangentMatrix c = single (.inl i) (.inr i) c := (rfl)

/-- The linear term of a negative long root. -/
@[simp]
theorem tangentMatrix_negativeLong (i : Fin m) (c : R) :
    (negativeLong i).tangentMatrix c = single (.inr i) (.inl i) c := (rfl)

/-- The linear term of a difference root. -/
@[simp]
theorem tangentMatrix_difference (i j : Fin m) (hij : i ≠ j) (c : R) :
    (difference i j hij).tangentMatrix c =
      single (.inl i) (.inl j) c - single (.inr j) (.inr i) c := (rfl)

/-- The linear term of a positive sum root. -/
@[simp]
theorem tangentMatrix_positiveSum (i j : Fin m) (hij : i < j) (c : R) :
    (positiveSum i j hij).tangentMatrix c =
      single (.inl i) (.inr j) c + single (.inl j) (.inr i) c := (rfl)

/-- The linear term of a negative sum root. -/
@[simp]
theorem tangentMatrix_negativeSum (i j : Fin m) (hij : i < j) (c : R) :
    (negativeSum i j hij).tangentMatrix c =
      single (.inr i) (.inl j) c + single (.inr j) (.inl i) c := (rfl)

/-- Entrywise application of an additive homomorphism preserves the linear term.
This applies to derivatives of coordinate functions as well as to changes of coefficients. -/
@[simp]
theorem map_tangentMatrix {S : Type*} [CommRing S] (root : RootSubgroupIndex m)
    (f : R →+ S) (c : R) :
    (root.tangentMatrix c).map f = root.tangentMatrix (f c) := by
  cases root <;>
    simp only [tangentMatrix_positiveLong, tangentMatrix_negativeLong, tangentMatrix_difference,
      tangentMatrix_positiveSum, tangentMatrix_negativeSum, Matrix.map_add f f.map_add,
      Matrix.map_sub f f.map_sub, Matrix.map_single]

/-- The parameter of the linear term is recoverable from one of its entries. -/
theorem tangentMatrix_injective (root : RootSubgroupIndex m) :
    Function.Injective (root.tangentMatrix (R := R)) := by
  intro c d h
  cases root with
  | positiveLong i => simpa using congrFun (congrFun h (.inl i)) (.inr i)
  | negativeLong i => simpa using congrFun (congrFun h (.inr i)) (.inl i)
  | difference i j hij =>
      simpa using congrFun (congrFun h (.inl i)) (.inl j)
  | positiveSum i j hij =>
      simpa [hij.ne] using congrFun (congrFun h (.inl i)) (.inr j)
  | negativeSum i j hij =>
      simpa [hij.ne] using congrFun (congrFun h (.inr i)) (.inl j)

/-- The root one-parameter subgroup is the identity plus its linear term.
This includes all long and short roots, over every commutative ring. -/
theorem hom_apply_matrix (root : RootSubgroupIndex m) (c : Multiplicative R) :
    (((root.hom c : GLSymplecticFin m R) : GL (Fin (m + m)) R) :
        Matrix (Fin (m + m)) (Fin (m + m)) R).submatrix finSumFinEquiv finSumFinEquiv =
      1 + root.tangentMatrix c.toAdd := by
  cases root with
  | positiveLong i =>
      simp only [hom_positiveLong, positiveLongRootTransvectionHom_apply,
        coe_positiveLongRootTransvectionUnit,
        coe_transvectionUnit,
        Matrix.transvection, tangentMatrix_positiveLong, submatrix_add, Pi.add_apply,
        submatrix_one_equiv,
        submatrix_single_equiv, Equiv.symm_apply_apply]
  | negativeLong i =>
      simp only [hom_negativeLong, negativeLongRootTransvectionHom_apply,
        coe_negativeLongRootTransvectionUnit,
        coe_transvectionUnit,
        Matrix.transvection, tangentMatrix_negativeLong, submatrix_add, Pi.add_apply,
        submatrix_one_equiv,
        submatrix_single_equiv, Equiv.symm_apply_apply]
  | difference i j hij =>
      rw [hom_difference, differenceShortRootHom_apply,
        coe_differenceShortRootUnit_eq_one_add_single_sub_single]
      simp only [tangentMatrix_difference, submatrix_add, submatrix_sub, Pi.add_apply, Pi.sub_apply,
        submatrix_one_equiv,
        submatrix_single_equiv, Equiv.symm_apply_apply]
      abel
  | positiveSum i j hij =>
      rw [hom_positiveSum, positiveSumShortRootHom_apply, coe_positiveSumShortRootUnit,
        Units.val_mul, coe_transvectionUnit, coe_transvectionUnit]
      have hz : (single (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inr j)) c.toAdd :
          Matrix (Fin (m + m)) (Fin (m + m)) R) *
          single (finSumFinEquiv (.inl j)) (finSumFinEquiv (.inr i)) c.toAdd = 0 := by
        apply single_mul_single_of_ne
        exact finSumFinEquiv_inr_ne_inl j j
      simp only [Matrix.transvection, add_mul, mul_add, one_mul, mul_one, hz, add_zero,
        tangentMatrix_positiveSum, submatrix_add, Pi.add_apply,
        submatrix_one_equiv, submatrix_single_equiv,
        Equiv.symm_apply_apply]
      abel
  | negativeSum i j hij =>
      rw [hom_negativeSum, negativeSumShortRootHom_apply, coe_negativeSumShortRootUnit,
        Units.val_mul, coe_transvectionUnit, coe_transvectionUnit]
      have hz : (single (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) c.toAdd :
          Matrix (Fin (m + m)) (Fin (m + m)) R) *
          single (finSumFinEquiv (.inr j)) (finSumFinEquiv (.inl i)) c.toAdd = 0 := by
        apply single_mul_single_of_ne
        exact finSumFinEquiv_inl_ne_inr j j
      simp only [Matrix.transvection, add_mul, mul_add, one_mul, mul_one, hz, add_zero,
        tangentMatrix_negativeSum, submatrix_add, Pi.add_apply,
        submatrix_one_equiv, submatrix_single_equiv,
        Equiv.symm_apply_apply]
      abel

end TauCeti.GLSymplecticFin.RootSubgroupIndex

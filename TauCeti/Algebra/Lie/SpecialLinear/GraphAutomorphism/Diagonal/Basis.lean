/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.GraphAutomorphism.Diagonal.Fixed
public import TauCeti.LinearAlgebra.FixedSubmodule.Permutation

/-!
# An orbit basis of the native fixed diagonal submodule

Simple-coroot orbit sums form a basis of the trace-zero diagonal matrices fixed
by the pinned type-A graph automorphism. Their coordinates are initial diagonal
sums. The construction works over every commutative ring, without inverting two.
-/

public noncomputable section

namespace TauCeti

open LieAlgebra.SpecialLinear

attribute [local instance 100] LieRing.ofAssociativeRing

variable (r : ℕ) (A : Type*) [CommRing A]

/-- Simple-coroot orbit sums form a basis of the actual fixed diagonal submodule. -/
def typeASpecialLinearFixedDiagonalBasis :
    Module.Basis (Quotient (Equiv.Perm.SameCycle.setoid (Fin.revPerm : Equiv.Perm (Fin r))))
      A (typeASpecialLinearFixedDiagonal r A) :=
  (Equiv.Perm.permutationFixedBasis (R := A) (Fin.revPerm : Equiv.Perm (Fin r))).map
    (typeASpecialLinearFixedDiagonalEquiv r A).symm

/-- The coefficient of the orbit containing an index is the corresponding initial diagonal sum. -/
@[simp]
theorem typeASpecialLinearFixedDiagonalBasis_repr
    (X : typeASpecialLinearFixedDiagonal r A) (i : Fin r) :
    (typeASpecialLinearFixedDiagonalBasis r A).repr X (Quotient.mk _ i) =
      Fin.partialSum (fun j : Fin r ↦ X.val.val j.castSucc j.castSucc) i.succ := by
  rw [typeASpecialLinearFixedDiagonalBasis, Module.Basis.map_repr]
  exact (Equiv.Perm.permutationFixedBasis_repr _ _ i).trans
    (typeASpecialLinearFixedDiagonalEquiv_apply r A X i)

/-- Each fixed diagonal basis vector is the sum of native coroots in its reversal orbit. -/
theorem typeASpecialLinearFixedDiagonalBasis_eq_sum
    [DecidableEq (Quotient (Equiv.Perm.SameCycle.setoid
      (Fin.revPerm : Equiv.Perm (Fin r))))]
    (o : Quotient (Equiv.Perm.SameCycle.setoid (Fin.revPerm : Equiv.Perm (Fin r)))) :
    (typeASpecialLinearFixedDiagonalBasis r A o).val =
      ∑ i ∈ Finset.univ.filter (fun i : Fin r ↦ Quotient.mk _ i = o),
        singleSubSingle i.castSucc i.succ (1 : A) := by
  rw [typeASpecialLinearFixedDiagonalBasis, Module.Basis.map_apply,
    typeASpecialLinearFixedDiagonalEquiv_symm_apply, specialLinearCorootEquiv_symm_val]
  simp only [Equiv.Perm.permutationFixedBasis_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_filter]

end TauCeti

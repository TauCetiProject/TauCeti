/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Norm.Transitivity

/-!
# Discriminants in algebra towers

This file proves the standard discriminant identity for the basis of a composite algebra obtained
from bases of the two steps in an algebra tower.

## Main result

* `Module.Basis.discr_smulTower`: the discriminant of `b.smulTower c` is the appropriate power of
  the discriminant of `b`, multiplied by the norm of the discriminant of `c`.

## Mathematical context

The discriminant of a basis is the determinant of its trace pairing. In a tower, the trace pairing
on the product basis factors through the trace pairing of the lower basis and the relative Gram
matrix associated to the relative trace pairing, yielding the displayed power and norm factors.

## References

* Neukirch, *Algebraic Number Theory*, Chapter III, §2, gives the corresponding discriminant
  identity for towers of number fields.
-/

public section

open Matrix Module

namespace Module.Basis

/-- The trace matrix of the product basis factors through the lower trace matrix and the Gram
matrix associated to the relative trace pairing. This is the matrix identity underlying the tower
formula for discriminants. -/
theorem traceMatrix_smulTower {K : Type*} [CommRing K]
    {L M : Type*} [CommRing L] [CommRing M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι K L) (c : Module.Basis κ L M) :
    Algebra.traceMatrix K (b.smulTower c) =
      (Matrix.blockDiagonal fun _ : κ => Algebra.traceMatrix K b) *
        LinearMap.toMatrix (b.smulTower c) (b.smulTower c)
          ((Matrix.toLin c c (Algebra.traceMatrix L c)).restrictScalars K) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [LinearMap.toMatrix_apply, Finsupp.single_apply, Matrix.mul_apply,
    Matrix.blockDiagonal_apply, ← Finset.univ_product_univ, Finset.sum_product,
    ← Algebra.trace_trace_of_basis b c]
  simpa [Matrix.mulVec, dotProduct, mul_comm, mul_left_comm] using
    (congrFun (Algebra.traceMatrix_of_basis_mulVec b
      (b j * Algebra.trace L M (c k * c l))) i).symm

/-- The discriminant of the product basis in a tower is the discriminant of the lower basis,
raised to the degree of the upper step, times the norm of the upper basis discriminant. -/
@[simp] theorem discr_smulTower {K : Type*} [CommRing K]
    {L M : Type*} [CommRing L] [CommRing M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι K L) (c : Module.Basis κ L M) :
    Algebra.discr K (b.smulTower c) =
      Algebra.discr K b ^ Fintype.card κ * Algebra.norm K (Algebra.discr L c) := by
  have := Module.Free.of_basis b
  have := Module.Free.of_basis c
  simp [Algebra.discr_def, traceMatrix_smulTower, Matrix.det_blockDiagonal,
    LinearMap.det_restrictScalars]

end Module.Basis

end

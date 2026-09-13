/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Discriminant

/-!
# Discriminants in field towers

This file proves the standard discriminant identity for the basis of a composite extension
obtained from bases of the two steps in a field tower.

## Main result

* `Module.Basis.discr_smulTower`: the discriminant of `b.smulTower c` is the appropriate power of
  the discriminant of `b`, multiplied by the norm of the discriminant of `c`.

## Mathematical context

The discriminant of a basis is the determinant of its trace pairing. In a tower, the trace
pairing on the product basis factors through the trace pairing of the lower basis and the relative
Gram matrix associated to the relative trace pairing, yielding the displayed power and norm
factors.

## References

* [TauCetiRoadmap, NumberFieldArithmetic, Layer 4.4](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/NumberFieldArithmetic/Suggested.lean#L693-L702)
  specifies this basis-level tower formula.
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
    _root_.Algebra.traceMatrix K (b.smulTower c) =
      (Matrix.blockDiagonal fun _ : κ => _root_.Algebra.traceMatrix K b) *
        LinearMap.toMatrix (b.smulTower c) (b.smulTower c)
          ((Matrix.toLin c c (_root_.Algebra.traceMatrix L c)).restrictScalars K) := by
  classical
  let C : Matrix κ κ L := _root_.Algebra.traceMatrix L c
  let f : M →ₗ[L] M := Matrix.toLin c c C
  let D : Matrix (ι × κ) (ι × κ) K :=
    Matrix.blockDiagonal fun _ : κ => _root_.Algebra.traceMatrix K b
  -- The target contains the expanded expressions, while the local abbreviations are needed
  -- below for the coefficient calculation; this `change` unfolds only those let-bound terms.
  change _root_.Algebra.traceMatrix K (b.smulTower c) =
    D * LinearMap.toMatrix (b.smulTower c) (b.smulTower c) (f.restrictScalars K)
  have hcoeff (i j : ι) (k l : κ) :
      LinearMap.toMatrix (b.smulTower c) (b.smulTower c) (f.restrictScalars K)
          (i, k) (j, l) = b.repr (b j * C k l) i := by
    simp only [LinearMap.toMatrix_apply, Basis.smulTower_apply, Basis.smulTower_repr,
      LinearMap.coe_restrictScalars, Matrix.toLin_self, map_smul, smul_eq_mul, map_sum,
      Basis.repr_self, Finsupp.smul_single, mul_one, Finsupp.coe_smul,
      Finsupp.coe_finsetSum, Pi.smul_apply, Finset.sum_apply, f]
    rw [Finset.sum_eq_single k]
    · simp
    · intro x _ hx
      rw [Finsupp.single_eq_of_ne hx.symm]
    · simp
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [_root_.Algebra.traceMatrix_apply, Basis.smulTower_apply,
    _root_.Algebra.traceForm_apply, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
    ← _root_.Algebra.trace_trace_of_basis b c, Matrix.mul_apply,
    ← Finset.univ_product_univ, Matrix.blockDiagonal_apply, hcoeff, D, C,
    Finset.sum_product, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte]
  simpa [Matrix.mulVec, dotProduct, Basis.equivFun_apply, mul_comm, mul_left_comm,
    mul_assoc] using
    (congrFun (_root_.Algebra.traceMatrix_of_basis_mulVec b
      (b j * _root_.Algebra.trace L M (c k * c l))) i).symm

/-- The discriminant of the product basis in a tower is the discriminant of the lower basis,
raised to the degree of the upper step, times the norm of the upper basis discriminant. -/
@[simp] theorem discr_smulTower {K : Type*} [CommRing K]
    {L M : Type*} [CommRing L] [CommRing M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι K L) (c : Module.Basis κ L M) :
    Algebra.discr K (b.smulTower c) =
      Algebra.discr K b ^ Fintype.card κ * Algebra.norm K (Algebra.discr L c) := by
  classical
  let _ := Module.Free.of_basis b
  let _ := Module.Free.of_basis c
  let C : Matrix κ κ L := _root_.Algebra.traceMatrix L c
  rw [_root_.Algebra.discr_def, traceMatrix_smulTower, Matrix.det_mul]
  simp only [Matrix.det_blockDiagonal, Finset.prod_const, Finset.card_univ]
  rw [← _root_.Algebra.discr_def, LinearMap.det_toMatrix,
    LinearMap.det_restrictScalars]
  -- `rw` leaves the determinant of `Matrix.toLin c c C` inside the norm. The target below is
  -- definitionally equal after unfolding the local abbreviation `C`, and exposes that wrapper
  -- so the public `det_toLin` conversion can be applied next.
  change _root_.Algebra.discr K b ^ Fintype.card κ *
      _root_.Algebra.norm K (LinearMap.det (Matrix.toLin c c C)) = _
  have hC : C.det = _root_.Algebra.discr L c := by
    simpa [C] using (_root_.Algebra.discr_def L c).symm
  rw [LinearMap.det_toLin, hC]

end Module.Basis

end

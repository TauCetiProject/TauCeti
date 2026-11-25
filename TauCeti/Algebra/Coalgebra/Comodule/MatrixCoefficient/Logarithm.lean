/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Matrix
public import TauCeti.RingTheory.Nilpotent.Log
public import Mathlib.RingTheory.Bialgebra.Primitive

/-!
# Logarithms of coefficient matrices over cocommutative bialgebras

For a comodule with a finite basis over a bialgebra `C`, comultiplication sends the coefficient
matrix `X` to the product of `X ⊗ 1` and `1 ⊗ X` in matrices over `C ⊗ C`. When `C` is
cocommutative, that is, for representations of a commutative group, the two factors commute, so
for unipotent `X` the finite logarithm turns this product into a sum: every entry of `log X` is
primitive. In group terms, the logarithm of a unipotent representation of a commutative group is
an additive map into the matrices. This is how primitive elements, the additive characters, are
produced from a unipotent representation in characteristic zero.

## Main declarations

* `TauCeti.Comodule.isPrimitiveElem_log_coefficientMatrix`: the entries of the logarithm of a
  coefficient matrix over a cocommutative bialgebra are primitive.

## References

* J. S. Milne, *Algebraic Groups* (2017), §14.c.
-/

public section

open TensorProduct Module

namespace TauCeti.Comodule

variable {R C M ι : Type*} [CommSemiring R] [Ring C] [Bialgebra R C] [Coalgebra.IsCocomm R C]
  [Algebra ℚ C] [AddCommMonoid M] [Module R M] [Comodule R C M] [Fintype ι] [DecidableEq ι]

/-- **The entries of the logarithm of a unipotent coefficient matrix over a cocommutative
bialgebra are primitive.** Comultiplication sends the coefficient matrix `X` to the product of
the commuting matrices `X ⊗ 1` and `1 ⊗ X`, so it sends `log X` to `log X ⊗ 1 + 1 ⊗ log X`. In
group terms: the logarithm of a unipotent representation of a commutative group is additive.
When `X - 1` is not nilpotent, `log X` is the junk value `0`, whose entries are primitive too. -/
theorem isPrimitiveElem_log_coefficientMatrix (b : Basis ι R M) (i j : ι) :
    Bialgebra.IsPrimitiveElem R (IsNilpotent.log (coefficientMatrix (C := C) b) i j) := by
  set X := coefficientMatrix (C := C) b
  by_cases hb : IsNilpotent (X - 1)
  swap
  · have h0 : IsNilpotent.log X = 0 := by
      rw [IsNilpotent.log_def, Nat.eq_zero_of_not_pos (mt isNilpotent_of_pos_nilpotencyClass hb),
        Finset.range_zero, Finset.sum_empty]
    simp [h0]
  let L : Matrix ι ι C →+* Matrix ι ι (C ⊗[R] C) :=
    (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := C) (B := C)).toRingHom.mapMatrix
  let Rt : Matrix ι ι C →+* Matrix ι ι (C ⊗[R] C) :=
    (Algebra.TensorProduct.includeRight (R := R) (A := C) (B := C)).toRingHom.mapMatrix
  let D : Matrix ι ι C →+* Matrix ι ι (C ⊗[R] C) :=
    (Bialgebra.comulAlgHom R C).toRingHom.mapMatrix
  -- Comultiplication is the product of `X ⊗ 1` and `1 ⊗ X`, in either order.
  have hD : D X = L X * Rt X := by
    ext i j
    simp [D, L, Rt, X, Matrix.mul_apply, Algebra.TensorProduct.tmul_mul_tmul]
  have hcomm : Commute (L X) (Rt X) := by
    rw [Commute, SemiconjBy, ← hD]
    ext i j
    have h := Coalgebra.comm_comul R (X i j)
    simp only [X, comul_coefficientMatrix_eq_sum, map_sum, TensorProduct.comm_tmul] at h
    simp [D, L, Rt, X, Matrix.mul_apply, Algebra.TensorProduct.tmul_mul_tmul, ← h]
  have hL : IsNilpotent (L X - 1) := by simpa using hb.map L
  have hR : IsNilpotent (Rt X - 1) := by simpa using hb.map Rt
  have hlog : D (IsNilpotent.log X) = L (IsNilpotent.log X) + Rt (IsNilpotent.log X) := by
    rw [IsNilpotent.map_log hb D, hD, IsNilpotent.log_mul_of_commute hcomm hL hR,
      IsNilpotent.map_log hb L, IsNilpotent.map_log hb Rt]
  refine Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul.mpr ?_
  have h := congrFun (congrFun hlog i) j
  simp only [D, L, Rt, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Bialgebra.comulAlgHom_apply,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply] at h
  rw [h, add_comm]

end TauCeti.Comodule


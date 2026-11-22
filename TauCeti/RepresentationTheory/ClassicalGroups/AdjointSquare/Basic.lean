/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The traceless symmetric product on the adjoint representation of SL₃

The bilinear product on trace-zero matrices is the anticommutator with its
scalar part removed. Its coefficient is `2 / 3`, since the identity matrix
has trace three. Together with the native Lie bracket, it supplies the two
products whose trace transposes give the octet embeddings.

This advances the explicit adjoint-square maps in the worked examples of
the TensorProductCombinatorics roadmap, intention 2823.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 15.
* Jeromie Beasley, `yang-mills-lean`, `AdjointWitnessSU3.lean`, the commutator
  and anticommutator trace forms.
-/

public section

namespace TauCeti.AdjointSquare

open Matrix

variable {K : Type*} [Field K]

/-- The traceless part of the anticommutator of two three-by-three matrices. -/
@[expose] def symmetricProductMatrix (X Y : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 3) (Fin 3) K :=
  X * Y + Y * X - ((2 / 3 : K) * trace (X * Y)) • 1

/-- The scalar correction removes the full trace of the anticommutator. -/
@[simp]
theorem trace_symmetricProductMatrix [NeZero (3 : K)] (X Y : Matrix (Fin 3) (Fin 3) K) :
    trace (symmetricProductMatrix X Y) = 0 := by
  simp only [symmetricProductMatrix, trace_sub, trace_add, trace_smul, trace_one,
    Fintype.card_fin, trace_mul_comm Y X, smul_eq_mul]
  field_simp [NeZero.ne (3 : K)]
  ring

/-- The traceless anticommutator is symmetric in its arguments. -/
theorem symmetricProductMatrix_comm (X Y : Matrix (Fin 3) (Fin 3) K) :
    symmetricProductMatrix X Y = symmetricProductMatrix Y X := by
  simp only [symmetricProductMatrix, trace_mul_comm Y X, add_comm]

/-- Additivity in the first argument. -/
theorem symmetricProductMatrix_add_left (X Y Z : Matrix (Fin 3) (Fin 3) K) :
    symmetricProductMatrix (X + Y) Z =
      symmetricProductMatrix X Z + symmetricProductMatrix Y Z := by
  simp only [symmetricProductMatrix, add_mul, mul_add, trace_add, mul_add, add_smul]
  abel

/-- Scalar compatibility in the first argument. -/
theorem symmetricProductMatrix_smul_left (a : K) (X Y : Matrix (Fin 3) (Fin 3) K) :
    symmetricProductMatrix (a • X) Y = a • symmetricProductMatrix X Y := by
  simp only [symmetricProductMatrix, Matrix.smul_mul, Matrix.mul_smul, trace_smul, smul_add,
    smul_sub, smul_smul]
  congr 2
  ring

/-- Additivity in the second argument. -/
theorem symmetricProductMatrix_add_right (X Y Z : Matrix (Fin 3) (Fin 3) K) :
    symmetricProductMatrix X (Y + Z) =
      symmetricProductMatrix X Y + symmetricProductMatrix X Z := by
  rw [symmetricProductMatrix_comm X, symmetricProductMatrix_add_left,
    symmetricProductMatrix_comm Y, symmetricProductMatrix_comm Z]

/-- Scalar compatibility in the second argument. -/
theorem symmetricProductMatrix_smul_right (a : K) (X Y : Matrix (Fin 3) (Fin 3) K) :
    symmetricProductMatrix X (a • Y) = a • symmetricProductMatrix X Y := by
  rw [symmetricProductMatrix_comm X, symmetricProductMatrix_smul_left,
    symmetricProductMatrix_comm Y]

/-- The symmetric product as a bilinear map on Mathlib's actual trace-zero Lie algebra. -/
@[expose] def symmetricProduct [NeZero (3 : K)] :
    LieAlgebra.SpecialLinear.sl (Fin 3) K →ₗ[K]
      LieAlgebra.SpecialLinear.sl (Fin 3) K →ₗ[K]
        LieAlgebra.SpecialLinear.sl (Fin 3) K where
  toFun X :=
    { toFun := fun Y => ⟨symmetricProductMatrix X.val Y.val, trace_symmetricProductMatrix _ _⟩
      map_add' := fun Y Z => Subtype.ext (symmetricProductMatrix_add_right X.val Y.val Z.val)
      map_smul' := fun a Y => Subtype.ext (symmetricProductMatrix_smul_right a X.val Y.val) }
  map_add' X Y := LinearMap.ext fun Z =>
    Subtype.ext (symmetricProductMatrix_add_left X.val Y.val Z.val)
  map_smul' a X := LinearMap.ext fun Y =>
    Subtype.ext (symmetricProductMatrix_smul_left a X.val Y.val)

/-- The bilinear map has the advertised matrix formula. -/
@[simp]
theorem coe_symmetricProduct [NeZero (3 : K)] (X Y : LieAlgebra.SpecialLinear.sl (Fin 3) K) :
    (symmetricProduct X Y).val = symmetricProductMatrix X.val Y.val := rfl

/-- Symmetry holds on the native adjoint carrier. -/
theorem symmetricProduct_comm [NeZero (3 : K)] (X Y : LieAlgebra.SpecialLinear.sl (Fin 3) K) :
    symmetricProduct X Y = symmetricProduct Y X :=
  Subtype.ext (symmetricProductMatrix_comm _ _)

/-- The product commutes with invertible conjugation, hence with the SL₃ action. -/
theorem symmetricProductMatrix_conj (g : (Matrix (Fin 3) (Fin 3) K)ˣ)
    (X Y : Matrix (Fin 3) (Fin 3) K) :
    symmetricProductMatrix ((g : Matrix (Fin 3) (Fin 3) K) * X *
      ((g⁻¹ : _) : Matrix (Fin 3) (Fin 3) K))
      ((g : Matrix (Fin 3) (Fin 3) K) * Y * ((g⁻¹ : _) : Matrix (Fin 3) (Fin 3) K)) =
      (g : Matrix (Fin 3) (Fin 3) K) * symmetricProductMatrix X Y *
        ((g⁻¹ : _) : Matrix (Fin 3) (Fin 3) K) := by
  have hmul (A B : Matrix (Fin 3) (Fin 3) K) :
      ((g : Matrix (Fin 3) (Fin 3) K) * A * ((g⁻¹ : _) : Matrix (Fin 3) (Fin 3) K)) *
        ((g : Matrix (Fin 3) (Fin 3) K) * B * ((g⁻¹ : _) : Matrix (Fin 3) (Fin 3) K)) =
        (g : Matrix (Fin 3) (Fin 3) K) * (A * B) * ((g⁻¹ : _) : Matrix (Fin 3) (Fin 3) K) := by
    simp [Matrix.mul_assoc]
  simp only [symmetricProductMatrix, hmul, trace_units_conj, mul_sub, mul_add,
    sub_mul, add_mul, Matrix.mul_smul]
  simp [Matrix.mul_assoc]

/-- Restriction of the symmetric product identity to determinant-one matrices. -/
theorem symmetricProductMatrix_sl_conj (g : SpecialLinearGroup (Fin 3) K)
    (X Y : Matrix (Fin 3) (Fin 3) K) :
    symmetricProductMatrix ((g : Matrix (Fin 3) (Fin 3) K) * X *
      ((g⁻¹ : _) : Matrix (Fin 3) (Fin 3) K))
      ((g : Matrix (Fin 3) (Fin 3) K) * Y * ((g⁻¹ : _) : Matrix (Fin 3) (Fin 3) K)) =
      (g : Matrix (Fin 3) (Fin 3) K) * symmetricProductMatrix X Y *
        ((g⁻¹ : _) : Matrix (Fin 3) (Fin 3) K) := by
  simpa only [← map_inv, SpecialLinearGroup.coe_GL_coe_matrix] using
    symmetricProductMatrix_conj (SpecialLinearGroup.toGL g) X Y

/-- The commutator commutes with the conjugation action of SL₃. -/
theorem commutator_sl_conj {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (g : SpecialLinearGroup ι R)
    (X Y : Matrix ι ι R) :
    ((g : Matrix ι ι R) * X * (g⁻¹ : SpecialLinearGroup ι R)) *
        ((g : Matrix ι ι R) * Y * (g⁻¹ : SpecialLinearGroup ι R)) -
      ((g : Matrix ι ι R) * Y * (g⁻¹ : SpecialLinearGroup ι R)) *
        ((g : Matrix ι ι R) * X * (g⁻¹ : SpecialLinearGroup ι R)) =
      (g : Matrix ι ι R) * (X * Y - Y * X) *
        (g⁻¹ : SpecialLinearGroup ι R) := by
  have hu (u : (Matrix ι ι R)ˣ) :
      ((u : Matrix ι ι R) * X * ((u⁻¹ : _) : Matrix ι ι R)) *
          ((u : Matrix ι ι R) * Y * ((u⁻¹ : _) : Matrix ι ι R)) -
        ((u : Matrix ι ι R) * Y * ((u⁻¹ : _) : Matrix ι ι R)) *
          ((u : Matrix ι ι R) * X * ((u⁻¹ : _) : Matrix ι ι R)) =
        (u : Matrix ι ι R) * (X * Y - Y * X) *
          ((u⁻¹ : _) : Matrix ι ι R) := by
    simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  simpa only [← map_inv, SpecialLinearGroup.coe_GL_coe_matrix] using
    hu (SpecialLinearGroup.toGL g)

/-- The trace pairing has zero left radical on the actual trace-zero carrier. -/
theorem trace_pairing_nondegenerate [NeZero (3 : K)]
    (X : LieAlgebra.SpecialLinear.sl (Fin 3) K)
    (h : ∀ Y : LieAlgebra.SpecialLinear.sl (Fin 3) K, trace (X.val * Y.val) = 0) : X = 0 := by
  apply Subtype.ext
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro Z
  change trace (X.val * Z) = trace ((0 : Matrix (Fin 3) (Fin 3) K) * Z)
  have hX : trace X.val = 0 := X.property
  have hZ : trace (Z - (trace Z / 3) • (1 : Matrix (Fin 3) (Fin 3) K)) = 0 := by
    simp only [trace_sub, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]
    field_simp [NeZero.ne (3 : K)]
    ring
  have htest := h ⟨Z - (trace Z / 3) • (1 : Matrix (Fin 3) (Fin 3) K), hZ⟩
  simpa only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, trace_sub,
    trace_smul, hX, smul_zero, sub_zero, zero_mul, trace_zero] using htest

end TauCeti.AdjointSquare

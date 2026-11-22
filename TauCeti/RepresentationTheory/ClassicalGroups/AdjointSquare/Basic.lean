/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Algebra.Ring.Action.ConjAct
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ConjAct

/-!
# The traceless symmetric product on the adjoint representation of SL₃

The bilinear product on trace-zero three-by-three matrices is the anticommutator with its
scalar part removed. Its coefficient is `2 / 3`, since the identity matrix has trace three.
Together with the Lie bracket, it supplies the two products whose trace transposes give the
two octet copies in the tensor square of `sl₃`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lectures 12 and 13.
* Jeromie Beasley, `yang-mills-lean`, `AdjointWitnessSU3.lean`, the commutator
  and anticommutator trace forms.
-/

public section

namespace TauCeti.AdjointSquare

open Matrix

variable {K : Type*} [Field K]

/-- The traceless part of the anticommutator of two three-by-three matrices. -/
def symmetricProductMatrix (X Y : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 3) (Fin 3) K :=
  X * Y + Y * X - ((2 / 3 : K) * trace (X * Y)) • 1

/-- The traceless anticommutator has the displayed formula. -/
theorem symmetricProductMatrix_apply (X Y : Matrix (Fin 3) (Fin 3) K) :
    symmetricProductMatrix X Y =
      X * Y + Y * X - ((2 / 3 : K) * trace (X * Y)) • 1 :=
  (rfl)

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
def symmetricProduct [NeZero (3 : K)] :
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
    (symmetricProduct X Y).val = symmetricProductMatrix X.val Y.val :=
  (rfl)

/-- Symmetry holds on the native adjoint carrier. -/
theorem symmetricProduct_comm [NeZero (3 : K)] (X Y : LieAlgebra.SpecialLinear.sl (Fin 3) K) :
    symmetricProduct X Y = symmetricProduct Y X :=
  Subtype.ext (symmetricProductMatrix_comm _ _)

/-- The product commutes with invertible conjugation, hence with the `SL₃` action. -/
theorem symmetricProductMatrix_conj (g : (Matrix (Fin 3) (Fin 3) K)ˣ)
    (X Y : Matrix (Fin 3) (Fin 3) K) :
    symmetricProductMatrix ((g : Matrix (Fin 3) (Fin 3) K) * X *
      ((g⁻¹ : _) : Matrix (Fin 3) (Fin 3) K))
      ((g : Matrix (Fin 3) (Fin 3) K) * Y * ((g⁻¹ : _) : Matrix (Fin 3) (Fin 3) K)) =
      (g : Matrix (Fin 3) (Fin 3) K) * symmetricProductMatrix X Y *
        ((g⁻¹ : _) : Matrix (Fin 3) (Fin 3) K) := by
  have hsmul (A : Matrix (Fin 3) (Fin 3) K) :
      (g : Matrix (Fin 3) (Fin 3) K) * A * ((g⁻¹ : _) : Matrix (Fin 3) (Fin 3) K) =
        ConjAct.toConjAct g • A := by
    simp [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]
  have htrace : trace (ConjAct.toConjAct g • (X * Y)) = trace (X * Y) := by
    rw [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]
    exact trace_units_conj g (X * Y)
  have hscalar (c : K) :
      ConjAct.toConjAct g • (c • (1 : Matrix (Fin 3) (Fin 3) K)) =
        c • (1 : Matrix (Fin 3) (Fin 3) K) := by
    -- The conjugation action fixes scalars, since it fixes `1`.
    rw [smul_comm, MulDistribMulAction.smul_one]
  rw [hsmul X, hsmul Y, hsmul (symmetricProductMatrix X Y)]
  simp only [symmetricProductMatrix, ← smul_mul', smul_add, smul_sub, htrace, hscalar]

/-- Restriction of the symmetric product identity to determinant-one matrices. -/
theorem symmetricProductMatrix_sl_conj (g : SpecialLinearGroup (Fin 3) K)
    (X Y : Matrix (Fin 3) (Fin 3) K) :
    symmetricProductMatrix ((g : Matrix (Fin 3) (Fin 3) K) * X *
      ((g⁻¹ : _) : Matrix (Fin 3) (Fin 3) K))
      ((g : Matrix (Fin 3) (Fin 3) K) * Y * ((g⁻¹ : _) : Matrix (Fin 3) (Fin 3) K)) =
      (g : Matrix (Fin 3) (Fin 3) K) * symmetricProductMatrix X Y *
        ((g⁻¹ : _) : Matrix (Fin 3) (Fin 3) K) := by
  -- Conjugation by `g` is conjugation by its image in `GL`.
  have h (A : Matrix (Fin 3) (Fin 3) K) :
      ((SpecialLinearGroup.toGL g : (Matrix (Fin 3) (Fin 3) K)ˣ) : Matrix (Fin 3) (Fin 3) K) * A *
          (((SpecialLinearGroup.toGL g)⁻¹ : _) : Matrix (Fin 3) (Fin 3) K) =
        (g : Matrix (Fin 3) (Fin 3) K) * A *
          ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    simp [← map_inv, SpecialLinearGroup.coe_GL_coe_matrix]
  simp only [← h]
  exact symmetricProductMatrix_conj (SpecialLinearGroup.toGL g) X Y

end TauCeti.AdjointSquare

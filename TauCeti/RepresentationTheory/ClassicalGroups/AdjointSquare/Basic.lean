/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import TauCeti.LinearAlgebra.Matrix.TracelessAnticommutator

/-!
# The traceless symmetric product on the adjoint representation of SL₃

`Matrix.tracelessAnticommutator` removes the scalar part of the anticommutator of two
three-by-three matrices. Restricted to trace-zero matrices it is bilinear, and together with
the Lie bracket it supplies the two products whose trace transposes give the two octet copies
in the tensor square of `sl₃`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lectures 12 and 13.
* Jeromie Beasley, `yang-mills-lean`, `AdjointWitnessSU3.lean`, the commutator
  and anticommutator trace forms.
-/

public section

namespace TauCeti.AdjointSquare

open Matrix

variable {K : Type*} [Field K]

/-- The symmetric product as a bilinear map on Mathlib's actual trace-zero Lie algebra. -/
def symmetricProduct [NeZero (3 : K)] :
    LieAlgebra.SpecialLinear.sl (Fin 3) K →ₗ[K]
      LieAlgebra.SpecialLinear.sl (Fin 3) K →ₗ[K]
        LieAlgebra.SpecialLinear.sl (Fin 3) K where
  toFun X :=
    { toFun := fun Y =>
        ⟨tracelessAnticommutator X.val Y.val, trace_tracelessAnticommutator _ _⟩
      map_add' := fun Y Z =>
        Subtype.ext (tracelessAnticommutator_add_right X.val Y.val Z.val)
      map_smul' := fun a Y =>
        Subtype.ext (tracelessAnticommutator_smul_right a X.val Y.val) }
  map_add' X Y := LinearMap.ext fun Z =>
    Subtype.ext (tracelessAnticommutator_add_left X.val Y.val Z.val)
  map_smul' a X := LinearMap.ext fun Y =>
    Subtype.ext (tracelessAnticommutator_smul_left a X.val Y.val)

/-- The bilinear map has the advertised matrix formula. -/
@[simp]
theorem coe_symmetricProduct [NeZero (3 : K)] (X Y : LieAlgebra.SpecialLinear.sl (Fin 3) K) :
    (symmetricProduct X Y).val = tracelessAnticommutator X.val Y.val :=
  (rfl)

/-- Symmetry holds on the native adjoint carrier. -/
theorem symmetricProduct_comm [NeZero (3 : K)] (X Y : LieAlgebra.SpecialLinear.sl (Fin 3) K) :
    symmetricProduct X Y = symmetricProduct Y X :=
  Subtype.ext (tracelessAnticommutator_comm _ _)

/-- The symmetric product commutes with conjugation by a determinant-one matrix. -/
theorem tracelessAnticommutator_sl_conj (g : SpecialLinearGroup (Fin 3) K)
    (X Y : Matrix (Fin 3) (Fin 3) K) :
    tracelessAnticommutator ((g : Matrix (Fin 3) (Fin 3) K) * X *
      ((g⁻¹ : _) : Matrix (Fin 3) (Fin 3) K))
      ((g : Matrix (Fin 3) (Fin 3) K) * Y * ((g⁻¹ : _) : Matrix (Fin 3) (Fin 3) K)) =
      (g : Matrix (Fin 3) (Fin 3) K) * tracelessAnticommutator X Y *
        ((g⁻¹ : _) : Matrix (Fin 3) (Fin 3) K) := by
  -- Conjugation by `g` is conjugation by its image in `GL`.
  have h (A : Matrix (Fin 3) (Fin 3) K) :
      ((SpecialLinearGroup.toGL g : (Matrix (Fin 3) (Fin 3) K)ˣ) : Matrix (Fin 3) (Fin 3) K) * A *
          (((SpecialLinearGroup.toGL g)⁻¹ : _) : Matrix (Fin 3) (Fin 3) K) =
        (g : Matrix (Fin 3) (Fin 3) K) * A *
          ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    simp [← map_inv, SpecialLinearGroup.coe_GL_coe_matrix]
  simp only [← h]
  exact tracelessAnticommutator_conj (SpecialLinearGroup.toGL g) X Y

end TauCeti.AdjointSquare

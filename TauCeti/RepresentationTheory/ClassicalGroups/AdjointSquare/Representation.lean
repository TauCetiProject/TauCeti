/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.AdjointSquare.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.Restriction
public import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The conjugation representation on the trace-zero matrices

The standard representation of SL₃ induces its conjugation representation on
endomorphisms. Transport through `Matrix.toLin'` identifies this with matrix
conjugation. Its trace-zero subrepresentation has Mathlib's actual special
linear Lie algebra as its carrier.

These representations supply the carriers of the explicit adjoint-square maps
in the worked examples of the TensorProductCombinatorics roadmap, intention 2823.
-/

public section

namespace TauCeti.AdjointSquare

open Matrix

variable (K : Type*) [Field K]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Matrix conjugation, transported from the endomorphisms of the standard SL₃ module. -/
def matrixAdjointRep :
    Representation K (SpecialLinearGroup (Fin 3) K) (Matrix (Fin 3) (Fin 3) K) :=
  ((Matrix.toLin' : Matrix (Fin 3) (Fin 3) K ≃ₗ[K]
    Module.End K (Fin 3 → K)).symm.conjRingEquiv).toMonoidHom.comp
      (Representation.linHom (stdSLRep K 3) (stdSLRep K 3))

/-- The transported action is conjugation by the determinant-one matrix. -/
@[simp]
theorem matrixAdjointRep_apply (g : SpecialLinearGroup (Fin 3) K)
    (X : Matrix (Fin 3) (Fin 3) K) :
    matrixAdjointRep K g X =
      (g : Matrix (Fin 3) (Fin 3) K) * X * (g⁻¹ : SpecialLinearGroup (Fin 3) K) := by
  apply (Matrix.toLin' : Matrix (Fin 3) (Fin 3) K ≃ₗ[K]
    Module.End K (Fin 3 → K)).injective
  -- The endomorphism-ring transport conjugates by the matrix-to-linear-map equivalence.
  change Matrix.toLin' (Matrix.toLin'.symm
    ((Representation.linHom (stdSLRep K 3) (stdSLRep K 3)) g (Matrix.toLin' X))) = _
  rw [LinearEquiv.apply_symm_apply, Representation.linHom_apply,
    Matrix.toLin'_mul, Matrix.toLin'_mul]
  simp only [stdSLRep_apply, Matrix.toLin'_apply', LinearMap.comp_assoc]

/-- Conjugation preserves the trace-zero submodule. -/
def tracelessSubrep : Subrepresentation (matrixAdjointRep K) where
  toSubmodule := (LieAlgebra.SpecialLinear.sl (Fin 3) K).toSubmodule
  apply_mem_toSubmodule g X hX := by
    change trace (matrixAdjointRep K g X) = 0
    change trace X = 0 at hX
    rw [matrixAdjointRep_apply]
    simpa only [← map_inv, SpecialLinearGroup.coe_GL_coe_matrix] using
      (trace_units_conj (SpecialLinearGroup.toGL g) X).trans hX

/-- The adjoint representation on Mathlib's native trace-zero Lie algebra. -/
def adjointRep :
    Representation K (SpecialLinearGroup (Fin 3) K)
      (LieAlgebra.SpecialLinear.sl (Fin 3) K) :=
  (tracelessSubrep K).toRepresentation

/-- The native adjoint carrier has the expected matrix conjugation action. -/
@[simp]
theorem coe_adjointRep_apply (g : SpecialLinearGroup (Fin 3) K)
    (X : LieAlgebra.SpecialLinear.sl (Fin 3) K) :
    (adjointRep K g X).val =
      (g : Matrix (Fin 3) (Fin 3) K) * X.val * (g⁻¹ : SpecialLinearGroup (Fin 3) K) := by
  -- Restriction to a subrepresentation does not change the underlying matrix action.
  change matrixAdjointRep K g X.val = _
  exact matrixAdjointRep_apply K g X.val

end TauCeti.AdjointSquare

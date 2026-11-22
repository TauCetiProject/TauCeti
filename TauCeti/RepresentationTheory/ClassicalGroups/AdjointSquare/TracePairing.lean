/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.AdjointSquare.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.AdjointSquare.Representation
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Trace self-duality of the trace-zero three-by-three matrices

The bilinear form `tr(XY)` on the native special-linear carrier is symmetric
and nondegenerate. Mathlib's `BilinForm.toDual` supplies its canonical linear
equivalence with the dual. This is the pairing needed to transpose the two
products in the adjoint-square worked example of TensorProductCombinatorics.
-/

@[expose] public section

namespace TauCeti.AdjointSquare

open Matrix

variable {K : Type*} [Field K]

/-- The trace pairing on Mathlib's native special-linear carrier. -/
def traceForm : LinearMap.BilinForm K (LieAlgebra.SpecialLinear.sl (Fin 3) K) where
  toFun X :=
    { toFun Y := trace (X.val * Y.val)
      map_add' Y Z := by simp [Matrix.mul_add, trace_add]
      map_smul' a Y := by simp [trace_smul] }
  map_add' X Y := by ext Z; simp [Matrix.add_mul, trace_add]
  map_smul' a X := by ext Y; simp [trace_smul]

/-- Evaluation is the trace of the product. -/
@[simp]
theorem traceForm_apply (X Y : LieAlgebra.SpecialLinear.sl (Fin 3) K) :
    traceForm X Y = trace (X.val * Y.val) := rfl

/-- Cyclicity of trace makes the pairing symmetric. -/
theorem traceForm_comm (X Y : LieAlgebra.SpecialLinear.sl (Fin 3) K) :
    traceForm X Y = traceForm Y X := by
  exact trace_mul_comm X.val Y.val

/-- Both radicals of the trace pairing vanish. -/
theorem traceForm_nondegenerate [NeZero (3 : K)] :
    (traceForm (K := K)).Nondegenerate := by
  constructor
  · exact trace_pairing_nondegenerate
  · intro Y h
    apply trace_pairing_nondegenerate Y
    intro X
    rw [trace_mul_comm]
    exact h X

/-- The trace pairing identifies the adjoint carrier with its linear dual. -/
noncomputable def traceDual [NeZero (3 : K)] :
    LieAlgebra.SpecialLinear.sl (Fin 3) K ≃ₗ[K]
      Module.Dual K (LieAlgebra.SpecialLinear.sl (Fin 3) K) :=
  traceForm.toDual traceForm_nondegenerate

/-- The dual functional associated to `X` evaluates as `tr(XY)`. -/
@[simp]
theorem traceDual_apply [NeZero (3 : K)] (X Y : LieAlgebra.SpecialLinear.sl (Fin 3) K) :
    traceDual X Y = trace (X.val * Y.val) := rfl

/-- The trace pairing is invariant under the native adjoint representation. -/
theorem traceForm_adjointRep (g : SpecialLinearGroup (Fin 3) K)
    (X Y : LieAlgebra.SpecialLinear.sl (Fin 3) K) :
    traceForm (adjointRep K g X) (adjointRep K g Y) = traceForm X Y := by
  simp only [traceForm_apply, coe_adjointRep_apply]
  have h (u : (Matrix (Fin 3) (Fin 3) K)ˣ) :
      trace (((u : Matrix (Fin 3) (Fin 3) K) * X.val * ((u⁻¹ : _) : Matrix (Fin 3) (Fin 3) K)) *
        ((u : Matrix (Fin 3) (Fin 3) K) * Y.val * ((u⁻¹ : _) : Matrix (Fin 3) (Fin 3) K))) =
      trace (X.val * Y.val) := by
    simpa [Matrix.mul_assoc] using trace_units_conj u (X.val * Y.val)
  simpa only [← map_inv, SpecialLinearGroup.coe_GL_coe_matrix] using h (SpecialLinearGroup.toGL g)

/-- The trace pairing gives an equivariant self-duality of the adjoint representation. -/
noncomputable def traceDualEquiv [NeZero (3 : K)] :
    (adjointRep K).Equiv (adjointRep K).dual :=
  Representation.Equiv.mk traceDual fun g => by
    ext X Y
    change traceForm (adjointRep K g X) Y = traceForm X (adjointRep K g⁻¹ Y)
    have h := traceForm_adjointRep g X (adjointRep K g⁻¹ Y)
    simpa only [Representation.self_inv_apply] using h

end TauCeti.AdjointSquare

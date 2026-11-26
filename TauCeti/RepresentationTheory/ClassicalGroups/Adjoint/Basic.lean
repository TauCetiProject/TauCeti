/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.TraceForm
public import TauCeti.RepresentationTheory.InvariantForm
public import TauCeti.RepresentationTheory.ClassicalGroups.Restriction
public import Mathlib.Algebra.Lie.Classical
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Ring.Action.ConjAct
import Mathlib.LinearAlgebra.Matrix.ToLin
import TauCeti.Algebra.Lie.GeneralLinear.Basic
import TauCeti.Data.Fintype.Fin
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ConjAct

/-!
# The adjoint representation of the special linear group

Conjugation on matrices is the representation induced by the standard representation of
`SL n` on endomorphisms, transported along `Matrix.toLin'`. The trace-zero matrices form
an invariant submodule, and that submodule is Mathlib's special linear Lie algebra.

The trace form of `gl n`, restricted to this submodule, is symmetric and invariant under
conjugation over a commutative ring.
Over a field in which the matrix size is nonzero, the trace form identifies the adjoint
representation with its dual.
-/

public section

namespace TauCeti.SLAdjoint

open Matrix
open LieAlgebra.SpecialLinear (traceForm traceForm_apply traceForm_nondegenerate)
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

section

variable (K : Type*) [CommRing K] (n : ℕ)

/-- Matrix conjugation, transported from the endomorphisms of the standard module of `SL n`. -/
def matrixAdjointRep :
    Representation K (SpecialLinearGroup (Fin n) K) (Matrix (Fin n) (Fin n) K) :=
  ((Matrix.toLin' : Matrix (Fin n) (Fin n) K ≃ₗ[K]
    Module.End K (Fin n → K)).symm.conjAlgEquiv K).toAlgHom.toMonoidHom.comp
      (Representation.linHom (stdSLRep K n) (stdSLRep K n))

/-- The transported action is conjugation by the determinant-one matrix. -/
@[simp]
theorem matrixAdjointRep_apply (g : SpecialLinearGroup (Fin n) K)
    (X : Matrix (Fin n) (Fin n) K) :
    matrixAdjointRep K n g X =
      (g : Matrix (Fin n) (Fin n) K) * X * (g⁻¹ : SpecialLinearGroup (Fin n) K) := by
  apply (Matrix.toLin' : Matrix (Fin n) (Fin n) K ≃ₗ[K]
    Module.End K (Fin n → K)).injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
  simp [matrixAdjointRep, LinearEquiv.conjAlgEquiv_apply, Representation.linHom_apply,
    stdSLRep_apply, ← Matrix.toLin'_apply', LinearMap.comp_assoc]

/-- Conjugation preserves the trace-zero submodule. -/
def tracelessSubrep : Subrepresentation (matrixAdjointRep K n) where
  toSubmodule := (LieAlgebra.SpecialLinear.sl (Fin n) K).toSubmodule
  apply_mem_toSubmodule g X hX := by
    rw [LieSubalgebra.mem_toSubmodule,
    LieAlgebra.SpecialLinear.mem_sl_iff] at hX ⊢
    rwa [matrixAdjointRep_apply, SpecialLinearGroup.conj_eq_units_smul,
      ConjAct.toConjAct_toGL_smul, ConjAct.trace_specialLinearGroup_smul]

/-- The underlying submodule consists of the trace-zero matrices. -/
@[simp] theorem tracelessSubrep_toSubmodule :
    (tracelessSubrep K n).toSubmodule = (LieAlgebra.SpecialLinear.sl (Fin n) K).toSubmodule :=
  (rfl)

/-- A matrix belongs to the adjoint subrepresentation precisely when its trace vanishes. -/
theorem mem_tracelessSubrep_iff (X : Matrix (Fin n) (Fin n) K) :
    X ∈ (tracelessSubrep K n).toSubmodule ↔ X.trace = 0 := by
  rw [tracelessSubrep_toSubmodule, LieSubalgebra.mem_toSubmodule,
    LieAlgebra.SpecialLinear.mem_sl_iff]

/-- The adjoint representation on Mathlib's trace-zero Lie algebra. -/
def adjointRep :
    Representation K (SpecialLinearGroup (Fin n) K)
      (LieAlgebra.SpecialLinear.sl (Fin n) K) :=
  (tracelessSubrep K n).toRepresentation

/-- The adjoint representation acts by matrix conjugation. -/
@[simp]
theorem coe_adjointRep_apply (g : SpecialLinearGroup (Fin n) K)
    (X : LieAlgebra.SpecialLinear.sl (Fin n) K) :
    (adjointRep K n g X).val =
      (g : Matrix (Fin n) (Fin n) K) * X.val * (g⁻¹ : SpecialLinearGroup (Fin n) K) := by
  rw [← matrixAdjointRep_apply K n g X.val, adjointRep]
  symm
  -- Transfer reflexivity of the restricted action to the underlying matrix equality.
  apply (Subrepresentation.toRepresentation_apply_coe (ρ' := tracelessSubrep K n)
    (g := g) (v := X)).mp
  rfl

/-- Simultaneous conjugation preserves the restricted trace pairing. -/
@[simp high]
theorem traceForm_adjointRep (g : SpecialLinearGroup (Fin n) K)
    (X Y : LieAlgebra.SpecialLinear.sl (Fin n) K) :
    traceForm K (Fin n) (adjointRep K n g X) (adjointRep K n g Y) = traceForm K (Fin n) X Y := by
  simp only [traceForm_apply, coe_adjointRep_apply, SpecialLinearGroup.trace_mul_conj]

/-- The restricted trace form is invariant under the adjoint action. -/
theorem isInvariantForm_traceForm :
    TauCeti.Representation.IsInvariantForm (adjointRep K n) (traceForm K (Fin n)) :=
  TauCeti.Representation.isInvariantForm_iff_isIsometry.mpr fun g =>
    TauCeti.BilinForm.isIsometry_iff.mpr (traceForm_adjointRep K n g)

end

section

variable (K : Type*) [Field K] (n : ℕ)

/-- The trace pairing is an equivariant self-duality of the adjoint representation. -/
noncomputable def traceDualEquiv [NeZero (n : K)] :
    (adjointRep K n).Equiv (adjointRep K n).dual := by
  have hcard : (Fintype.card (Fin n) : K) ≠ 0 := by simpa using NeZero.ne (n : K)
  exact (isInvariantForm_traceForm K n).equivDual
    (traceForm_nondegenerate K (Fin n) (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hcard))

/-- Evaluation of the equivariant self-duality is the trace of the matrix product. -/
@[simp] theorem traceDualEquiv_apply [NeZero (n : K)]
    (X Y : LieAlgebra.SpecialLinear.sl (Fin n) K) :
    traceDualEquiv K n X Y = trace (X.val * Y.val) := by
  rw [traceDualEquiv, TauCeti.Representation.IsInvariantForm.equivDual_apply, traceForm_apply]

end

end TauCeti.SLAdjoint

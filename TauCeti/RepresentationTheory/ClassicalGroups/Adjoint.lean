/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.TraceForm
public import TauCeti.RepresentationTheory.ClassicalGroups.Restriction
public import Mathlib.Algebra.Lie.Classical
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.Algebra.Ring.Action.ConjAct
import Mathlib.LinearAlgebra.Matrix.ToLin
import TauCeti.Algebra.Lie.GeneralLinear.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ConjAct

/-!
# The adjoint representation of the special linear group

Conjugation on matrices is the representation induced by the standard representation of
`SL n` on endomorphisms, transported along `Matrix.toLin'`. The trace-zero matrices form
an invariant submodule, and that submodule is Mathlib's special linear Lie algebra.

The trace form of `gl n`, restricted to this submodule, is symmetric and invariant under
conjugation over a commutative ring. The Lie bracket is equivariant for every `n`.
Over a field in which the matrix size is nonzero, the trace form identifies the adjoint
representation with its dual.
-/

public section

namespace TauCeti.SLAdjoint

open Matrix
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

section

variable (K : Type*) [CommRing K] (n : ℕ)

/-- Matrix conjugation, transported from the endomorphisms of the standard module of `SL n`. -/
def matrixAdjointRep :
    Representation K (SpecialLinearGroup (Fin n) K) (Matrix (Fin n) (Fin n) K) :=
  ((Matrix.toLin' : Matrix (Fin n) (Fin n) K ≃ₗ[K]
    Module.End K (Fin n → K)).symm.conjRingEquiv).toMonoidHom.comp
      (Representation.linHom (stdSLRep K n) (stdSLRep K n))

/-- The transported action is conjugation by the determinant-one matrix. -/
@[simp]
theorem matrixAdjointRep_apply (g : SpecialLinearGroup (Fin n) K)
    (X : Matrix (Fin n) (Fin n) K) :
    matrixAdjointRep K n g X =
      (g : Matrix (Fin n) (Fin n) K) * X * (g⁻¹ : SpecialLinearGroup (Fin n) K) := by
  apply (Matrix.toLin' : Matrix (Fin n) (Fin n) K ≃ₗ[K]
    Module.End K (Fin n → K)).injective
  -- Unfold the transport through `Matrix.toLin'` and `Representation.linHom`.
  -- After `toLin'` is applied, both sides are the same composite endomorphism;
  -- the transport itself has no separate rewrite.
  change Matrix.toLin' (Matrix.toLin'.symm
    ((Representation.linHom (stdSLRep K n) (stdSLRep K n)) g (Matrix.toLin' X))) = _
  rw [LinearEquiv.apply_symm_apply, Representation.linHom_apply,
    Matrix.toLin'_mul, Matrix.toLin'_mul]
  simp only [stdSLRep_apply, Matrix.toLin'_apply', LinearMap.comp_assoc]

/-- Conjugation preserves the trace-zero submodule. -/
def tracelessSubrep : Subrepresentation (matrixAdjointRep K n) where
  toSubmodule := (LieAlgebra.SpecialLinear.sl (Fin n) K).toSubmodule
  apply_mem_toSubmodule g X hX := by
    rw [LieSubalgebra.mem_toSubmodule,
    LieAlgebra.SpecialLinear.mem_sl_iff] at hX ⊢
    rw [matrixAdjointRep_apply]
    simpa only [ConjAct.specialLinearGroup_smul_def, ConjAct.ofConjAct_toConjAct] using
      (ConjAct.trace_specialLinearGroup_smul (ConjAct.toConjAct g) X).trans hX

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
  -- `Subrepresentation.coe_toRepresentation_apply` is `rfl`, so the coercion to the
  -- ambient representation has no syntactic occurrence for `rw`.
  change matrixAdjointRep K n g (X : Matrix (Fin n) (Fin n) K) = _
  exact matrixAdjointRep_apply K n g X

/-- Simultaneous conjugation preserves the restricted trace pairing. -/
@[simp high]
theorem traceForm_adjointRep (g : SpecialLinearGroup (Fin n) K)
    (X Y : LieAlgebra.SpecialLinear.sl (Fin n) K) :
    traceForm K n (adjointRep K n g X) (adjointRep K n g Y) = traceForm K n X Y := by
  simp only [traceForm_apply, coe_adjointRep_apply]
  simpa only [SpecialLinearGroup.coe_inv] using SpecialLinearGroup.trace_mul_conj g X.val Y.val

/-- The Lie bracket as an equivariant map out of the tensor square. -/
noncomputable def alternatingProductMap :
    ((adjointRep K n).tprod (adjointRep K n)).IntertwiningMap (adjointRep K n) where
  toLinearMap :=
    TensorProduct.lift (LieAlgebra.ad K (LieAlgebra.SpecialLinear.sl (Fin n) K)).toLinearMap
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro X Y
    rw [Representation.tprod_apply, LinearMap.comp_apply, TensorProduct.map_tmul,
      TensorProduct.lift.tmul, LinearMap.comp_apply, TensorProduct.lift.tmul]
    apply Subtype.ext
    -- `LieAlgebra.ad` is the bracket, so `lift` on a pure tensor is definitionally `⁅·, ·⁆`.
    change ⁅adjointRep K n g X, adjointRep K n g Y⁆.val =
      (adjointRep K n g ⁅X, Y⁆).val
    simp only [LieAlgebra.SpecialLinear.sl_bracket, coe_adjointRep_apply]
    rw [SpecialLinearGroup.conj_eq_units_smul, SpecialLinearGroup.conj_eq_units_smul,
      SpecialLinearGroup.conj_eq_units_smul, smul_sub, smul_mul', smul_mul']

/-- On a simple tensor the alternating intertwiner is the commutator. -/
@[simp]
theorem alternatingProductMap_tmul (X Y : LieAlgebra.SpecialLinear.sl (Fin n) K) :
    alternatingProductMap K n (X ⊗ₜ[K] Y) = ⁅X, Y⁆ :=
  (rfl)

/-- Swapping the tensor factors negates the alternating intertwiner. -/
theorem alternatingProductMap_comm
    (T : LieAlgebra.SpecialLinear.sl (Fin n) K ⊗[K]
      LieAlgebra.SpecialLinear.sl (Fin n) K) :
    alternatingProductMap K n (TensorProduct.comm K _ _ T) =
      -alternatingProductMap K n T := by
  have h : (alternatingProductMap K n).toLinearMap.comp (TensorProduct.comm K _ _).toLinearMap =
      -(alternatingProductMap K n).toLinearMap := by
    apply TensorProduct.ext'
    intro X Y
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.comm_tmul]
    -- `toLinearMap` is `TensorProduct.lift` of the bracket, and `lift.tmul` is `rfl`,
    -- so after `comm_tmul` there is no `lift` to rewrite.
    change ⁅Y, X⁆ = -⁅X, Y⁆
    exact (lie_skew Y X).symm
  exact LinearMap.congr_fun h T

end

section

variable (K : Type*) [Field K] (n : ℕ)

/-- The trace pairing is an equivariant self-duality of the adjoint representation. -/
noncomputable def traceDualEquiv [NeZero (n : K)] :
    (adjointRep K n).Equiv (adjointRep K n).dual :=
  Representation.Equiv.mk (traceDual K n) fun g => by
    ext X Y
    change traceDual K n (adjointRep K n g X) Y = traceDual K n X (adjointRep K n g⁻¹ Y)
    rw [traceDual_apply, traceDual_apply, ← traceForm_apply, ← traceForm_apply]
    have h := traceForm_adjointRep K n g X (adjointRep K n g⁻¹ Y)
    simpa only [Representation.self_inv_apply] using h

/-- Evaluation of the equivariant self-duality is the trace of the matrix product. -/
@[simp] theorem traceDualEquiv_apply [NeZero (n : K)]
    (X Y : LieAlgebra.SpecialLinear.sl (Fin n) K) :
    traceDualEquiv K n X Y = trace (X.val * Y.val) := traceDual_apply K n X Y

end

end TauCeti.SLAdjoint

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
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import TauCeti.Algebra.Lie.GeneralLinear.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ConjAct

/-!
# The adjoint representation of the special linear group

Conjugation on matrices is the representation induced by the standard representation of
`SL n` on endomorphisms, transported along `Matrix.toLin'`. The trace-zero matrices form
an invariant submodule, and that submodule is Mathlib's special linear Lie algebra.

The trace form of `gl n`, restricted to this submodule, is symmetric and invariant under
conjugation. It is nondegenerate when the matrix size is nonzero in the scalar field.
The Lie bracket is then an equivariant map on the tensor square for every `n`.
-/

public section

namespace TauCeti

open Matrix
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

variable (K : Type*) [Field K] (n : ℕ)

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
    rw [LieSubalgebra.mem_toSubmodule, LieAlgebra.SpecialLinear.mem_sl_iff] at hX ⊢
    rw [matrixAdjointRep_apply]
    -- `SL` conjugation is the `ConjAct` action, whose trace is invariant.
    have hsmul :
        (g : Matrix (Fin n) (Fin n) K) * X * (g⁻¹ : SpecialLinearGroup (Fin n) K) =
          ConjAct.toConjAct g • X := by
      simp [ConjAct.specialLinearGroup_smul_def, ConjAct.ofConjAct_toConjAct]
    rw [hsmul]
    exact (ConjAct.trace_specialLinearGroup_smul (ConjAct.toConjAct g) X).trans hX

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

/-- The trace pairing on the special linear Lie algebra, the restriction of
`TauCeti.traceBilinForm`. -/
def traceForm : LinearMap.BilinForm K (LieAlgebra.SpecialLinear.sl (Fin n) K) :=
  (traceBilinForm K (Fin n)).restrict (LieAlgebra.SpecialLinear.sl (Fin n) K).toSubmodule

/-- Evaluation is the trace of the product. -/
@[simp]
theorem traceForm_apply (X Y : LieAlgebra.SpecialLinear.sl (Fin n) K) :
    traceForm K n X Y = trace (X.val * Y.val) := by
  -- `traceBilinForm` is not exposed, so the restriction is not definitionally the trace.
  unfold traceForm
  rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, traceBilinForm_apply]

/-- The restricted trace form is symmetric, because `TauCeti.traceBilinForm` is. -/
theorem traceForm_comm (X Y : LieAlgebra.SpecialLinear.sl (Fin n) K) :
    traceForm K n X Y = traceForm K n Y X :=
  ((traceBilinForm_isSymm K (Fin n)).restrict
    (LieAlgebra.SpecialLinear.sl (Fin n) K).toSubmodule).eq X Y

private theorem eq_zero_of_forall_trace_mul_eq_zero [NeZero (n : K)]
    (X : LieAlgebra.SpecialLinear.sl (Fin n) K)
    (h : ∀ Y : LieAlgebra.SpecialLinear.sl (Fin n) K, trace (X.val * Y.val) = 0) : X = 0 := by
  refine Subtype.ext (Matrix.ext_iff_trace_mul_right.mpr fun Z => ?_)
  -- The right-hand zero is the zero of `sl`, coerced into the matrices.
  simp only [Submodule.coe_zero, zero_mul, trace_zero]
  have hX : trace X.val = 0 := X.property
  have hZ : trace (Z - (trace Z / (n : K)) • (1 : Matrix (Fin n) (Fin n) K)) = 0 := by
    simp only [trace_sub, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]
    field_simp [NeZero.ne (n : K)]
    ring
  have htest := h ⟨Z - (trace Z / (n : K)) • (1 : Matrix (Fin n) (Fin n) K), hZ⟩
  simpa only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, trace_sub, trace_smul, hX,
    smul_zero, sub_zero] using htest

/-- Both radicals of the trace pairing vanish when `n` is nonzero in `K`. -/
theorem traceForm_nondegenerate [NeZero (n : K)] : (traceForm K n).Nondegenerate := by
  constructor
  · intro X h
    exact eq_zero_of_forall_trace_mul_eq_zero K n X fun Y => by
      simpa [traceForm_apply] using h Y
  · intro Y h
    exact eq_zero_of_forall_trace_mul_eq_zero K n Y fun X => by
      simpa [traceForm_apply] using (traceForm_comm K n Y X).trans (h X)

/-- The trace pairing identifies the adjoint carrier with its linear dual. -/
noncomputable def traceDual [NeZero (n : K)] :
    LieAlgebra.SpecialLinear.sl (Fin n) K ≃ₗ[K]
      Module.Dual K (LieAlgebra.SpecialLinear.sl (Fin n) K) :=
  (traceForm K n).toDual (traceForm_nondegenerate K n)

/-- The dual functional associated to `X` evaluates as `tr(XY)`. -/
@[simp]
theorem traceDual_apply [NeZero (n : K)] (X Y : LieAlgebra.SpecialLinear.sl (Fin n) K) :
    traceDual K n X Y = trace (X.val * Y.val) := by
  rw [traceDual, LinearMap.BilinForm.toDual_def, traceForm_apply]

/-- The trace pairing is invariant under the adjoint representation. -/
@[simp]
theorem traceForm_adjointRep (g : SpecialLinearGroup (Fin n) K)
    (X Y : LieAlgebra.SpecialLinear.sl (Fin n) K) :
    traceForm K n (adjointRep K n g X) (adjointRep K n g Y) = traceForm K n X Y := by
  simp only [traceForm_apply, coe_adjointRep_apply]
  have hsmul (A : Matrix (Fin n) (Fin n) K) :
      (g : Matrix (Fin n) (Fin n) K) * A * (g⁻¹ : SpecialLinearGroup (Fin n) K) =
        ConjAct.toConjAct g • A := by
    simp [ConjAct.specialLinearGroup_smul_def, ConjAct.ofConjAct_toConjAct]
  rw [hsmul X.val, hsmul Y.val, ← ConjAct.toConjAct_toGL_smul, ← ConjAct.toConjAct_toGL_smul,
    ← smul_mul', ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]
  exact trace_units_conj (SpecialLinearGroup.toGL g) (X.val * Y.val)

/-- The trace pairing is an equivariant self-duality of the adjoint representation. -/
noncomputable def traceDualEquiv [NeZero (n : K)] :
    (adjointRep K n).Equiv (adjointRep K n).dual :=
  Representation.Equiv.mk (traceDual K n) fun g => by
    ext X Y
    -- `traceDual` is `BilinForm.toDual` and the dual representation precomposes with `g⁻¹`.
    -- Both steps are definitional (`toDual_def` and `dual_apply` are `rfl`), so `rw` does not
    -- see a `traceDual` application to rewrite.
    change traceForm K n (adjointRep K n g X) Y = traceForm K n X (adjointRep K n g⁻¹ Y)
    have h := traceForm_adjointRep K n g X (adjointRep K n g⁻¹ Y)
    simpa only [Representation.self_inv_apply] using h

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
    -- Conjugation is the `ConjAct` action of the image in `GL`, which preserves products
    -- and differences.
    have hsmul (A : Matrix (Fin n) (Fin n) K) :
        (g : Matrix (Fin n) (Fin n) K) * A * (g⁻¹ : SpecialLinearGroup (Fin n) K) =
          ConjAct.toConjAct g • A := by
      simp [ConjAct.specialLinearGroup_smul_def, ConjAct.ofConjAct_toConjAct]
    rw [hsmul X.val, hsmul Y.val, hsmul (X.val * Y.val - Y.val * X.val),
      ← ConjAct.toConjAct_toGL_smul, ← ConjAct.toConjAct_toGL_smul, ← ConjAct.toConjAct_toGL_smul,
      ← smul_mul', ← smul_mul', ← smul_sub]

/-- On a simple tensor the alternating intertwiner is the commutator. -/
@[simp]
theorem alternatingProductMap_tmul (X Y : LieAlgebra.SpecialLinear.sl (Fin n) K) :
    alternatingProductMap K n (X ⊗ₜ[K] Y) = ⁅X, Y⁆ :=
  (rfl)

/-- Swapping the tensor factors negates the alternating intertwiner. -/
theorem comm_alternatingProductMap
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

end TauCeti

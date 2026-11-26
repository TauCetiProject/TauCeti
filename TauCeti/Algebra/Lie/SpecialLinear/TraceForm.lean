/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.TraceForm
public import Mathlib.Algebra.Lie.Classical
public import Mathlib.LinearAlgebra.BilinearForm.Properties
import TauCeti.Algebra.Lie.GeneralLinear.Basic
import Mathlib.Algebra.GroupWithZero.Regular
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# The trace pairing of the special linear Lie algebra

Restricting the trace-of-product pairing to trace-zero matrices gives a symmetric bilinear form.
When multiplication by the matrix size is injective, the restriction is nondegenerate.
A scalar correction to each matrix multiplied by the size allows testing against all matrices.
-/

public section

namespace LieAlgebra.SpecialLinear

attribute [local instance 100] LieRing.ofAssociativeRing

open Matrix TauCeti

section

variable (K : Type*) [CommRing K] (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The trace pairing on the special linear Lie algebra, the restriction of
`TauCeti.traceBilinForm`. -/
def traceForm : LinearMap.BilinForm K (sl ι K) :=
  (traceBilinForm K ι).restrict (sl ι K).toSubmodule

/-- Evaluation is the trace of the product. -/
@[simp]
theorem traceForm_apply (X Y : sl ι K) :
    traceForm K ι X Y = trace (X.val * Y.val) := by
  -- `traceBilinForm` is not exposed, so the restriction is not definitionally the trace.
  unfold traceForm
  rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, traceBilinForm_apply]

/-- The trace form on the special linear Lie algebra is symmetric. -/
theorem traceForm_isSymm : (traceForm K ι).IsSymm := by
  unfold traceForm
  exact (traceBilinForm_isSymm K ι).restrict (sl ι K).toSubmodule

/-- Exchanging the two trace-zero matrices leaves their trace pairing unchanged. -/
theorem traceForm_comm (X Y : sl ι K) :
    traceForm K ι X Y = traceForm K ι Y X :=
  (traceForm_isSymm K ι).eq X Y

end

section

variable (K : Type*) [CommRing K] (ι : Type*) [Fintype ι] [DecidableEq ι]

private theorem eq_zero_of_forall_trace_mul_eq_zero (hcard : IsLeftRegular (Fintype.card ι : K))
    (X : sl ι K)
    (h : ∀ Y : sl ι K, trace (X.val * Y.val) = 0) : X = 0 := by
  refine Subtype.ext (Matrix.ext_iff_trace_mul_right.mpr fun Z => ?_)
  -- The right-hand zero is the zero of `sl`, coerced into the matrices.
  simp only [Submodule.coe_zero, zero_mul, trace_zero]
  have hX : trace X.val = 0 := LieAlgebra.SpecialLinear.mem_sl_iff.mp X.property
  let d : K := Fintype.card ι
  let Y : sl ι K := ⟨d • Z - trace Z • 1, by
    rw [LieAlgebra.SpecialLinear.mem_sl_iff, trace_sub, trace_smul, trace_smul, trace_one,
      smul_eq_mul, smul_eq_mul]
    exact sub_eq_zero.mpr (mul_comm _ _)⟩
  apply hcard.mul_left_eq_zero_iff.mp
  simpa only [Y, d, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, trace_sub,
    trace_smul, hX, smul_zero, sub_zero, smul_eq_mul, mul_zero] using h Y

/-- Both radicals of the trace pairing vanish when multiplication by the matrix size is
injective. -/
theorem traceForm_nondegenerate (hcard : IsLeftRegular (Fintype.card ι : K)) :
    (traceForm K ι).Nondegenerate := by
  apply (traceForm_isSymm K ι).isRefl.nondegenerate_iff_separatingLeft.mpr
  intro X h
  exact eq_zero_of_forall_trace_mul_eq_zero K ι hcard X fun Y => by
    simpa only [traceForm_apply] using h Y

end

end LieAlgebra.SpecialLinear

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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# The trace pairing of the special linear Lie algebra

Restricting the trace-of-product pairing to trace-zero matrices gives a symmetric bilinear form.
The restriction is nondegenerate over any commutative ring in which the matrix size is invertible:
every ambient matrix is a sum of a trace-zero matrix and a scalar matrix, and the scalar part
pairs to zero with trace-zero matrices.
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

private theorem eq_zero_of_forall_trace_mul_eq_zero [Invertible (Fintype.card ι : K)]
    (X : sl ι K)
    (h : ∀ Y : sl ι K, trace (X.val * Y.val) = 0) : X = 0 := by
  refine Subtype.ext (Matrix.ext_iff_trace_mul_right.mpr fun Z => ?_)
  -- The right-hand zero is the zero of `sl`, coerced into the matrices.
  simp only [Submodule.coe_zero, zero_mul, trace_zero]
  have hX : trace X.val = 0 := LieAlgebra.SpecialLinear.mem_sl_iff.mp X.property
  obtain ⟨Y, r, rfl⟩ := exists_sl_add_smul_one_eq
    (fun _ => isUnit_of_invertible _) Z
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, trace_add, trace_smul, h Y,
    hX, smul_zero, add_zero]

/-- Both radicals of the trace pairing vanish when the index cardinality is invertible in `K`. -/
theorem traceForm_nondegenerate [Invertible (Fintype.card ι : K)] :
    (traceForm K ι).Nondegenerate := by
  apply (traceForm_isSymm K ι).isRefl.nondegenerate_iff_separatingLeft.mpr
  intro X h
  exact eq_zero_of_forall_trace_mul_eq_zero K ι X fun Y => by
    simpa only [traceForm_apply] using h Y

end

end LieAlgebra.SpecialLinear

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Module
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Topology.Instances.Matrix

/-!
# The Hermitian Gram map

The Gram matrix `Yᴴ Y` of the columns of a complex matrix `Y` is Hermitian, so `Y ↦ Yᴴ Y` is a
map `Matrix.hermitianGram` into the real submodule `selfAdjoint.submodule ℝ (Matrix m m ℂ)` of
Hermitian matrices. It is continuous and measurable, and it is invariant under left multiplication
by unitary matrices.

## Main declarations

* `Matrix.hermitianGram Y`: the Gram matrix `Yᴴ Y`, as a Hermitian matrix.
* `Matrix.hermitianGram_unitary_mul`: `hermitianGram (u * Y) = hermitianGram Y` for `u` unitary.
-/

public section

namespace Matrix

variable {l m : Type*} [Fintype l]

/-- The Gram matrix `Yᴴ Y` of the columns of a complex matrix `Y`, as a Hermitian matrix. -/
def hermitianGram (Y : Matrix l m ℂ) : selfAdjoint.submodule ℝ (Matrix m m ℂ) :=
  ⟨Yᴴ * Y, (isHermitian_conjTranspose_mul_self Y).isSelfAdjoint⟩

/-- The underlying matrix of `hermitianGram Y` is `Yᴴ * Y`. -/
@[simp] theorem coe_hermitianGram (Y : Matrix l m ℂ) :
    (hermitianGram Y : Matrix m m ℂ) = Yᴴ * Y := (rfl)

/-- The Gram map is invariant under left multiplication by a unitary matrix. -/
theorem hermitianGram_unitary_mul [DecidableEq l] {u : Matrix l l ℂ}
    (hu : u ∈ unitaryGroup l ℂ) (Y : Matrix l m ℂ) : hermitianGram (u * Y) = hermitianGram Y := by
  refine Subtype.ext ?_
  rw [coe_hermitianGram, coe_hermitianGram, conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc uᴴ, ← star_eq_conjTranspose, mem_unitaryGroup_iff'.1 hu, Matrix.one_mul]

/-- The Gram map is continuous. -/
@[fun_prop] theorem continuous_hermitianGram :
    Continuous (hermitianGram : Matrix l m ℂ → _) :=
  (Continuous.matrix_mul (by fun_prop) continuous_id).subtype_mk _

/-- The Gram map is measurable: each entry of `Yᴴ Y` is a finite sum of products of entries of
`Y`. -/
@[fun_prop] theorem measurable_hermitianGram :
    Measurable (hermitianGram : Matrix l m ℂ → _) := by
  refine Measurable.subtype_mk (.of_eval fun a ↦ .of_eval fun b ↦ ?_)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact Finset.measurable_sum _ fun i _ ↦ by fun_prop

end Matrix

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.Analysis.Matrix.Exponential
public import TauCeti.Analysis.Matrix.Normed
public import TauCeti.Geometry.Lie.Exponential.Unitary

/-!
# Matrix exponential lines in the special unitary group

This file identifies the complex matrices whose whole exponential line lies in the special
unitary matrix group: they are exactly the skew-Hermitian matrices of trace zero. It is the
special-unitary companion of the symplectic and orthogonal characterizations in
`TauCeti/Geometry/Lie/Exponential/Matrix/Symplectic.lean` and
`TauCeti/Geometry/Lie/Exponential/Matrix/SpecialOrthogonal.lean`.

The unitary half is already available at the altitude of a Banach star algebra:
`TauCeti.forall_exp_smul_mem_unitary_iff_mem_skewAdjoint` says that the exponential line of `A`
stays unitary exactly when `Aᴴ = -A`. What is special to matrices is the determinant, and that is
what the trace condition records. A skew-Hermitian matrix is diagonalizable, so
`Matrix.det_exp_of_conjTranspose_eq_neg` evaluates `det (exp (t • A))` as `exp (t • trace A)`;
asking that this be `1` for *every* real `t` is asking that two exponential lines in `ℂ` agree,
and exponential lines determine their generators (`TauCeti.eq_of_forall_exp_smul_eq`), so the
trace vanishes. A single `t` would not do: `trace A = 2 * π * I` already gives
`det (exp A) = 1`.

The trace-zero condition is not implied by skew-Hermitian-ness, unlike the real skew-symmetric
case where the diagonal entries vanish outright: the diagonal entries of a skew-Hermitian complex
matrix are purely imaginary, and their sum need not be zero.

This is the matrix-level input for computing the Lie algebra of the special unitary group, the
piece whose absence is recorded in `TauCeti/Geometry/Lie/Subgroup/Unitary.lean`.

## Main results

* `Matrix.exp_mem_specialUnitaryGroup_of_conjTranspose_eq_neg`: the exponential of a
  skew-Hermitian matrix of trace zero is special unitary.
* `Matrix.forall_exp_smul_mem_specialUnitaryGroup_iff`: **a complex matrix generates a
  one-parameter subgroup of the special unitary group exactly when it is skew-Hermitian with
  vanishing trace.**

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 2, "Consequences": the matrix groups are Lie groups, with their Lie
  algebras stated explicitly.
-/

public section

open NormedSpace
open scoped Matrix Matrix.Norms.Operator

noncomputable section

namespace Matrix

/-- A complex matrix is skew-Hermitian exactly when it is a skew-adjoint element of the matrix
algebra. This is the dictionary between the two spellings of the condition, the matrix one used
for the classical groups and the star-algebra one the Banach-algebra exponential lemmas take. -/
theorem mem_skewAdjoint_iff_conjTranspose_eq_neg {n : Type*} {A : Matrix n n ℂ} :
    A ∈ skewAdjoint (Matrix n n ℂ) ↔ Aᴴ = -A := by
  rw [skewAdjoint.mem_iff, star_eq_conjTranspose]

variable {n : Type*} [Fintype n] [DecidableEq n]

-- Select the matrix topology underlying the operator norm, together with continuity of the
-- conjugate transpose for it.
attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar

/-- **The exponential of a skew-Hermitian matrix of trace zero is special unitary.** -/
theorem exp_mem_specialUnitaryGroup_of_conjTranspose_eq_neg {A : Matrix n n ℂ} (hA : Aᴴ = -A)
    (htrace : A.trace = 0) : exp A ∈ specialUnitaryGroup n ℂ := by
  refine mem_specialUnitaryGroup_iff.mpr
    ⟨exp_mem_unitary_of_mem_skewAdjoint (mem_skewAdjoint_iff_conjTranspose_eq_neg.mpr hA), ?_⟩
  have hdet : (exp A).det = NormedSpace.exp A.trace := det_exp_of_conjTranspose_eq_neg hA
  rw [hdet, htrace, NormedSpace.exp_zero]

/-- **A complex matrix generates a one-parameter subgroup of the special unitary group exactly
when it is skew-Hermitian with vanishing trace.** The left-hand side is the condition defining
the Lie algebra of a subgroup through the exponential, so this is the matrix form of "the Lie
algebra of `SU(n)` is the traceless skew-Hermitian matrices". -/
@[simp]
theorem forall_exp_smul_mem_specialUnitaryGroup_iff (A : Matrix n n ℂ) :
    (∀ t : ℝ, exp (t • A) ∈ specialUnitaryGroup n ℂ) ↔ Aᴴ = -A ∧ A.trace = 0 := by
  constructor
  · intro h
    have hskew : Aᴴ = -A := by
      rw [← mem_skewAdjoint_iff_conjTranspose_eq_neg]
      exact (TauCeti.forall_exp_smul_mem_unitary_iff_mem_skewAdjoint A).mp fun t =>
        (mem_specialUnitaryGroup_iff.mp (h t)).1
    refine ⟨hskew, ?_⟩
    -- The determinant along the line is `exp (t • trace A)`, and it is constantly `1`; comparing
    -- that with the constant line of `0` identifies the two generators.
    refine TauCeti.eq_of_forall_exp_smul_eq fun t => ?_
    have hline : (t • A)ᴴ = -(t • A) := mem_skewAdjoint_iff_conjTranspose_eq_neg.mp
      (skewAdjoint.smul_mem t (mem_skewAdjoint_iff_conjTranspose_eq_neg.mpr hskew))
    have hdet : (exp (t • A)).det = NormedSpace.exp (t • A).trace :=
      det_exp_of_conjTranspose_eq_neg hline
    rw [(mem_specialUnitaryGroup_iff.mp (h t)).2, trace_smul] at hdet
    rw [← hdet, smul_zero, NormedSpace.exp_zero]
  · rintro ⟨hskew, htrace⟩ t
    refine exp_mem_specialUnitaryGroup_of_conjTranspose_eq_neg
      (mem_skewAdjoint_iff_conjTranspose_eq_neg.mp
        (skewAdjoint.smul_mem t (mem_skewAdjoint_iff_conjTranspose_eq_neg.mpr hskew))) ?_
    rw [trace_smul, htrace, smul_zero]

end Matrix

end

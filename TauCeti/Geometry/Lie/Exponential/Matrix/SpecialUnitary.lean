/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.Analysis.Matrix.Normed
public import TauCeti.Geometry.Lie.Exponential.Matrix.SpecialLinear
public import TauCeti.Geometry.Lie.Exponential.Unitary

/-!
# Matrix exponential lines in the special unitary group

This file identifies the matrices over `ℝ` or `ℂ` (any `RCLike` field) whose whole exponential
line lies in the special unitary matrix group: they are exactly the skew-Hermitian matrices of
trace zero. It is the special-unitary companion of the orthogonal, symplectic and special linear
characterizations in `TauCeti/Geometry/Lie/Exponential/Matrix/SpecialOrthogonal.lean`,
`TauCeti/Geometry/Lie/Exponential/Matrix/Symplectic.lean` and
`TauCeti/Geometry/Lie/Exponential/Matrix/SpecialLinear.lean`.

The special unitary group is cut out of the matrix algebra by two independent conditions, and
each of them already has its own exponential-line characterization. Unitarity is available at
the altitude of a Banach star algebra, `TauCeti.forall_exp_smul_mem_unitary_iff_mem_skewAdjoint`,
and gives `Aᴴ = -A`; determinant one is `Matrix.forall_det_exp_smul_eq_one_iff_mem_sl`, and gives
`trace A = 0`. So the proof is the conjunction of the two, read through
`Matrix.mem_specialUnitaryGroup_iff`; nothing analytic is new here. The two spellings of
skew-Hermitian-ness are interchanged by `skewAdjoint.mem_iff` and `Matrix.star_eq_conjTranspose`.

Over `ℂ` the trace condition is not implied by skew-Hermitian-ness, unlike the real
skew-symmetric case where the diagonal entries vanish outright: the diagonal entries of a
skew-Hermitian complex matrix are purely imaginary, and their sum need not be zero. It is also
genuinely the whole line that is needed, not a single time: `exp` is `1` on all of `2πiℤ`, so a
matrix of trace `2πi` has `det (exp A) = 1` without having trace zero.

## Main results

* `Matrix.exp_mem_specialUnitaryGroup_of_conjTranspose_eq_neg_of_trace_eq_zero`: the exponential
  of a skew-Hermitian matrix of trace zero is special unitary.
* `Matrix.forall_exp_smul_mem_specialUnitaryGroup_iff_conjTranspose_eq_neg_and_trace_eq_zero`:
  **a matrix generates a one-parameter subgroup of the special unitary group exactly when it is
  skew-Hermitian with vanishing trace.**
-/

public section

open NormedSpace
open scoped Matrix Matrix.Norms.Operator

noncomputable section

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

attribute [local instance 100] LieRing.ofAssociativeRing

-- Select the matrix topology underlying the operator norm, together with continuity of the
-- conjugate transpose for it.
attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar

/-- **The exponential of a skew-Hermitian matrix of trace zero is special unitary.** -/
theorem exp_mem_specialUnitaryGroup_of_conjTranspose_eq_neg_of_trace_eq_zero
    {A : Matrix n n 𝕜} (hA : Aᴴ = -A) (htrace : A.trace = 0) :
    exp A ∈ specialUnitaryGroup n 𝕜 :=
  mem_specialUnitaryGroup_iff.mpr
    ⟨exp_mem_unitary_of_mem_skewAdjoint
        (skewAdjoint.mem_iff.mpr ((star_eq_conjTranspose A).trans hA)),
      det_exp_eq_one_of_mem_sl A (LieAlgebra.SpecialLinear.mem_sl_iff.mpr htrace)⟩

/-- **A matrix generates a one-parameter subgroup of the special unitary group exactly when it is
skew-Hermitian with vanishing trace.** The left-hand side is the condition defining the Lie
algebra of a subgroup through the exponential, so this is the matrix form of "the Lie algebra of
`SU(n)` is the traceless skew-Hermitian matrices". -/
@[simp]
theorem forall_exp_smul_mem_specialUnitaryGroup_iff_conjTranspose_eq_neg_and_trace_eq_zero
    (A : Matrix n n 𝕜) :
    (∀ t : ℝ, exp (t • A) ∈ specialUnitaryGroup n 𝕜) ↔ Aᴴ = -A ∧ A.trace = 0 := by
  constructor
  · intro h
    -- The two defining conditions of the special unitary group are read off the line one at a
    -- time, each by the characterization already available for it.
    refine ⟨(star_eq_conjTranspose A).symm.trans (skewAdjoint.mem_iff.mp
        ((TauCeti.forall_exp_smul_mem_unitary_iff_mem_skewAdjoint A).mp fun t =>
          (mem_specialUnitaryGroup_iff.mp (h t)).1)),
      LieAlgebra.SpecialLinear.mem_sl_iff.mp ((forall_det_exp_smul_eq_one_iff_mem_sl A).mp
        fun t => (mem_specialUnitaryGroup_iff.mp (h t)).2)⟩
  · rintro ⟨hskew, htrace⟩ t
    refine exp_mem_specialUnitaryGroup_of_conjTranspose_eq_neg_of_trace_eq_zero ?_ ?_
    · rw [conjTranspose_smul, star_trivial, hskew, smul_neg]
    · rw [trace_smul, htrace, smul_zero]

end Matrix

end

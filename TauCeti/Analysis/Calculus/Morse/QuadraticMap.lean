/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import TauCeti.Analysis.Calculus.FDeriv.QuadraticMap
public import TauCeti.Analysis.Calculus.Morse.Basic
public import TauCeti.Analysis.Calculus.Morse.Index
import TauCeti.LinearAlgebra.QuadraticForm.Signature

/-!
# Morse data of a quadratic form

A quadratic form `Q` on a finite-dimensional real normed space, viewed as a function, is the
model of a critical point: its Hessian quadratic form is `2 • Q` at every point
(`QuadraticMap.hessianQuadraticForm_eq_two_smul`), so its Morse index is the negative index of
inertia `sigNeg Q` at every point (`QuadraticMap.morseIndex_eq_sigNeg`), and the origin is a
nondegenerate critical point exactly when `Q` is nondegenerate
(`QuadraticMap.isNondegenerateCriticalPoint_zero_iff`).

These identify the Morse data of a function which, after a change of coordinates, is a constant
plus a quadratic form, such as a diagonal form `QuadraticMap.weightedSumSquares`, whose
negative index of inertia Mathlib computes as the number of negative weights
(`QuadraticForm.sigNeg_weightedSumSquares`).
-/

public section

open TauCeti

namespace QuadraticMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Hessian quadratic form of a quadratic form `Q` is `2 • Q`, at every point. -/
theorem hessianQuadraticForm_eq_two_smul (Q : QuadraticForm ℝ E) (x : E) :
    hessianQuadraticForm Q x = (2 : ℝ) • Q := by
  ext v
  rw [hessianQuadraticForm_apply, fderiv_fderiv_apply, polar_self, smul_apply, two_nsmul,
    two_smul]

/-- The Morse index of a quadratic form `Q` is its negative index of inertia, at every point. -/
@[simp]
theorem morseIndex_eq_sigNeg (Q : QuadraticForm ℝ E) (x : E) : morseIndex Q x = sigNeg Q := by
  rw [morseIndex_def, hessianQuadraticForm_eq_two_smul,
    QuadraticForm.sigNeg_smul_of_pos _ two_pos]

/-- The origin is a nondegenerate critical point of a quadratic form exactly when the form is
nondegenerate. -/
theorem isNondegenerateCriticalPoint_zero_iff (Q : QuadraticForm ℝ E) :
    IsNondegenerateCriticalPoint Q 0 ↔ Q.Nondegenerate := by
  have h₁ : fderiv ℝ Q 0 = 0 := by
    ext v
    simp [fderiv_apply]
  have h₂ : (fderiv ℝ (fderiv ℝ Q) 0).toBilinForm = polarBilin Q := by
    ext v w
    simp [fderiv_fderiv_apply]
  rw [isNondegenerateCriticalPoint_iff_separatingLeft, h₂, nondegenerate_iff_radical_eq_bot,
    radical_eq_ker_polarBilin, ← LinearMap.separatingLeft_iff_ker_eq_bot]
  exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨Q.contDiff.contDiffAt, h₁, h⟩⟩

end QuadraticMap

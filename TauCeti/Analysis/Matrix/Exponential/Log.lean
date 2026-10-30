/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import TauCeti.Analysis.Matrix.Exponential.Derivative
public import TauCeti.Analysis.Matrix.L2OpNorm
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# The logarithm and real powers of positive definite matrices

Over `𝕜 = ℝ` or `ℂ`, the matrix exponential maps the Hermitian matrices onto the positive definite
ones, with inverse the logarithm `cfc Real.log` of the continuous functional calculus. This file
proves both inverse identities and that the logarithm is `C^n` on the positive definite matrices
for every `n : ℕ∞ω`, including the analytic case `n = ω`, over `𝕜` itself. Near each positive
definite matrix it agrees with the analytic local inverse of `exp` on the full matrix space, which
the inverse function theorem provides because the derivative of `exp` at a Hermitian matrix is
invertible (`Matrix.IsHermitian.isUnit_expFDeriv`). The real powers `P ^ s = exp (s • log P)` and
the square root inherit this smoothness.

The logarithm is written `cfc Real.log`, which is `CFC.log` whenever the latter is defined;
`CFC.log` needs a normed `ℝ`-algebra structure, which complex matrices do not carry by default.
The smoothness statements use the scoped Euclidean operator norm `Matrix.Norms.L2Operator`, whose
topology is the native matrix topology.

## Main results

* `Matrix.IsHermitian.posDef_exp`: the exponential of a Hermitian matrix is positive definite.
* `Matrix.IsHermitian.cfc_log_exp`, `Matrix.PosDef.exp_cfc_log`: the logarithm inverts the
  exponential on the Hermitian matrices, and the exponential inverts the logarithm on the positive
  definite matrices.
* `Matrix.PosDef.rpow_eq_exp_smul_cfc_log`: `P ^ s = exp (s • log P)` for positive definite `P`.
* `Matrix.contDiffOn_cfc_log`, `Matrix.contDiffOn_rpow`, `Matrix.contDiffOn_sqrt`: the logarithm,
  every real power and the square root are `C^n` on the positive definite matrices.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts
  in Mathematics 222, Springer, 2015, Sections 2.3 and 2.5.
-/

public section

noncomputable section

open NormedSpace
open scoped ContDiff ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- The exponential of a Hermitian matrix is positive definite. -/
theorem IsHermitian.posDef_exp {X : Matrix n n 𝕜} (hX : X.IsHermitian) : (exp X).PosDef := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  exact isStrictlyPositive_iff_posDef.1 <|
    (Matrix.isUnit_exp X).isStrictlyPositive hX.isSelfAdjoint.exp_nonneg

/-- The logarithm of the exponential of a Hermitian matrix is the matrix itself. -/
@[simp, grind =]
theorem IsHermitian.cfc_log_exp {X : Matrix n n 𝕜} (hX : X.IsHermitian) :
    cfc Real.log (exp X) = X := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  exact CFC.log_exp X hX.isSelfAdjoint

/-- The exponential of the logarithm of a positive definite matrix is the matrix itself. -/
@[simp, grind =]
theorem PosDef.exp_cfc_log {P : Matrix n n 𝕜} (hP : P.PosDef) : exp (cfc Real.log P) = P := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  exact CFC.exp_log P (isStrictlyPositive_iff_posDef.2 hP)

/-- **Smoothness of the matrix logarithm.** The logarithm is `C^n` on the positive definite
matrices for every `n : ℕ∞ω`, including `n = ω`, over either the real or the complex scalars. -/
theorem contDiffOn_cfc_log {k : ℕ∞ω} :
    ContDiffOn 𝕜 k (cfc Real.log : Matrix n n 𝕜 → Matrix n n 𝕜) {P | P.PosDef} := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  have h := CFC.contDiffOn_log (𝕂 := 𝕜) (A := Matrix n n 𝕜) (n := k)
    fun X hX ↦ (isHermitian_iff_isSelfAdjoint.2 hX).isUnit_expFDeriv
  simp only [isStrictlyPositive_iff_posDef] at h
  -- `CFC.log` is defined as `cfc Real.log`, and the norm of the normed `𝕜`-algebra structure is
  -- the scoped Euclidean operator norm, so `h` is the goal once `CFC.log` is unfolded.
  unfold CFC.log at h
  exact h

/-- A real power of a positive definite matrix is the exponential of its rescaled logarithm. -/
theorem PosDef.rpow_eq_exp_smul_cfc_log {P : Matrix n n 𝕜} (hP : P.PosDef) (s : ℝ) :
    P ^ s = exp (s • cfc Real.log P) := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  exact CFC.rpow_eq_exp_smul_log P s (isStrictlyPositive_iff_posDef.2 hP)

/-- Every real power `P ↦ P ^ s` is `C^n` on the positive definite matrices, for every
`n : ℕ∞ω`. -/
theorem contDiffOn_rpow (s : ℝ) {k : ℕ∞ω} :
    ContDiffOn 𝕜 k (fun P : Matrix n n 𝕜 ↦ P ^ s) {P | P.PosDef} := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  have h := CFC.contDiffOn_rpow (𝕂 := 𝕜) (A := Matrix n n 𝕜) (n := k)
    (fun X hX ↦ (isHermitian_iff_isSelfAdjoint.2 hX).isUnit_expFDeriv) s
  simpa only [isStrictlyPositive_iff_posDef] using h

/-- The square root is `C^n` on the positive definite matrices, for every `n : ℕ∞ω`. -/
theorem contDiffOn_sqrt {k : ℕ∞ω} :
    ContDiffOn 𝕜 k (CFC.sqrt : Matrix n n 𝕜 → Matrix n n 𝕜) {P | P.PosDef} := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  have h := CFC.contDiffOn_sqrt (𝕂 := 𝕜) (A := Matrix n n 𝕜) (n := k)
    fun X hX ↦ (isHermitian_iff_isSelfAdjoint.2 hX).isUnit_expFDeriv
  simpa only [isStrictlyPositive_iff_posDef] using h

end Matrix

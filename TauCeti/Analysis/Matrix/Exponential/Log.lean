/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Matrix.Order
public import TauCeti.Analysis.Matrix.Exponential.Derivative
public import TauCeti.Analysis.Matrix.L2OpNorm
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import TauCeti.Analysis.Matrix.Exponential.Block
import TauCeti.Analysis.Matrix.PosDef
import TauCeti.Analysis.Matrix.RCLike

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

Pushing matrices into `Matrix n n ℂ` via `Matrix.toComplexStarAlgHom` also transfers the
C⋆-algebraic operator monotonicity and operator concavity of `CFC.log` to `cfc Real.log` over an
arbitrary `RCLike` scalar field.

The logarithm is written `cfc Real.log`, which is `CFC.log` whenever the latter is defined;
`CFC.log` needs a normed `ℝ`-algebra structure, which complex matrices do not carry by default.
The smoothness statements use the scoped Euclidean operator norm `Matrix.Norms.L2Operator`, whose
topology is the native matrix topology.

## Main results

* `Matrix.IsHermitian.posDef_exp`: the exponential of a Hermitian matrix is positive definite.
* `Matrix.IsHermitian.cfc_log_exp`, `Matrix.PosDef.exp_cfc_log`: the logarithm inverts the
  exponential on the Hermitian matrices, and the exponential inverts the logarithm on the positive
  definite matrices.
* `Matrix.IsHermitian.exp_eq_exp_iff`: the exponential is injective on the Hermitian matrices.
* `Matrix.IsHermitian.commute_exp_iff`: a matrix commutes with the exponential of a Hermitian
  matrix exactly when it commutes with the matrix.
* `Matrix.PosDef.cfc_log_inv`, `Matrix.PosDef.cfc_log_smul`,
  `Matrix.PosDef.cfc_log_fromBlocks_diagonal`: logarithm of an inverse, positive scalar multiple,
  and two-block diagonal matrix.
* `Matrix.PosDef.cfc_log_le_cfc_log`, `Matrix.concaveOn_cfc_log`: Loewner monotonicity and
  operator concavity of `cfc Real.log` on the positive definite cone over `ℝ` or `ℂ`.
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

/-- The exponential is injective on the Hermitian matrices. -/
@[simp]
theorem IsHermitian.exp_eq_exp_iff {X Y : Matrix n n 𝕜} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    exp X = exp Y ↔ X = Y :=
  ⟨fun h ↦ by rw [← hX.cfc_log_exp, h, hY.cfc_log_exp], fun h ↦ h ▸ rfl⟩

/-- A matrix commutes with the exponential of a Hermitian matrix exactly when it commutes with the
matrix itself. -/
@[simp]
theorem IsHermitian.commute_exp_iff {X U : Matrix n n 𝕜} (hX : X.IsHermitian) :
    Commute U (exp X) ↔ Commute U X := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  refine ⟨fun h ↦ ?_, fun h ↦ h.exp_right⟩
  -- `X = log (exp X)` lies in the functional calculus of `exp X`.
  simpa only [hX.cfc_log_exp] using (h.symm.cfc_real Real.log).symm

/-- The exponential of the logarithm of a positive definite matrix is the matrix itself. -/
@[simp, grind =]
theorem PosDef.exp_cfc_log {P : Matrix n n 𝕜} (hP : P.PosDef) : exp (cfc Real.log P) = P := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  exact CFC.exp_log P (isStrictlyPositive_iff_posDef.2 hP)

/-- The logarithm of the inverse of a positive definite matrix is minus its logarithm. -/
theorem PosDef.cfc_log_inv {P : Matrix n n 𝕜} (hP : P.PosDef) :
    cfc Real.log P⁻¹ = -cfc Real.log P := by
  rw [nonsing_inv_eq_ringInverse, ← cfc_ringInverse_id (R := ℝ) P hP.isUnit hP.1.isSelfAdjoint,
    ← cfc_comp' Real.log (fun x : ℝ ↦ x⁻¹) P
      ((P.finite_real_spectrum.image _).continuousOn _) (P.finite_real_spectrum.continuousOn _)
      hP.1.isSelfAdjoint, ← cfc_neg]
  exact cfc_congr fun x _ ↦ Real.log_inv x

/-- Scaling a positive definite matrix by `c > 0` shifts its logarithm by `log c • 1`. -/
theorem PosDef.cfc_log_smul {P : Matrix n n 𝕜} (hP : P.PosDef) {c : ℝ} (hc : 0 < c) :
    cfc Real.log (c • P) = Real.log c • 1 + cfc Real.log P := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  have hcP : c • P = (c • (1 : Matrix n n 𝕜)) * P := by rw [smul_mul_assoc, one_mul]
  rw [hcP]
  simpa only [CFC.log, ← Algebra.algebraMap_eq_smul_one, cfc_algebraMap] using
    CFC.log_mul_of_commute ((Commute.one_left P).smul_left c)
      (isStrictlyPositive_iff_posDef.2 (PosDef.one.smul hc))
      (isStrictlyPositive_iff_posDef.2 hP)

/-- The logarithm of a two-block diagonal positive definite matrix is block diagonal. -/
theorem PosDef.cfc_log_fromBlocks_diagonal {m : Type*} [Fintype m] [DecidableEq m]
    {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜} (hP : P.PosDef) (hQ : Q.PosDef) :
    cfc Real.log (fromBlocks P 0 0 Q) = fromBlocks (cfc Real.log P) 0 0 (cfc Real.log Q) := by
  have hLP : (cfc Real.log P).IsHermitian :=
    isHermitian_iff_isSelfAdjoint.2 (cfc_predicate Real.log P)
  have hLQ : (cfc Real.log Q).IsHermitian :=
    isHermitian_iff_isSelfAdjoint.2 (cfc_predicate Real.log Q)
  have hH : (fromBlocks (cfc Real.log P) 0 0 (cfc Real.log Q)).IsHermitian := by
    simp only [IsHermitian, fromBlocks_conjTranspose, conjTranspose_zero, hLP.eq, hLQ.eq]
  rw [← hH.cfc_log_exp, exp_fromBlocks_diagonal, hP.exp_cfc_log, hQ.exp_cfc_log]

/-- **Operator monotonicity of the matrix logarithm.** For positive definite `P` and `P ≤ Q` in the
Loewner order over `ℝ` or `ℂ`, `cfc Real.log P ≤ cfc Real.log Q`. -/
@[gcongr]
theorem PosDef.cfc_log_le_cfc_log {P Q : Matrix n n 𝕜} (hP : P.PosDef) (hPQ : P ≤ Q) :
    cfc Real.log P ≤ cfc Real.log Q := by
  rw [← toComplexStarAlgHom_le_iff (𝕜 := 𝕜), toComplexStarAlgHom_cfc, toComplexStarAlgHom_cfc]
  exact CFC.log_le_log (toComplexStarAlgHom_le_iff.2 hPQ)
    (isStrictlyPositive_iff_posDef.2 (posDef_toComplexStarAlgHom_iff.2 hP))

/-- **Operator concavity of the matrix logarithm** on the positive definite cone over `ℝ` or `ℂ`. -/
theorem concaveOn_cfc_log : ConcaveOn ℝ {P : Matrix n n 𝕜 | P.PosDef} (cfc Real.log) := by
  refine ⟨TauCeti.convex_setOfPred_posDef, fun P hP Q hQ a b ha hb hab ↦ ?_⟩
  simp only [← toComplexStarAlgHom_le_iff (𝕜 := 𝕜), map_add, map_smul, toComplexStarAlgHom_cfc]
  exact CFC.concaveOn_log.2
    (isStrictlyPositive_iff_posDef.2 (posDef_toComplexStarAlgHom_iff.2 hP))
    (isStrictlyPositive_iff_posDef.2 (posDef_toComplexStarAlgHom_iff.2 hQ)) ha hb hab

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

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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import TauCeti.Analysis.Normed.Algebra.Basic

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
* `Matrix.IsHermitian.exp_eq_exp_iff`: the exponential is injective on the Hermitian matrices.
* `Matrix.IsHermitian.commute_exp_iff`: a matrix commutes with the exponential of a Hermitian
  matrix exactly when it commutes with the matrix.
* `Matrix.IsHermitian.star_exp_mul_mul_exp_eq_iff`: the exponential of a Hermitian matrix `X`
  preserves a form `J` (`star (exp X) * J * exp X = J`) exactly when `J * X + X * J = 0`.
* `Matrix.PosDef.cfc_log_inv`: `log P⁻¹ = -log P` for positive definite `P`.
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

/-- For any matrix `J` and a Hermitian matrix `X`, the exponential `exp X` preserves the form `J`
if and only if `J * X + X * J = 0`. -/
theorem IsHermitian.star_exp_mul_mul_exp_eq_iff (J : Matrix n n 𝕜) {X : Matrix n n 𝕜}
    (hX : X.IsHermitian) : star (exp X) * J * exp X = J ↔ J * X + X * J = 0 := by
  have hexp_star : star (NormedSpace.exp X) = NormedSpace.exp X := by
    rw [star_eq_conjTranspose, ← exp_conjTranspose, hX.eq]
  rw [hexp_star]
  constructor
  · intro h
    -- Diagonalize `X = U diag(d) U⁻¹` with real eigenvalues `d`, so that
    -- `exp X = U diag(exp d) U⁻¹`.
    let u : (Matrix n n 𝕜)ˣ := Unitary.toUnits hX.eigenvectorUnitary
    let d : n → 𝕜 := RCLike.ofReal ∘ hX.eigenvalues
    have hX_eq : X = u.val * diagonal d * u⁻¹.val := by
      simpa [u, d, Unitary.conjStarAlgAut_apply, Unitary.val_toUnits_apply] using
        hX.spectral_theorem
    have hexp_eq :
        NormedSpace.exp X = u.val * diagonal (fun i ↦ NormedSpace.exp (d i)) * u⁻¹.val := by
      rw [hX_eq, Matrix.exp_units_conj u (diagonal d), Matrix.exp_diagonal, Pi.exp_def]
    -- In the eigenbasis, `J' = U⁻¹ J U` satisfies `diag(exp d) J' diag(exp d) = J'`.
    let J' : Matrix n n 𝕜 := u⁻¹.val * J * u.val
    have hJ' : diagonal (fun i ↦ NormedSpace.exp (d i)) * J' *
        diagonal (fun i ↦ NormedSpace.exp (d i)) = J' := by
      calc _ = u⁻¹.val * (NormedSpace.exp X * J * NormedSpace.exp X) * u.val := by
            simp [hexp_eq, J', Matrix.mul_assoc]
        _ = J' := by rw [h]
    -- Compare entries: `exp (dᵢ + dⱼ) J'ᵢⱼ = J'ᵢⱼ`, and `exp (dᵢ + dⱼ) = 1` forces `dᵢ + dⱼ = 0`
    -- because the eigenvalues are real. Hence `J'` anticommutes with `diag(d)`.
    have hanti' : J' * diagonal d + diagonal d * J' = 0 := by
      ext i j
      have hij : NormedSpace.exp (d i) * J' i j * NormedSpace.exp (d j) = J' i j := by
        simpa [Matrix.diagonal_mul, Matrix.mul_diagonal] using congrFun (congrFun hJ' i) j
      have hmul : (NormedSpace.exp (d i + d j) - 1) * J' i j = 0 := by
        rw [NormedSpace.exp_add_of_commute (Commute.all _ _), sub_mul, one_mul, sub_eq_zero]
        linear_combination hij
      rcases mul_eq_zero.1 hmul with h1 | h0
      · have hreal : Real.exp (hX.eigenvalues i + hX.eigenvalues j) = 1 := by
          refine RCLike.ofReal_injective (K := 𝕜) ?_
          rw [Real.exp_eq_exp_ℝ, ← RCLike.algebraMap_eq_ofReal, algebraMap_exp_comm,
            RCLike.algebraMap_eq_ofReal, RCLike.ofReal_one]
          simpa [d] using sub_eq_zero.1 h1
        have hd : d i + d j = 0 := by
          simp [d, ← map_add, (Real.exp_eq_one_iff _).1 hreal]
        simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.zero_apply]
        linear_combination J' i j * hd
      · simp [Matrix.mul_diagonal, Matrix.diagonal_mul, h0]
    -- Undiagonalize.
    calc J * X + X * J = u.val * (J' * diagonal d + diagonal d * J') * u⁻¹.val := by
          simp [hX_eq, J', mul_add, add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hanti', Matrix.mul_zero, Matrix.zero_mul]
  · intro h
    let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
    let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
    have hS : SemiconjBy J X (-X) := by
      rw [SemiconjBy, neg_mul, eq_neg_of_add_eq_zero_left h]
    simpa only [neg_neg] using hS.exp_neg_mul_mul_exp_eq_self

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

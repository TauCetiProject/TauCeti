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
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

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
* `Matrix.PosDef.cfc_log_inv`: `log P⁻¹ = -log P` for positive definite `P`.
* `Matrix.PosDef.cfc_log_le_cfc_log`: the matrix logarithm is operator monotone on positive
  definite matrices over any `RCLike` field.
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

/-- **Operator monotonicity of the matrix logarithm.** For positive definite matrices `A ≤ B` over
any `RCLike` field `𝕜`, `cfc Real.log A ≤ cfc Real.log B` in the Loewner order. -/
theorem PosDef.cfc_log_le_cfc_log {A B : Matrix n n 𝕜} (hA : A.PosDef) (hle : A ≤ B) :
    cfc Real.log A ≤ cfc Real.log B := by
  -- Transfer `CFC.log_le_log` from `Matrix n n ℂ` along entrywise `RCLike.map 𝕜 ℂ`.
  let Φ : Matrix n n 𝕜 →⋆ₐ[ℝ] Matrix n n ℂ :=
    { toFun := fun M ↦ M.map (RCLike.map 𝕜 ℂ)
      map_one' := by
        ext i j; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      map_mul' := fun M N ↦ by
        ext i j
        simp only [map_apply, Matrix.mul_apply, map_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        apply Complex.ext <;> simp
      map_zero' := by ext; simp
      map_add' := fun M N ↦ by
        ext i j; apply Complex.ext <;> simp
      commutes' := fun r ↦ by
        ext i j; by_cases hij : i = j <;> simp [Algebra.algebraMap_eq_smul_one, hij]
      map_star' := fun M ↦ by
        ext i j; apply Complex.ext <;> simp [star_eq_conjTranspose] }
  have hΦ_cont : Continuous Φ :=
    continuous_pi fun _ ↦ continuous_pi fun _ ↦
      (RCLike.map 𝕜 ℂ).continuous.comp (continuous_apply _ |>.comp (continuous_apply _))
  have hΦ_psd {M : Matrix n n 𝕜} (hM : M.PosSemidef) : (Φ M).PosSemidef := by
    have hsq : CFC.sqrt M * CFC.sqrt M = M := CFC.sqrt_mul_sqrt_self M hM.nonneg
    have hself : (CFC.sqrt M)ᴴ = CFC.sqrt M := (CFC.sqrt_nonneg M).isSelfAdjoint
    have hΦself : (Φ (CFC.sqrt M))ᴴ = Φ (CFC.sqrt M) := by
      rw [← star_eq_conjTranspose, ← map_star, star_eq_conjTranspose, hself]
    have hmul : Φ M = (Φ (CFC.sqrt M))ᴴ * Φ (CFC.sqrt M) := by
      rw [hΦself, ← map_mul, hsq]
    rw [hmul]
    exact posSemidef_conjTranspose_mul_self _
  have hΦA : IsStrictlyPositive (Φ A) :=
    ⟨(hΦ_psd hA.posSemidef).nonneg, hA.isUnit.map Φ.toRingHom⟩
  have hΦle : Φ A ≤ Φ B := by
    rw [le_iff, ← map_sub]
    exact hΦ_psd (le_iff.1 hle)
  have hB_sa : IsSelfAdjoint B := (hA.posSemidef.nonneg.trans hle).isSelfAdjoint
  have hlog : CFC.log (Φ A) ≤ CFC.log (Φ B) := CFC.log_le_log hΦle hΦA
  unfold CFC.log at hlog
  rw [← StarAlgHom.map_cfc Φ Real.log A (A.finite_real_spectrum.continuousOn _) hΦ_cont
      hA.1.isSelfAdjoint (hA.1.isSelfAdjoint.map Φ),
    ← StarAlgHom.map_cfc Φ Real.log B (B.finite_real_spectrum.continuousOn _) hΦ_cont
      hB_sa (hB_sa.map Φ),
    le_iff, ← map_sub] at hlog
  rw [le_iff]
  have hdiff_herm : (cfc Real.log B - cfc Real.log A).IsHermitian :=
    (IsSelfAdjoint.isHermitian (cfc_predicate Real.log B)).sub
      (IsSelfAdjoint.isHermitian (cfc_predicate Real.log A))
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨hdiff_herm, fun x ↦ ?_⟩
  let y : n → ℂ := fun i ↦ RCLike.map 𝕜 ℂ (x i)
  have hy := (posSemidef_iff_dotProduct_mulVec.1 hlog).2 y
  have hquad : star y ⬝ᵥ Φ (cfc Real.log B - cfc Real.log A) *ᵥ y =
      RCLike.map 𝕜 ℂ (star x ⬝ᵥ (cfc Real.log B - cfc Real.log A) *ᵥ x) := by
    simp only [dotProduct, mulVec, map_sum, y, Φ, StarAlgHom.coe_mk', AlgHom.coe_mk,
      RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, map_apply, Pi.star_apply,
      RCLike.star_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    apply Complex.ext <;> simp
  rw [hquad, Complex.nonneg_iff] at hy
  exact RCLike.nonneg_iff.2 ⟨by simpa using hy.1, by simpa using hy.2.symm⟩

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

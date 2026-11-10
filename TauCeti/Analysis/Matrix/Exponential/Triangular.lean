/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Exponential.Block
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Analysis.Calculus.DSlope
import TauCeti.Analysis.Normed.Algebra.MatrixExponential
import TauCeti.Analysis.SpecialFunctions.Exp.DividedDifference
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.LinearAlgebra.Matrix.Bilinear
import TauCeti.Analysis.Normed.Algebra.Exponential
import TauCeti.Analysis.Normed.Algebra.Basic

/-!
# The last-column coefficient of a triangular exponential

For an upper block matrix with final diagonal entry `d`, the exponential is linear in its
last off-diagonal column. Its coefficient is the integral of the exponential of the leading
block, weighted by the scalar exponential of `d`. The integral, block identity, triangularity,
and joint regularity hold over every complete real normed coefficient algebra. For real or
complex coefficients, an upper-triangular leading block with real diagonal has an invertible
coefficient, including when diagonal entries repeat.

## Main definitions

* `Matrix.expColumnCoefficient`: the exponential-weight integral acting on the last column.

## Main results

* `Matrix.expColumnCoefficient_apply`: the entrywise integral formula.
* `Matrix.expColumnCoefficient_eq_toBlocks₁₂_exp`: the coefficient as an exponential block.
* `Matrix.toBlocks₁₂_exp_fromBlocks_real_smul_one`: the upper-right block is the coefficient
  times the original rectangular block.
* `Matrix.contDiff_expColumnCoefficient`: joint regularity, including analyticity.
* `Matrix.IsUpperTriangular.expColumnCoefficient`: the coefficient remains upper triangular.
* `Matrix.IsUpperTriangular.expColumnCoefficient_apply_diag`: real diagonal entries give
  divided differences, including the equal-entry value.
* `Matrix.IsUpperTriangular.isUnit_expColumnCoefficient`: real diagonal entries imply
  invertibility without a distinctness assumption.

## References

* C. F. Van Loan, *Computing Integrals Involving the Matrix Exponential*, IEEE Transactions
  on Automatic Control 23(3) (1978), 395–404, Theorem 1, pp. 395–396,
  DOI: 10.1109/TAC.1978.1101743, for the underlying block-exponential integral.
-/

public noncomputable section

open NormedSpace MeasureTheory
open scoped Matrix.Norms.Operator ContDiff

attribute [local instance] TauCeti.normedAlgebraRatOfReal

namespace Matrix

variable {n R : Type*} [Fintype n] [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

section Coefficient

variable [DecidableEq n]

/-- The exponential-weight coefficient acting on the last column of an upper block matrix. -/
def expColumnCoefficient (A : Matrix n n R) (d : ℝ) : Matrix n n R :=
  ∫ t in (0 : ℝ)..1, Real.exp (t * d) • exp ((1 - t) • A)

/-- Each coefficient entry is the scalar integral of the corresponding exponential entry. -/
@[simp]
theorem expColumnCoefficient_apply (A : Matrix n n R) (d : ℝ) (i j : n) :
    expColumnCoefficient A d i j =
      ∫ t in (0 : ℝ)..1, Real.exp (t * d) • exp ((1 - t) • A) i j := by
  let : ENormedAddMonoid (Matrix n n R) := NormedAddGroup.toENormedAddMonoid
  have hi : IntervalIntegrable
      (fun t : ℝ ↦ Real.exp (t * d) • exp ((1 - t) • A)) volume 0 1 :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  let e : Matrix n n R →L[ℝ] R :=
    { toLinearMap := entryLinearMap ℝ R i j
      cont := continuous_id.matrix_elem i j }
  exact (e.intervalIntegral_comp_comm hi).symm

/-- Exponentiating a real scalar matrix gives the corresponding positive scalar matrix. -/
private theorem exp_real_smul_one (x : ℝ) :
    exp (x • (1 : Matrix n n R)) = Real.exp x • 1 := by
  have h : exp (x • (1 : R)) = Real.exp x • (1 : R) := by
    simpa only [Algebra.algebraMap_eq_smul_one, ← Real.exp_eq_exp_ℝ] using
      (NormedSpace.algebraMap_exp_comm (𝔸 := R) x).symm
  rw [← diagonal_one, ← diagonal_smul, exp_diagonal, ← diagonal_smul]
  congr 1
  funext i
  simpa only [Pi.coe_exp, Pi.smul_apply] using h

/-- The column coefficient is a block of a matrix exponential. This explicit rewrite gives
access to the regularity of the exponential without differentiating its integral formula. -/
theorem expColumnCoefficient_eq_toBlocks₁₂_exp (A : Matrix n n R) (d : ℝ) :
    expColumnCoefficient A d =
      (exp (fromBlocks A (1 : Matrix n n R) (0 : Matrix n n R)
        (d • (1 : Matrix n n R)))).toBlocks₁₂ := by
  symm
  rw [toBlocks₁₂_exp_fromBlocks_zero₂₁, expColumnCoefficient]
  congr 1
  funext t
  simp only [smul_smul, exp_real_smul_one, mul_one, mul_smul_comm]

/-- With a real scalar final diagonal block, the upper-right exponential block is the
column coefficient times the original rectangular block. Empty block sizes are allowed. -/
theorem toBlocks₁₂_exp_fromBlocks_real_smul_one {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix n n R) (B : Matrix n m R) (d : ℝ) :
    (exp (fromBlocks A B 0 (d • (1 : Matrix m m R)))).toBlocks₁₂ =
      expColumnCoefficient A d * B := by
  let : ENormedAddMonoid (Matrix n n R) := NormedAddGroup.toENormedAddMonoid
  have hi : IntervalIntegrable
      (fun t : ℝ ↦ Real.exp (t * d) • exp ((1 - t) • A)) volume 0 1 :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  let L : Matrix n n R →L[ℝ] Matrix n m R :=
    { toLinearMap := mulRightLinearMap n ℝ B
      cont := continuous_id.matrix_mul continuous_const }
  have h : (∫ t in (0 : ℝ)..1, (Real.exp (t * d) • exp ((1 - t) • A)) * B) =
      (∫ t in (0 : ℝ)..1, Real.exp (t * d) • exp ((1 - t) • A)) * B := by
    exact L.intervalIntegral_comp_comm hi
  rw [toBlocks₁₂_exp_fromBlocks_zero₂₁, expColumnCoefficient]
  simp only [smul_smul, exp_real_smul_one, Matrix.mul_smul, Matrix.mul_one]
  simpa only [Matrix.smul_mul] using h

/-- The last-column exponential coefficient is jointly smooth in the leading block and
its final real diagonal entry, with arbitrary finite, smooth, or analytic regularity. -/
@[fun_prop]
theorem contDiff_expColumnCoefficient (m : ℕ∞ω) : ContDiff ℝ m
    (fun p : Matrix n n R × ℝ ↦ expColumnCoefficient p.1 p.2) := by
  let T : (Matrix n n R × ℝ) →L[ℝ] Matrix (n ⊕ n) (n ⊕ n) R :=
    { toLinearMap :=
      { toFun := fun p ↦ fromBlocks p.1 0 0 (p.2 • (1 : Matrix n n R))
        map_add' := by
          intro p q
          simp only [Prod.fst_add, Prod.snd_add, add_smul, fromBlocks_add, add_zero]
        map_smul' := by
          intro c p
          simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply,
            fromBlocks_smul, smul_zero, smul_smul, smul_eq_mul] }
      cont := continuous_matrix fun i j ↦ by
        cases i with
        | inl i =>
          cases j with
          | inl j => exact continuous_fst.matrix_elem i j
          | inr j => exact continuous_const
        | inr i =>
          cases j with
          | inl j => exact continuous_const
          | inr j => exact (continuous_snd.smul continuous_const).matrix_elem i j }
  let P : Matrix (n ⊕ n) (n ⊕ n) R →L[ℝ] Matrix n n R :=
    { toLinearMap :=
      { toFun := toBlocks₁₂
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
      cont := continuous_matrix fun i j ↦ continuous_id.matrix_elem (Sum.inl i) (Sum.inr j) }
  have he : ContDiff ℝ m (exp : Matrix (n ⊕ n) (n ⊕ n) R → _) := contDiff_exp ℝ
  have hT : ContDiff ℝ m (fun p ↦ T p) := T.contDiff
  have hP : ContDiff ℝ m (fun A ↦ P A) := P.contDiff
  have h := hP.comp (he.comp (hT.add
    (contDiff_const (c := fromBlocks (0 : Matrix n n R) (1 : Matrix n n R) 0 0))))
  have hTapp (p : Matrix n n R × ℝ) :
      T p = fromBlocks p.1 0 0 (p.2 • (1 : Matrix n n R)) := rfl
  have hid (p : Matrix n n R × ℝ) :
      T p + fromBlocks (0 : Matrix n n R) (1 : Matrix n n R) 0 0 =
        fromBlocks p.1 1 0 (p.2 • (1 : Matrix n n R)) := by
    simp only [hTapp, fromBlocks_add, add_zero, zero_add]
  have hPapp (A : Matrix (n ⊕ n) (n ⊕ n) R) : P A = A.toBlocks₁₂ := rfl
  simpa only [Function.comp_def, hid, hPapp,
    ← Matrix.expColumnCoefficient_eq_toBlocks₁₂_exp] using h

end Coefficient

section Triangular

variable [LinearOrder n]

/-- The last-column exponential coefficient of an upper-triangular block is upper triangular. -/
theorem IsUpperTriangular.expColumnCoefficient {A : Matrix n n R}
    (hA : A.IsUpperTriangular) (d : ℝ) : (expColumnCoefficient A d).IsUpperTriangular := by
  intro i j hji
  rw [expColumnCoefficient_apply]
  have hscaled (t : ℝ) : ((1 - t) • A).IsUpperTriangular :=
    (blockTriangularSubalgebra ℝ R id).smul_mem hA (1 - t)
  have hz (t : ℝ) : exp ((1 - t) • A) i j = 0 := (hscaled t).exp hji
  simp only [hz, smul_zero, intervalIntegral.integral_zero]

end Triangular

section RealDiagonal

variable {𝕜 : Type*} [RCLike 𝕜] [LinearOrder n]

/-- A real diagonal entry gives the corresponding divided difference on the coefficient diagonal.
The formula includes the equal-diagonal value of the divided difference. -/
theorem IsUpperTriangular.expColumnCoefficient_apply_diag {A : Matrix n n 𝕜}
    (hA : A.IsUpperTriangular) (d a : ℝ) (i : n) (hii : A i i = (a : 𝕜)) :
    Matrix.expColumnCoefficient A d i i = ((dslope Real.exp a d : ℝ) : 𝕜) := by
  have hscaled (t : ℝ) : ((1 - t) • A).IsUpperTriangular :=
    (blockTriangularSubalgebra ℝ 𝕜 id).smul_mem hA (1 - t)
  have hexp (x : ℝ) : exp (x : 𝕜) = (Real.exp x : 𝕜) := by
    simpa only [RCLike.algebraMap_eq_ofReal, ← Real.exp_eq_exp_ℝ] using
      (NormedSpace.algebraMap_exp_comm (𝔸 := 𝕜) x).symm
  have he (t : ℝ) : exp ((1 - t) • A) i i = (Real.exp ((1 - t) * a) : 𝕜) := by
    rw [(hscaled t).exp_apply_diag, Matrix.smul_apply, hii,
      RCLike.real_smul_eq_coe_mul, ← RCLike.ofReal_mul, hexp]
  have heq (t : ℝ) : Real.exp (t * d) • exp ((1 - t) • A) i i =
      (Real.exp ((1 - t) * a + t * d) : 𝕜) := by
    rw [he, RCLike.real_smul_eq_coe_mul, Real.exp_add, RCLike.ofReal_mul]
    exact mul_comm _ _
  rw [expColumnCoefficient_apply]
  simp_rw [heq]
  rw [RCLike.intervalIntegral_ofReal, ← Real.dslope_exp_eq_integral]

/-- Real diagonal entries make the last-column exponential coefficient invertible.
No distinctness assumption on the diagonal entries is needed. -/
theorem IsUpperTriangular.isUnit_expColumnCoefficient {A : Matrix n n 𝕜}
    (hA : A.IsUpperTriangular) (hreal : ∀ i, RCLike.im (A i i) = 0) (d : ℝ) :
    IsUnit (Matrix.expColumnCoefficient A d) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [(hA.expColumnCoefficient d).det_eq_prod_diag Function.injective_id]
  apply isUnit_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  have hii : A i i = (RCLike.re (A i i) : 𝕜) := by
    simpa only [hreal i, RCLike.ofReal_zero, zero_mul, add_zero] using
      (RCLike.re_add_im (A i i)).symm
  rw [hA.expColumnCoefficient_apply_diag d (RCLike.re (A i i)) i hii]
  exact_mod_cast ne_of_gt (Real.dslope_exp_pos (RCLike.re (A i i)) d)

end RealDiagonal

end Matrix

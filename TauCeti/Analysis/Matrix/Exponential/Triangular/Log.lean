/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Exponential.Triangular.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TauCeti.Analysis.Normed.Algebra.Basic
import TauCeti.Analysis.Normed.Algebra.Exponential
import TauCeti.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Analysis.RCLike.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.DividedDifference

/-!
# The logarithm of an upper-triangular matrix with positive diagonal

The matrix exponential takes upper-triangular matrices with real diagonal bijectively onto
upper-triangular matrices with positive real diagonal. Its inverse is a recursive logarithm:
recover the leading block and the last diagonal entry, then solve for the last column using
`Matrix.expColumnCoefficient`. This coefficient is invertible even for repeated diagonal
entries, so the logarithm requires no separation assumptions. The resulting formula is
real analytic wherever the real parts of the input diagonal entries are nonzero.

## Main results

* `Matrix.triangularLog`: the recursive last-column logarithm.
* `Matrix.isUpperTriangular_triangularLog` and `im_triangularLog_apply_diag`: the output is
  upper triangular with real diagonal.
* `Matrix.triangularLog_apply_diag`: the diagonal is given by the real logarithm.
* `Matrix.triangularLog_apply_castSucc_castSucc`: the logarithm commutes with taking the leading
  principal block.
* `Matrix.triangularLog_apply_castSucc_last`: the last column is recovered by solving the
  exponential column equation.
* `Matrix.triangularLog_exp` and `Matrix.exp_triangularLog`: the two inverse equations.
* `Matrix.bijOn_exp_upperTriangular_realDiagonal`: the exponential bijection on these matrices.
* `Matrix.contDiffAt_triangularLog` and `Matrix.contDiffOn_triangularLog`: real regularity,
  including analyticity, on the open nonzero-real-diagonal domain.

* `Matrix.triangularLog_apply_lt`: the entry recurrence for the logarithm.

## References

* C. F. Van Loan, *Computing Integrals Involving the Matrix Exponential*, IEEE Transactions
  on Automatic Control 23(3) (1978), 395–404, Theorem 1, pp. 395–396, for the block exponential
  formula used to recover the last column.
-/

public noncomputable section

open NormedSpace Set
open scoped Matrix.Norms.Operator ContDiff

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

attribute [local instance] TauCeti.normedAlgebraRatOfReal

private def leadingBlock {n : ℕ} (X : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  X.submatrix Fin.castSucc Fin.castSucc

private def lastColumn {n : ℕ} (X : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) :
    Matrix (Fin n) (Fin 1) 𝕜 :=
  X.submatrix Fin.castSucc (fun _ : Fin 1 ↦ Fin.last n)

/-- The real-diagonal logarithm of a matrix with positive real diagonal.

On upper-triangular matrices with positive real diagonal this is the inverse of `NormedSpace.exp`.
The recursion takes the logarithm of the leading block and of the last diagonal entry, then
solves the last-column equation with `Matrix.expColumnCoefficient`. The same total formula
produces an upper-triangular real-diagonal matrix for arbitrary input. -/
def triangularLog : (n : ℕ) → Matrix (Fin n) (Fin n) 𝕜 → Matrix (Fin n) (Fin n) 𝕜
  | 0, _ => 0
  | n + 1, g =>
    let A := triangularLog n (leadingBlock g)
    let d := Real.log (RCLike.re (g (Fin.last n) (Fin.last n)))
    assembleLastBlock A ((expColumnCoefficient A d)⁻¹ * lastColumn g) d

private theorem triangularLog_succ {n : ℕ} (g : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) :
    triangularLog (n + 1) g =
      assembleLastBlock (triangularLog n (leadingBlock g))
        ((expColumnCoefficient (triangularLog n (leadingBlock g))
          (Real.log (RCLike.re (g (Fin.last n) (Fin.last n)))))⁻¹ * lastColumn g)
        (Real.log (RCLike.re (g (Fin.last n) (Fin.last n)))) := rfl

/-- The logarithm of a leading principal block is the corresponding block of the logarithm. -/
@[simp]
theorem triangularLog_apply_castSucc_castSucc {n : ℕ}
    (g : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) (i j : Fin n) :
    triangularLog (n + 1) g i.castSucc j.castSucc =
      triangularLog n (g.submatrix Fin.castSucc Fin.castSucc) i j := by
  rw [triangularLog_succ]
  simp only [assembleLastBlock_apply_castSucc_castSucc, leadingBlock]

/-- The last column of the triangular logarithm is recovered by inverting the exponential
column coefficient on the logarithm of the leading block. -/
theorem triangularLog_apply_castSucc_last {n : ℕ}
    (g : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) (i : Fin n) :
    triangularLog (n + 1) g i.castSucc (Fin.last n) =
      let A := triangularLog n (g.submatrix Fin.castSucc Fin.castSucc)
      let d := Real.log (RCLike.re (g (Fin.last n) (Fin.last n)))
      ((expColumnCoefficient A d)⁻¹ *
        g.submatrix Fin.castSucc (fun _ : Fin 1 ↦ Fin.last n)) i 0 := by
  rw [triangularLog_succ]
  simp only [assembleLastBlock_apply_castSucc_last, leadingBlock, lastColumn]

/-- The diagonal of the triangular logarithm is obtained by taking real scalar logarithms. -/
@[simp]
theorem triangularLog_apply_diag {n : ℕ} (g : Matrix (Fin n) (Fin n) 𝕜) (i : Fin n) :
    triangularLog n g i i = (Real.log (RCLike.re (g i i)) : 𝕜) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [triangularLog_succ]
      simp only [assembleLastBlock_apply_last_last]
    · rw [triangularLog_apply_castSucc_castSucc, ih, submatrix_apply]

/-- The triangular logarithm is upper triangular for every input. -/
theorem isUpperTriangular_triangularLog (n : ℕ) (g : Matrix (Fin n) (Fin n) 𝕜) :
    (triangularLog n g).IsUpperTriangular := by
  induction n with
  | zero => exact fun {i} ↦ Fin.elim0 i
  | succ n ih =>
    rw [triangularLog_succ]
    exact (ih _).assembleLastBlock _ _

/-- The triangular logarithm has real diagonal for every input. -/
theorem im_triangularLog_apply_diag (n : ℕ) (g : Matrix (Fin n) (Fin n) 𝕜) (i : Fin n) :
    RCLike.im (triangularLog n g i i) = 0 := by
  rw [triangularLog_apply_diag, RCLike.ofReal_im]

/-- The logarithm inverts the exponential on upper-triangular matrices with real diagonal. -/
theorem triangularLog_exp {n : ℕ} {X : Matrix (Fin n) (Fin n) 𝕜}
    (hX : X.IsUpperTriangular) (hreal : ∀ i, RCLike.im (X i i) = 0) :
    triangularLog n (exp X) = X := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    have hLead := hX.submatrix_of_strictMono Fin.strictMono_castSucc
    have hrLead (i : Fin n) : RCLike.im (leadingBlock X i i) = 0 := hreal i.castSucc
    have hA : triangularLog n (leadingBlock (exp X)) = leadingBlock X := by
      rw [leadingBlock, hX.exp_submatrix_castSucc]
      exact ih hLead hrLead
    have hd : Real.log (RCLike.re (exp X (Fin.last n) (Fin.last n))) =
        RCLike.re (X (Fin.last n) (Fin.last n)) := by
      have hlast := RCLike.re_eq_self_of_im_eq_zero (hreal (Fin.last n))
      have hexp := (congrArg NormedSpace.exp hlast.symm).trans (RCLike.exp_ofReal _)
      rw [hX.exp_apply_diag, hexp, RCLike.ofReal_re, Real.log_exp]
    have hcol : lastColumn (exp X) = expColumnCoefficient (leadingBlock X)
        (RCLike.re (X (Fin.last n) (Fin.last n))) * lastColumn X := by
      simpa only [leadingBlock, lastColumn] using
        hX.exp_submatrix_castSucc_last (hreal (Fin.last n))
    rw [triangularLog_succ, hA, hd, hcol]
    have hk : IsUnit (expColumnCoefficient (leadingBlock X)
        (RCLike.re (X (Fin.last n) (Fin.last n)))).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (hLead.isUnit_expColumnCoefficient hrLead _)
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hk]
    exact hX.assembleLastBlock_submatrix (hreal (Fin.last n))

/-- Exponentiating the triangular logarithm recovers an upper-triangular matrix with positive
real diagonal. -/
theorem exp_triangularLog {n : ℕ} {g : Matrix (Fin n) (Fin n) 𝕜}
    (hg : g.IsUpperTriangular) (hreal : ∀ i, RCLike.im (g i i) = 0)
    (hpos : ∀ i, 0 < RCLike.re (g i i)) : exp (triangularLog n g) = g := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    let A := triangularLog n (leadingBlock g)
    let d := Real.log (RCLike.re (g (Fin.last n) (Fin.last n)))
    have hk : IsUnit (expColumnCoefficient A d).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp
        ((isUpperTriangular_triangularLog n (leadingBlock g)).isUnit_expColumnCoefficient
          (im_triangularLog_apply_diag n (leadingBlock g)) d)
    have heA : exp A = leadingBlock g :=
      ih (hg.submatrix_of_strictMono Fin.strictMono_castSucc) (fun i ↦ hreal i.castSucc)
        (fun i ↦ hpos i.castSucc)
    have hd : Real.exp d = RCLike.re (g (Fin.last n) (Fin.last n)) :=
      Real.exp_log (hpos (Fin.last n))
    rw [triangularLog_succ]
    calc
      exp (assembleLastBlock A ((expColumnCoefficient A d)⁻¹ * lastColumn g) d) =
          assembleLastBlock (exp A)
            (expColumnCoefficient A d * ((expColumnCoefficient A d)⁻¹ * lastColumn g))
            (Real.exp d) := exp_assembleLastBlock _ _ _
      _ = assembleLastBlock (leadingBlock g) (lastColumn g)
          (RCLike.re (g (Fin.last n) (Fin.last n))) := by
        rw [heA, Matrix.mul_nonsing_inv_cancel_left _ _ hk, hd]
      _ = g := hg.assembleLastBlock_submatrix (hreal (Fin.last n))

/-- The matrix exponential is a bijection between upper-triangular matrices with real diagonal
and upper-triangular matrices with positive real diagonal. -/
theorem bijOn_exp_upperTriangular_realDiagonal (n : ℕ) :
    BijOn exp
      {X : Matrix (Fin n) (Fin n) 𝕜 | X.IsUpperTriangular ∧ ∀ i, RCLike.im (X i i) = 0}
      {g | g.IsUpperTriangular ∧ ∀ i, RCLike.im (g i i) = 0 ∧ 0 < RCLike.re (g i i)} := by
  refine ⟨?_, ?_, ?_⟩
  · rintro X ⟨hX, hreal⟩
    exact ⟨hX.exp, fun i ↦ (RCLike.pos_iff.mp (hX.exp_apply_diag_pos i (hreal i))).symm⟩
  · intro X hX Y hY h
    exact (triangularLog_exp hX.1 hX.2).symm.trans
      ((congrArg (triangularLog n) h).trans (triangularLog_exp hY.1 hY.2))
  · intro g hg
    exact ⟨triangularLog n g,
      ⟨isUpperTriangular_triangularLog n g, im_triangularLog_apply_diag n g⟩,
      exp_triangularLog hg.1 (fun i ↦ (hg.2 i).1) (fun i ↦ (hg.2 i).2)⟩

private def leadingCLM (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜 →L[ℝ] Matrix (Fin n) (Fin n) 𝕜 where
  toLinearMap :=
    { toFun := leadingBlock
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  cont := continuous_matrix fun i j ↦ continuous_id.matrix_elem i.castSucc j.castSucc

@[simp] private theorem leadingCLM_apply (n : ℕ) (X : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) :
    leadingCLM n X = leadingBlock X := rfl

private def columnCLM (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜 →L[ℝ] Matrix (Fin n) (Fin 1) 𝕜 where
  toLinearMap :=
    { toFun := lastColumn
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  cont := continuous_matrix fun i _ ↦ continuous_id.matrix_elem i.castSucc (Fin.last n)

@[simp] private theorem columnCLM_apply (n : ℕ) (X : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) :
    columnCLM n X = lastColumn X := rfl

private def lastDiagonalCLM (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜 →L[ℝ] 𝕜 where
  toLinearMap := Matrix.entryLinearMap ℝ 𝕜 (Fin.last n) (Fin.last n)
  cont := continuous_id.matrix_elem _ _

@[simp] private theorem lastDiagonalCLM_apply (n : ℕ)
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) :
    lastDiagonalCLM n X = X (Fin.last n) (Fin.last n) := rfl

private theorem contDiffAt_logLastDiagonal (m : ℕ∞ω) {n : ℕ}
    {g : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜}
    (hg : RCLike.re (g (Fin.last n) (Fin.last n)) ≠ 0) :
    ContDiffAt ℝ m (fun X ↦ Real.log (RCLike.re (X (Fin.last n) (Fin.last n)))) g := by
  have hr : ContDiffAt ℝ m (fun X ↦ RCLike.re (X (Fin.last n) (Fin.last n))) g := by
    have h := (RCLike.reCLM (K := 𝕜)).contDiff.contDiffAt.comp g
      (lastDiagonalCLM (𝕜 := 𝕜) n).contDiff.contDiffAt (n := m)
    convert h using 1
    funext X
    exact congrArg RCLike.re (lastDiagonalCLM_apply n X).symm
  exact hr.log hg

private def lastColumnMulCLM (n : ℕ) :
    Matrix (Fin n) (Fin n) 𝕜 →L[ℝ]
      Matrix (Fin n) (Fin 1) 𝕜 →L[ℝ] Matrix (Fin n) (Fin 1) 𝕜 :=
  (mulLinearMap ℝ).mkContinuous₂ 1 (fun A B ↦ by
    -- Expose the matrix product in the bundled multiplication map before bounding its norm.
    change ‖A * B‖ ≤ 1 * ‖A‖ * ‖B‖
    simpa only [one_mul] using Matrix.linfty_opNorm_mul A B)

@[simp] private theorem lastColumnMulCLM_apply (n : ℕ)
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin 1) 𝕜) :
    lastColumnMulCLM n A B = A * B := rfl

/-- The triangular logarithm has every real regularity where the real parts of the diagonal
entries are nonzero. The input may be an arbitrary matrix. -/
theorem contDiffAt_triangularLog (m : ℕ∞ω) {n : ℕ}
    {g : Matrix (Fin n) (Fin n) 𝕜} (hg : ∀ i, (RCLike.re (g i i)) ≠ 0) :
    ContDiffAt ℝ m (triangularLog n) g := by
  induction n with
  | zero => exact contDiffAt_const
  | succ n ih =>
    -- Use the induction hypothesis for the leading block. Recover the diagonal and last
    -- column by smooth operations, then assemble the blocks.
    have hA : ContDiffAt ℝ m (fun X ↦ triangularLog n (leadingBlock X)) g := by
      have hLead : ContDiffAt ℝ m (leadingCLM (𝕜 := 𝕜) n) g :=
        (leadingCLM (𝕜 := 𝕜) n).contDiff.contDiffAt
      have h := (ih (g := leadingBlock g) (fun i ↦ hg i.castSucc)).comp g hLead
      convert h using 1
      funext X
      exact congrArg (triangularLog n) (leadingCLM_apply n X).symm
    have hd := contDiffAt_logLastDiagonal m (hg (Fin.last n))
    let F := fun X : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜 ↦
      expColumnCoefficient (triangularLog n (leadingBlock X))
        (Real.log (RCLike.re (X (Fin.last n) (Fin.last n))))
    have hF : ContDiffAt ℝ m F g :=
      (Matrix.contDiff_expColumnCoefficient m).contDiffAt.comp g (hA.prodMk hd)
    have hunit : IsUnit (F g) :=
      (isUpperTriangular_triangularLog n (leadingBlock g)).isUnit_expColumnCoefficient
        (im_triangularLog_apply_diag n (leadingBlock g)) _
    have hinv : ContDiffAt ℝ m (fun X ↦ (F X)⁻¹) g := by
      simpa only [Function.comp_def, Matrix.nonsing_inv_eq_ringInverse] using
        (contDiffAt_ringInverse ℝ hunit.unit).comp g hF
    have hcol : ContDiffAt ℝ m lastColumn g := by
      convert (columnCLM (𝕜 := 𝕜) n).contDiff.contDiffAt using 1
      funext X
      exact (columnCLM_apply n X).symm
    have hB : ContDiffAt ℝ m (fun X ↦ (F X)⁻¹ * lastColumn X) g := by
      convert (lastColumnMulCLM (𝕜 := 𝕜) n).isBoundedBilinearMap.contDiff.contDiffAt.comp g
        (hinv.prodMk hcol) using 1
      funext X
      exact (lastColumnMulCLM_apply n (F X)⁻¹ (lastColumn X)).symm
    have h := (assembleLastBlockCLM (𝕜 := 𝕜) n).contDiff.contDiffAt.comp g
      ((hA.prodMk hB).prodMk hd)
    convert h using 1
    funext X
    dsimp only [Function.comp_def]
    exact (triangularLog_succ X).trans (assembleLastBlockCLM_apply n
      ((triangularLog n (leadingBlock X), (F X)⁻¹ * lastColumn X),
        Real.log (RCLike.re (X (Fin.last n) (Fin.last n))))).symm

/-- The triangular logarithm has every real regularity on the nonzero-real-diagonal domain. -/
theorem contDiffOn_triangularLog (m : ℕ∞ω) (n : ℕ) :
    ContDiffOn ℝ m (triangularLog (𝕜 := 𝕜) n) {g | ∀ i, RCLike.re (g i i) ≠ 0} :=
  fun _ hg ↦ (contDiffAt_triangularLog m hg).contDiffWithinAt

/-- A positive triangular matrix's logarithm is recovered in increasing gap order. Each
entry is obtained by subtracting the smaller-gap remainder and dividing by the positive
exponential divided difference, which includes its equal-diagonal value. -/
theorem triangularLog_apply_lt {m : ℕ} {g : Matrix (Fin m) (Fin m) 𝕜}
    (hg : g.IsUpperTriangular) (hreal : ∀ k, RCLike.im (g k k) = 0)
    (hpos : ∀ k, 0 < RCLike.re (g k k)) (i j : Fin m) (hij : i < j) :
    triangularLog m g i j =
      (g i j - triangularExpRemainder (triangularLog m g) i j hij) /
        ((dslope Real.exp (Real.log (RCLike.re (g i i)))
          (Real.log (RCLike.re (g j j))) : ℝ) : 𝕜) := by
  have h := (isUpperTriangular_triangularLog m g).exp_apply_eq_dslope_mul_add
    i j hij (fun k _ ↦ im_triangularLog_apply_diag m g k)
  rw [exp_triangularLog hg hreal hpos, triangularLog_apply_diag, triangularLog_apply_diag,
    RCLike.ofReal_re, RCLike.ofReal_re] at h
  have hq : ((dslope Real.exp (Real.log (RCLike.re (g i i)))
      (Real.log (RCLike.re (g j j))) : ℝ) : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (ne_of_gt (Real.dslope_exp_pos _ _))
  apply (eq_div_iff hq).2
  rw [mul_comm]
  exact eq_sub_iff_add_eq.mpr h.symm

end Matrix

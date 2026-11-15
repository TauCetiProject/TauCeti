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
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Interval.Set.OrdConnected
import TauCeti.Analysis.RCLike.Basic
public import TauCeti.Order.Interval.Set.Fin
import TauCeti.Topology.Algebra.Module.Matrix

/-!
# The last-column coefficient of a triangular exponential

For an upper block matrix with final diagonal entry `d`, the exponential is linear in its
last off-diagonal column. Its coefficient is the integral of the exponential of the leading
block, weighted by the scalar exponential of `d`. The integral, block identity, triangularity,
and joint regularity hold over every complete real normed coefficient algebra. For real or
complex coefficients, an upper-triangular leading block with real diagonal has an invertible
coefficient, including when diagonal entries repeat. Restricting to a principal
interval gives the corresponding entry formula and its smaller-gap remainder.

## Main definitions

* `Matrix.expColumnCoefficient`: the exponential-weight integral acting on the last column.

## Main results

* `Matrix.expColumnCoefficient_def`: the matrix-valued integral formula.
* `Matrix.expColumnCoefficient_apply`: the entrywise integral formula.
* `Matrix.expColumnCoefficient_eq_toBlocks₁₂_exp`: the coefficient as an exponential block.
* `Matrix.toBlocks₁₂_exp_fromBlocks_real_smul_one`: the upper-right block is the coefficient
  times the original rectangular block.
* `Matrix.exp_fromBlocks_zero₂₁_real_smul_one`: the full block exponential.
* `Matrix.fromBlocksZero₂₁SmulOneCLM`: the linear block insertion used in the coefficient.
* `Matrix.contDiff_expColumnCoefficient`: joint regularity, including analyticity.
* `Matrix.BlockTriangular.expColumnCoefficient`: the coefficient preserves block triangularity.
* `Matrix.IsUpperTriangular.expColumnCoefficient_apply_diag`: real diagonal entries give
  divided differences, including the equal-entry value.
* `Matrix.IsUpperTriangular.isUnit_expColumnCoefficient`: real diagonal entries imply
  invertibility without a distinctness assumption.
* `Matrix.IsUpperTriangular.exp_submatrix_castSucc_last`: the last-column formula on `Fin`.
* `Matrix.assembleLastBlock` and `Matrix.exp_assembleLastBlock`: assembling and exponentiating
  an upper block matrix indexed by `Fin (n + 1)`.
* `Matrix.triangularExpRemainder`, `triangularExpRemainder_eq_sum`, and
  `triangularExpRemainder_congr`: the smaller-gap remainder and its sum formula.
* `Matrix.IsUpperTriangular.exp_apply_eq_dslope_mul_add`: the entry coefficient, including
  its repeated-diagonal value by `dslope_same` and `Real.deriv_exp`.

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

/-- The matrix `∫₀¹ exp(t d) • exp((1 - t) • A) dt`. For the upper block matrix
`M = fromBlocks A B 0 (d • 1)`, its product with `B` is the upper-right block of `exp M`;
see `Matrix.toBlocks₁₂_exp_fromBlocks_real_smul_one`. -/
def expColumnCoefficient (A : Matrix n n R) (d : ℝ) : Matrix n n R :=
  ∫ t in (0 : ℝ)..1, Real.exp (t * d) • exp ((1 - t) • A)

omit [CompleteSpace R] in
/-- The last-column coefficient equals its defining matrix-valued integral. -/
-- Keep the integral equations as explicit rewrites so structural laws retain their normal form.
theorem expColumnCoefficient_def (A : Matrix n n R) (d : ℝ) :
    expColumnCoefficient A d =
      ∫ t in (0 : ℝ)..1, Real.exp (t * d) • exp ((1 - t) • A) := by rfl

/-- The coefficient integrand is interval integrable for the operator norm. -/
private theorem intervalIntegrable_expColumnCoefficient_integrand
    (A : Matrix n n R) (d : ℝ) :
    letI : ENormedAddMonoid (Matrix n n R) := NormedAddGroup.toENormedAddMonoid
    IntervalIntegrable (fun t : ℝ ↦ Real.exp (t * d) • exp ((1 - t) • A)) volume 0 1 := by
  let : ENormedAddMonoid (Matrix n n R) := NormedAddGroup.toENormedAddMonoid
  exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- Each coefficient entry is the scalar integral of the corresponding exponential entry. -/
theorem expColumnCoefficient_apply (A : Matrix n n R) (d : ℝ) (i j : n) :
    expColumnCoefficient A d i j =
      ∫ t in (0 : ℝ)..1, Real.exp (t * d) • exp ((1 - t) • A) i j := by
  -- Use the extended norm induced by the operator norm rather than the entrywise instance.
  let : ENormedAddMonoid (Matrix n n R) := NormedAddGroup.toENormedAddMonoid
  have hi := intervalIntegrable_expColumnCoefficient_integrand A d
  let e : Matrix n n R →L[ℝ] R :=
    { toLinearMap := entryLinearMap ℝ R i j
      cont := continuous_id.matrix_elem i j }
  exact (e.intervalIntegral_comp_comm hi).symm

/-- With a real scalar final diagonal block, the upper-right exponential block is the
column coefficient times the original rectangular block. Empty block sizes are allowed. -/
theorem toBlocks₁₂_exp_fromBlocks_real_smul_one {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix n n R) (B : Matrix n m R) (d : ℝ) :
    (exp (fromBlocks A B 0 (d • (1 : Matrix m m R)))).toBlocks₁₂ =
      expColumnCoefficient A d * B := by
  -- Use the extended norm induced by the operator norm rather than the entrywise instance.
  let : ENormedAddMonoid (Matrix n n R) := NormedAddGroup.toENormedAddMonoid
  have hi := intervalIntegrable_expColumnCoefficient_integrand A d
  let L : Matrix n n R →L[ℝ] Matrix n m R :=
    { toLinearMap := mulRightLinearMap n ℝ B
      cont := continuous_id.matrix_mul continuous_const }
  have h : (∫ t in (0 : ℝ)..1, (Real.exp (t * d) • exp ((1 - t) • A)) * B) =
      (∫ t in (0 : ℝ)..1, Real.exp (t * d) • exp ((1 - t) • A)) * B := by
    exact L.intervalIntegral_comp_comm hi
  -- This typed specialization pins the operator-norm matrix ring instance so that
  -- the general scalar identity matches the matrix exponential in simp only.
  have hexp (x : ℝ) : exp (x • (1 : Matrix m m R)) = Real.exp x • 1 :=
    NormedSpace.exp_real_smul_one x
  rw [toBlocks₁₂_exp_fromBlocks_zero₂₁, expColumnCoefficient_def]
  simp only [smul_smul, hexp, Matrix.mul_smul, Matrix.mul_one]
  simpa only [Matrix.smul_mul] using h

/-- The exponential of an upper block matrix with a real scalar final diagonal block. -/
theorem exp_fromBlocks_zero₂₁_real_smul_one {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix n n R) (B : Matrix n m R) (d : ℝ) :
    exp (fromBlocks A B 0 (d • (1 : Matrix m m R))) =
      fromBlocks (exp A) (expColumnCoefficient A d * B) 0
        (Real.exp d • (1 : Matrix m m R)) := by
  -- The typed scalar identity selects the operator-norm matrix structure.
  have he : exp (d • (1 : Matrix m m R)) = Real.exp d • (1 : Matrix m m R) :=
    NormedSpace.exp_real_smul_one d
  rw [exp_fromBlocks_zero₂₁_eq_fromBlocks, toBlocks₁₂_exp_fromBlocks_real_smul_one, he]

/-- The column coefficient equals the upper-right block of the corresponding matrix exponential. -/
theorem expColumnCoefficient_eq_toBlocks₁₂_exp (A : Matrix n n R) (d : ℝ) :
    expColumnCoefficient A d =
      (exp (fromBlocks A (1 : Matrix n n R) (0 : Matrix n n R)
        (d • (1 : Matrix n n R)))).toBlocks₁₂ := by
  rw [toBlocks₁₂_exp_fromBlocks_real_smul_one, Matrix.mul_one]

/-- Insert a leading block, an upper-right block, and a real scalar final block
into an upper two-block matrix as a continuous linear map. -/
def fromBlocksZero₂₁SmulOneCLM {m : Type*} [DecidableEq m] :
    ((Matrix n n R × Matrix n m R) × ℝ) →L[ℝ]
      Matrix (n ⊕ m) (n ⊕ m) R where
  toLinearMap :=
    { toFun := fun p ↦ fromBlocks p.1.1 p.1.2 0 (p.2 • (1 : Matrix m m R))
      map_add' := by
        intro p q
        simp only [Prod.fst_add, Prod.snd_add, add_smul, fromBlocks_add, zero_add]
      map_smul' := by
        intro c p
        simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply,
          fromBlocks_smul, smul_zero, smul_smul, smul_eq_mul] }
  cont := continuous_matrix fun i j ↦ by
    cases i with
    | inl i =>
      cases j with
      | inl j => exact continuous_fst.fst.matrix_elem i j
      | inr j => exact continuous_fst.snd.matrix_elem i j
    | inr i =>
      cases j with
      | inl j => exact continuous_const
      | inr j => exact (continuous_snd.smul continuous_const).matrix_elem i j

omit [Fintype n] [CompleteSpace R] [DecidableEq n] in
/-- Application of `fromBlocksZero₂₁SmulOneCLM` assembles the four specified matrix blocks. -/
@[simp]
theorem fromBlocksZero₂₁SmulOneCLM_apply {m : Type*} [DecidableEq m]
    (p : (Matrix n n R × Matrix n m R) × ℝ) :
    fromBlocksZero₂₁SmulOneCLM p = fromBlocks p.1.1 p.1.2 0 (p.2 • (1 : Matrix m m R)) := by rfl

/-- The last-column exponential coefficient is jointly smooth in the leading block and
its final real diagonal entry, with arbitrary finite, smooth, or analytic regularity. -/
@[fun_prop]
theorem contDiff_expColumnCoefficient (m : ℕ∞ω) : ContDiff ℝ m
    (fun p : Matrix n n R × ℝ ↦ expColumnCoefficient p.1 p.2) := by
  have he : ContDiff ℝ m (exp : Matrix (n ⊕ n) (n ⊕ n) R → _) := contDiff_exp ℝ
  have hT : ContDiff ℝ m (fun p : Matrix n n R × ℝ ↦
      fromBlocksZero₂₁SmulOneCLM ((p.1, (0 : Matrix n n R)), p.2)) :=
    (fromBlocksZero₂₁SmulOneCLM (n := n) (m := n) (R := R)).contDiff.comp
      ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd)
  have hP : ContDiff ℝ m (fun A : Matrix (n ⊕ n) (n ⊕ n) R ↦ toBlocks₁₂CLM ℝ A) :=
    (toBlocks₁₂CLM ℝ (R := R) (m := n) (n := n) (l := n) (o := n)).contDiff
  have h := hP.comp (he.comp (hT.add
    (contDiff_const (c := fromBlocks (0 : Matrix n n R) (1 : Matrix n n R) 0 0))))
  have hid (p : Matrix n n R × ℝ) :
      fromBlocksZero₂₁SmulOneCLM ((p.1, (0 : Matrix n n R)), p.2) +
        fromBlocks (0 : Matrix n n R) (1 : Matrix n n R) 0 0 =
        fromBlocks p.1 1 0 (p.2 • (1 : Matrix n n R)) := by
    simp only [fromBlocksZero₂₁SmulOneCLM_apply, fromBlocks_add, add_zero, zero_add]
  simpa only [Function.comp_def, hid, toBlocks₁₂CLM_apply,
    ← Matrix.expColumnCoefficient_eq_toBlocks₁₂_exp] using h

end Coefficient

section Triangular

variable [DecidableEq n] {α : Type*} [LinearOrder α] {b : n → α}

/-- The last-column exponential coefficient preserves any block-triangular structure. -/
theorem BlockTriangular.expColumnCoefficient {A : Matrix n n R}
    (hA : A.BlockTriangular b) (d : ℝ) : (expColumnCoefficient A d).BlockTriangular b := by
  intro i j hji
  rw [expColumnCoefficient_apply]
  have hscaled (t : ℝ) : ((1 - t) • A).BlockTriangular b :=
    (blockTriangularSubalgebra ℝ R b).smul_mem hA (1 - t)
  have hz (t : ℝ) : NormedSpace.exp ((1 - t) • A) i j = 0 := (hscaled t).exp hji
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
  have he (t : ℝ) : exp ((1 - t) • A) i i = (Real.exp ((1 - t) * a) : 𝕜) := by
    rw [(hscaled t).exp_apply_diag, Matrix.smul_apply, hii,
      RCLike.real_smul_eq_coe_mul, ← RCLike.ofReal_mul, RCLike.exp_ofReal]
  have heq (t : ℝ) : Real.exp (t * d) • exp ((1 - t) • A) i i =
      (Real.exp ((1 - t) * a + t * d) : 𝕜) := by
    rw [he, RCLike.real_smul_eq_coe_mul, Real.exp_add, RCLike.ofReal_mul]
    ring
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
    exact (RCLike.re_eq_self_of_im_eq_zero (hreal i)).symm
  rw [hA.expColumnCoefficient_apply_diag d (RCLike.re (A i i)) i hii]
  exact_mod_cast ne_of_gt (Real.dslope_exp_pos (RCLike.re (A i i)) d)

end RealDiagonal

section EntryRecurrence

variable {𝕜 : Type*} [RCLike 𝕜]

private def joinLastBlock {n : ℕ} (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) 𝕜) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜 :=
  Matrix.reindexAlgEquiv 𝕜 𝕜 finSumFinEquiv M

@[simp] private theorem join_castSucc_castSucc {n : ℕ}
    (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) 𝕜) (i j : Fin n) :
    joinLastBlock M i.castSucc j.castSucc = M (Sum.inl i) (Sum.inl j) := by
  simp [joinLastBlock, Matrix.reindex, Matrix.submatrix, finSumFinEquiv_symm_apply_castSucc]

@[simp] private theorem join_castSucc_last {n : ℕ}
    (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) 𝕜) (i : Fin n) :
    joinLastBlock M i.castSucc (Fin.last n) = M (Sum.inl i) (Sum.inr 0) := by
  simp [joinLastBlock, Matrix.reindex, Matrix.submatrix, finSumFinEquiv_symm_apply_castSucc,
    finSumFinEquiv_symm_last]

@[simp] private theorem join_last_castSucc {n : ℕ}
    (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) 𝕜) (j : Fin n) :
    joinLastBlock M (Fin.last n) j.castSucc = M (Sum.inr 0) (Sum.inl j) := by
  simp [joinLastBlock, Matrix.reindex, Matrix.submatrix, finSumFinEquiv_symm_apply_castSucc,
    finSumFinEquiv_symm_last]

@[simp] private theorem join_last_last {n : ℕ}
    (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) 𝕜) :
    joinLastBlock M (Fin.last n) (Fin.last n) = M (Sum.inr 0) (Sum.inr 0) := by
  simp [joinLastBlock, Matrix.reindex, Matrix.submatrix, finSumFinEquiv_symm_last]

private theorem exp_join {n : ℕ} (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) 𝕜) :
    exp (joinLastBlock M) = joinLastBlock (exp M) := by
  let e := Matrix.reindexAlgEquiv 𝕜 𝕜 (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))
  have hc : Continuous e := continuous_id.matrix_reindex finSumFinEquiv finSumFinEquiv
  exact (NormedSpace.map_exp e hc M).symm

/-- Assemble a finite upper block matrix with a scalar last diagonal entry. -/
def assembleLastBlock {n : ℕ} (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin 1) 𝕜)
    (d : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜 :=
  joinLastBlock (fromBlocks A B 0 (d • (1 : Matrix (Fin 1) (Fin 1) 𝕜)))

/-- The leading entries of the assembled matrix come from the leading block. -/
@[simp] theorem assembleLastBlock_apply_castSucc_castSucc {n : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin 1) 𝕜) (d : ℝ)
    (i j : Fin n) : assembleLastBlock A B d i.castSucc j.castSucc = A i j := by
  simp only [assembleLastBlock, join_castSucc_castSucc, fromBlocks_apply₁₁]

/-- The final column above the diagonal comes from the upper-right block. -/
@[simp] theorem assembleLastBlock_apply_castSucc_last {n : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin 1) 𝕜) (d : ℝ)
    (i : Fin n) : assembleLastBlock A B d i.castSucc (Fin.last n) = B i 0 := by
  simp only [assembleLastBlock, join_castSucc_last, fromBlocks_apply₁₂]

/-- The final row to the left of the diagonal is zero. -/
@[simp] theorem assembleLastBlock_apply_last_castSucc {n : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin 1) 𝕜) (d : ℝ)
    (j : Fin n) : assembleLastBlock A B d (Fin.last n) j.castSucc = 0 := by
  simp only [assembleLastBlock, join_last_castSucc, fromBlocks_apply₂₁, Matrix.zero_apply]

/-- The final diagonal entry is the given real scalar. -/
@[simp] theorem assembleLastBlock_apply_last_last {n : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin 1) 𝕜) (d : ℝ) :
    assembleLastBlock A B d (Fin.last n) (Fin.last n) = (d : 𝕜) := by
  simp [assembleLastBlock, RCLike.real_smul_eq_coe_mul]

/-- Appending a last column and a real final diagonal entry preserves upper
triangularity. -/
theorem IsUpperTriangular.assembleLastBlock {n : ℕ} {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsUpperTriangular) (B : Matrix (Fin n) (Fin 1) 𝕜) (d : ℝ) :
    (Matrix.assembleLastBlock A B d).IsUpperTriangular := by
  intro i j
  refine Fin.lastCases ?_ (fun i ↦ ?_) i <;>
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
  · intro h
    exact (lt_irrefl _ h).elim
  · intro _
    simp only [assembleLastBlock_apply_last_castSucc]
  · intro h
    exact (not_lt_of_ge (le_of_lt (Fin.castSucc_lt_last _)) h).elim
  · intro h
    simpa only [assembleLastBlock_apply_castSucc_castSucc] using
      hA (i := i) (j := j) (by exact_mod_cast h)

/-- An upper-triangular matrix with real final diagonal entry is recovered from its
leading block, final column above the diagonal, and final diagonal entry. -/
theorem IsUpperTriangular.assembleLastBlock_submatrix {n : ℕ}
    {X : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜} (hX : X.IsUpperTriangular)
    (hreal : RCLike.im (X (Fin.last n) (Fin.last n)) = 0) :
    Matrix.assembleLastBlock (X.submatrix Fin.castSucc Fin.castSucc)
      (X.submatrix Fin.castSucc (fun _ : Fin 1 ↦ Fin.last n))
      (RCLike.re (X (Fin.last n) (Fin.last n))) = X := by
  ext i j
  refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> refine Fin.lastCases ?_ (fun j ↦ ?_) j
  · rw [assembleLastBlock_apply_last_last]
    exact RCLike.re_eq_self_of_im_eq_zero hreal
  · rw [assembleLastBlock_apply_last_castSucc]
    exact (hX (Fin.castSucc_lt_last j)).symm
  · simp only [assembleLastBlock_apply_castSucc_last, submatrix_apply]
  · simp only [assembleLastBlock_apply_castSucc_castSucc, submatrix_apply]

/-- Exponentiating the assembled matrix exponentiates the diagonal blocks and
multiplies the final column by the exponential coefficient. -/
theorem exp_assembleLastBlock {n : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin 1) 𝕜) (d : ℝ) :
    exp (assembleLastBlock A B d) =
      assembleLastBlock (exp A) (expColumnCoefficient A d * B) (Real.exp d) := by
  rw [assembleLastBlock, exp_join, exp_fromBlocks_zero₂₁_real_smul_one, assembleLastBlock]

private def joinCLM (n : ℕ) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) 𝕜 →L[ℝ] Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜 where
  toLinearMap := (Matrix.reindexLinearEquiv ℝ 𝕜 finSumFinEquiv finSumFinEquiv).toLinearMap
  cont := continuous_id.matrix_reindex finSumFinEquiv finSumFinEquiv

@[simp] private theorem joinCLM_apply (n : ℕ) (X : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) 𝕜) :
    joinCLM n X = joinLastBlock X := rfl

/-- Assembling an upper block matrix is continuous and real linear in its three inputs. -/
def assembleLastBlockCLM (n : ℕ) :
    ((Matrix (Fin n) (Fin n) 𝕜 × Matrix (Fin n) (Fin 1) 𝕜) × ℝ) →L[ℝ]
      Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜 :=
  (joinCLM (𝕜 := 𝕜) n).comp (fromBlocksZero₂₁SmulOneCLM (n := Fin n) (m := Fin 1) (R := 𝕜))

/-- The block assembly map evaluates to the assembled matrix. -/
@[simp] theorem assembleLastBlockCLM_apply (n : ℕ)
    (p : (Matrix (Fin n) (Fin n) 𝕜 × Matrix (Fin n) (Fin 1) 𝕜) × ℝ) :
    assembleLastBlockCLM n p = assembleLastBlock p.1.1 p.1.2 p.2 := by
  rw [assembleLastBlockCLM, ContinuousLinearMap.comp_apply, fromBlocksZero₂₁SmulOneCLM_apply,
    joinCLM_apply, assembleLastBlock]

/-- On an upper-triangular matrix with real last diagonal entry, the exponential's last
column above the diagonal is obtained by multiplying by the column coefficient. -/
theorem IsUpperTriangular.exp_submatrix_castSucc_last {n : ℕ}
    {X : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜} (hX : X.IsUpperTriangular)
    (hreal : RCLike.im (X (Fin.last n) (Fin.last n)) = 0) :
    (exp X).submatrix Fin.castSucc (fun _ : Fin 1 ↦ Fin.last n) =
      expColumnCoefficient (X.submatrix Fin.castSucc Fin.castSucc)
        (RCLike.re (X (Fin.last n) (Fin.last n))) *
        X.submatrix Fin.castSucc (fun _ : Fin 1 ↦ Fin.last n) := by
  have hexp := congrArg NormedSpace.exp (hX.assembleLastBlock_submatrix hreal)
  rw [exp_assembleLastBlock] at hexp
  rw [← hexp]
  ext i j
  simp only [submatrix_apply, assembleLastBlock_apply_castSucc_last, Fin.eq_zero j]

-- The only omitted last-column term is the maximal gap, at row zero.
private def expCornerRemainder {n : ℕ} (X : Matrix (Fin (n + 2)) (Fin (n + 2)) 𝕜) : 𝕜 :=
  ∑ k : Fin n,
    expColumnCoefficient (X.submatrix Fin.castSucc Fin.castSucc)
      (RCLike.re (X (Fin.last (n + 1)) (Fin.last (n + 1)))) 0 k.succ *
      X k.succ.castSucc (Fin.last (n + 1))

private theorem expCornerRemainder_congr {n : ℕ} {X Y : Matrix (Fin (n + 2)) (Fin (n + 2)) 𝕜}
    (hXY : ∀ i j, j.val - i.val < n + 1 → X i j = Y i j) :
    expCornerRemainder X = expCornerRemainder Y := by
  have hlead : X.submatrix Fin.castSucc Fin.castSucc =
      Y.submatrix Fin.castSucc Fin.castSucc := by
    ext i j
    exact hXY i.castSucc j.castSucc (by
      have hi := i.isLt
      have hj := j.isLt
      simp only [Fin.val_castSucc]
      omega)
  have hdiag : X (Fin.last (n + 1)) (Fin.last (n + 1)) =
      Y (Fin.last (n + 1)) (Fin.last (n + 1)) := hXY _ _ (by simp)
  simp only [expCornerRemainder, hlead, hdiag]
  apply Finset.sum_congr rfl
  intro k _hk
  congr 1
  apply hXY
  have hk := k.isLt
  simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last]
  omega

private theorem triangular_corner_exp {n : ℕ} {X : Matrix (Fin (n + 2)) (Fin (n + 2)) 𝕜}
    (hX : X.IsUpperTriangular) (hreal : ∀ i, RCLike.im (X i i) = 0) :
    exp X 0 (Fin.last (n + 1)) =
      ((dslope Real.exp (RCLike.re (X 0 0))
          (RCLike.re (X (Fin.last (n + 1)) (Fin.last (n + 1)))) : ℝ) : 𝕜) *
        X 0 (Fin.last (n + 1)) + expCornerRemainder X := by
  let A := X.submatrix Fin.castSucc Fin.castSucc
  have hA : A.IsUpperTriangular := hX.submatrix_of_strictMono Fin.strictMono_castSucc
  have h00 : A 0 0 = (RCLike.re (A 0 0) : 𝕜) :=
    (RCLike.re_eq_self_of_im_eq_zero (hreal (Fin.castSucc 0))).symm
  have hd := hA.expColumnCoefficient_apply_diag
    (RCLike.re (X (Fin.last (n + 1)) (Fin.last (n + 1)))) (RCLike.re (A 0 0)) 0 h00
  have hc := congrArg (fun M : Matrix (Fin (n + 1)) (Fin 1) 𝕜 ↦ M 0 0)
    (hX.exp_submatrix_castSucc_last (hreal (Fin.last (n + 1))))
  simp only [submatrix_apply, Matrix.mul_apply, Fin.sum_univ_succ] at hc
  rw [hd] at hc
  simpa only [A, submatrix_apply, Fin.castSucc_zero, expCornerRemainder] using hc

/-- On the principal interval from `i` to `j`, sum the first row of the column coefficient
times the last-column entries, omitting the term containing `X i j`. For upper-triangular `X`
with real diagonal this is the remainder in `IsUpperTriangular.exp_apply_eq_dslope_mul_add`. -/
def triangularExpRemainder {m : ℕ} (X : Matrix (Fin m) (Fin m) 𝕜)
    (i j : Fin m) (hij : i < j) : 𝕜 :=
  expCornerRemainder (X.submatrix (Fin.intervalOrderEmbOfLt i j hij)
    (Fin.intervalOrderEmbOfLt i j hij))

/-- The remainder is the last-column coefficient sum on the principal interval, with
the term for the first row omitted. -/
theorem triangularExpRemainder_eq_sum {m : ℕ} (X : Matrix (Fin m) (Fin m) 𝕜)
    (i j : Fin m) (hij : i < j) :
    triangularExpRemainder X i j hij =
      let e := Fin.intervalOrderEmbOfLt i j hij
      ∑ k : Fin (j.val - i.val - 1),
        expColumnCoefficient (X.submatrix (e ∘ Fin.castSucc) (e ∘ Fin.castSucc))
          (RCLike.re (X j j)) 0 k.succ * X (e k.succ.castSucc) j := by
  simp only [triangularExpRemainder, expCornerRemainder, submatrix_submatrix,
    submatrix_apply, Fin.intervalOrderEmbOfLt_apply_last]

/-- The triangular exponential remainder only depends on entries at strictly smaller gaps. -/
theorem triangularExpRemainder_congr {m : ℕ} {X Y : Matrix (Fin m) (Fin m) 𝕜}
    (i j : Fin m) (hij : i < j)
    (hXY : ∀ a b, b.val - a.val < j.val - i.val → X a b = Y a b) :
    triangularExpRemainder X i j hij = triangularExpRemainder Y i j hij := by
  apply expCornerRemainder_congr
  intro a b hab
  apply hXY
  simp only [Fin.intervalOrderEmbOfLt_apply_val]
  omega

/-- In the `(i,j)` entry of the exponential, the coefficient of `X i j` is the divided
difference of the real exponential at the two diagonal entries. The remaining terms use
only entries at smaller gaps. The diagonal need only be real on the interval from `i` to `j`.
At equal diagonal entries, `dslope_same` and `Real.deriv_exp` give the coefficient
`Real.exp (RCLike.re (X i i))`. -/
theorem IsUpperTriangular.exp_apply_eq_dslope_mul_add {m : ℕ} {X : Matrix (Fin m) (Fin m) 𝕜}
    (hX : X.IsUpperTriangular) (i j : Fin m) (hij : i < j)
    (hreal : ∀ k ∈ Set.Icc i j, RCLike.im (X k k) = 0) :
    exp X i j =
      ((dslope Real.exp (RCLike.re (X i i)) (RCLike.re (X j j)) : ℝ) : 𝕜) * X i j +
        triangularExpRemainder X i j hij := by
  let e := Fin.intervalOrderEmbOfLt i j hij
  have hblock : (X.submatrix e e).IsUpperTriangular :=
    hX.submatrix_of_strictMono e.strictMono
  have hrange : Set.range e = Set.Icc i j := Fin.range_intervalOrderEmbOfLt i j hij
  have hc := triangular_corner_exp hblock (fun k ↦ hreal (e k) (hrange ▸ Set.mem_range_self k))
  have he : Set.OrdConnected (Set.range e) := hrange.symm ▸ Set.ordConnected_Icc
  have hexp : (exp X).submatrix e e = exp (X.submatrix e e) := by
    simpa only [RelEmbedding.coe_toEmbedding] using hX.exp_submatrix e.toEmbedding he
  have hentry := congrArg (fun M ↦ M 0 (Fin.last ((j.val - i.val - 1) + 1))) hexp
  simpa only [Matrix.submatrix_apply, e, Fin.intervalOrderEmbOfLt_apply_zero,
    Fin.intervalOrderEmbOfLt_apply_last, triangularExpRemainder] using hentry.trans hc

/-- For adjacent indices the exponential remainder is zero. -/
theorem triangularExpRemainder_eq_zero_of_gap_one {m : ℕ} (X : Matrix (Fin m) (Fin m) 𝕜)
    (i j : Fin m) (hij : i < j) (hgap : j.val = i.val + 1) :
    triangularExpRemainder X i j hij = 0 := by
  unfold triangularExpRemainder expCornerRemainder
  apply Finset.sum_eq_zero
  intro k _
  have hk := k.isLt
  omega

end EntryRecurrence

end Matrix

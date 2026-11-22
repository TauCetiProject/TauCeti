/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Map
import Mathlib.Analysis.CStarAlgebra.Hom
import TauCeti.Analysis.CStarAlgebra.Module.AdjointPair

/-!
# Operator-norm laws and continuity for rectangular `CStarMatrix`

Within the `CStarMatrix` module split, choose `Norm` to connect rectangular operator-norm
estimates with entrywise continuity, `Map` for change of coefficients and index types, and
`Block` for block-matrix direct sums and amplification used in stabilization.

This file establishes operator-norm identities for rectangular C⋆-matrices via Hilbert C⋆-module
adjoint pairs (`‖M * N‖ ≤ ‖M‖ * ‖N‖`, `‖Mᴴ‖ = ‖M‖`, `‖M * Mᴴ‖ = ‖Mᴴ * M‖ = ‖M‖ ^ 2`,
`norm_reindexₐ`, `norm_reindexₗ`, `norm_single`) and entrywise continuity (`continuous_ofMatrix`,
`continuous_ofMatrix_symm`, `continuous_iff`).

## Main declarations

* `CStarMatrix.toCLM_mul`, `CStarMatrix.norm_mul_le`,
  `CStarMatrix.isAdjointPair_toCLM_conjTranspose`, `CStarMatrix.norm_conjTranspose`,
  `CStarMatrix.norm_self_mul_conjTranspose`, `CStarMatrix.norm_conjTranspose_mul_self`,
  `CStarMatrix.norm_reindexₐ`, `CStarMatrix.norm_reindexₗ`, `CStarMatrix.norm_single`,
  `CStarMatrix.continuous_iff`.

## References

* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Ch. 1.
* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., §4.6 and §5.1.
-/

public section

open Matrix
open scoped InnerProductSpace WithCStarModule

namespace CStarMatrix

section Norms
variable {l m n o R A : Type*} [NonUnitalCStarAlgebra A]
/-- `toCLM` reverses rectangular matrix multiplication into operator composition. -/
theorem toCLM_mul [Fintype l] [Fintype m] (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    toCLM (M * N) = (toCLM N).comp (toCLM M) := by
  ext v j; simp only [ContinuousLinearMap.comp_apply, toCLM_apply_eq_sum,
    WithCStarModule.equiv_symm_pi_apply, mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm
variable [PartialOrder A] [StarOrderedRing A]
/-- Rectangular submultiplicativity of the `CStarMatrix` operator norm. -/
theorem norm_mul_le [Fintype l] [Fintype m] [Fintype n]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) : ‖M * N‖ ≤ ‖M‖ * ‖N‖ := by
  rw [norm_def, norm_def, norm_def, toCLM_mul, mul_comm]; exact (toCLM N).opNorm_comp_le (toCLM M)
section
variable [Fintype m] [Fintype n]
/-- `toCLM M` and `toCLM M.conjTranspose` form a C⋆-module adjoint pair. -/
theorem isAdjointPair_toCLM_conjTranspose (M : CStarMatrix m n A) :
    LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := A)).flip
      (CStarModule.innerₛₗ (A := A)).flip (toCLM M) (toCLM M.conjTranspose) :=
  CStarModule.isAdjointPair_inner_iff.mpr fun _ _ =>
    CStarMatrix.inner_toCLM_conjTranspose_right.symm
/-- Conjugate transposition on rectangular `CStarMatrix` is isometric. -/
@[simp] theorem norm_conjTranspose (M : CStarMatrix m n A) : ‖M.conjTranspose‖ = ‖M‖ := by
  rw [norm_def, norm_def]; exact (isAdjointPair_toCLM_conjTranspose M).norm_eq_cstarModule
/-- Rectangular C⋆-identity `‖M * M.conjTranspose‖ = ‖M‖ ^ 2`. -/
@[simp] theorem norm_self_mul_conjTranspose (M : CStarMatrix m n A) :
    ‖M * M.conjTranspose‖ = ‖M‖ ^ 2 := by
  rw [norm_def, norm_def, toCLM_mul]
  exact (isAdjointPair_toCLM_conjTranspose M).norm_adjoint_comp_self_cstarModule
/-- Rectangular C⋆-identity `‖M.conjTranspose * M‖ = ‖M‖ ^ 2`. -/
@[simp] theorem norm_conjTranspose_mul_self (M : CStarMatrix m n A) :
    ‖M.conjTranspose * M‖ = ‖M‖ ^ 2 := by simpa using norm_self_mul_conjTranspose M.conjTranspose
/-- Simultaneous row and column relabeling by an equivalence preserves the square matrix operator
norm. -/
@[simp] theorem norm_reindexₐ [Semiring R] [Module R A] (e : m ≃ n) (M : CStarMatrix m m A) :
    ‖reindexₐ R A e M‖ = ‖M‖ :=
  (by ext; simp : reindexₐ R A e M = reindexₐ ℂ A e M) ▸ StarAlgEquiv.norm_map (reindexₐ ℂ A e) M
/-- `reindexₗ` along arbitrary row and column equivalences is isometric. -/
@[simp] theorem norm_reindexₗ [Fintype l] [Fintype o] [Semiring R] [Module R A] (eₘ : m ≃ l)
    (eₙ : n ≃ o) (M : CStarMatrix m n A) : ‖reindexₗ R A eₘ eₙ M‖ = ‖M‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp <| by
    rw [← norm_conjTranspose_mul_self, conjTranspose_reindexₗ, reindexₗ_mul,
      reindexₗ_self_eq_reindexₐ, norm_reindexₐ, norm_conjTranspose_mul_self]
/-- A matrix with a single entry `a` at `(i, j)` has operator norm `‖a‖`. -/
@[simp] theorem norm_single [DecidableEq m] [DecidableEq n] (i : m) (j : n) (a : A) :
    ‖ofMatrix (Matrix.single i j a)‖ = ‖a‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp <| by
    have hmul : (ofMatrix (Matrix.single i j a)).conjTranspose * ofMatrix (Matrix.single i j a) =
        singleNonUnitalStarAlgHom ℂ j (star a * a) :=
      ofMatrix.symm.injective <| by
        simp only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose, Equiv.symm_apply_apply,
          Matrix.conjTranspose_single, Matrix.single_mul_single_same,
          singleNonUnitalStarAlgHom_apply]
    rw [← norm_conjTranspose_mul_self, hmul, NonUnitalStarAlgHom.norm_map
      (singleNonUnitalStarAlgHom ℂ (A := A) j) (singleNonUnitalStarAlgHom_injective j) _,
      CStarRing.norm_star_mul_self, sq]
end
end Norms

section Continuity
variable {m n X A : Type*} [TopologicalSpace X] [NonUnitalCStarAlgebra A]
/-- `CStarMatrix.ofMatrix` is continuous. -/
@[fun_prop] theorem continuous_ofMatrix :
    Continuous (ofMatrix : Matrix m n A → CStarMatrix m n A) := by
  rw [ofMatrix_eq_ofMatrixL]; exact ofMatrixL.continuous
/-- `CStarMatrix.ofMatrix.symm` agrees with
`(ofMatrixL : Matrix m n A ≃L[ℂ] CStarMatrix m n A).symm`. -/
theorem ofMatrix_symm_eq_ofMatrixL_symm :
    (ofMatrix.symm : CStarMatrix m n A → Matrix m n A) =
      (ofMatrixL : Matrix m n A ≃L[ℂ] CStarMatrix m n A).symm := by
  funext M
  refine ofMatrix.injective ?_
  calc
    ofMatrix (ofMatrix.symm M) = M := ofMatrix.apply_symm_apply M
    _ = ofMatrixL (ofMatrixL.symm M) := (ofMatrixL.apply_symm_apply M).symm
    _ = ofMatrix (ofMatrixL.symm M) := congrFun ofMatrix_eq_ofMatrixL.symm (ofMatrixL.symm M)
/-- `CStarMatrix.ofMatrix.symm` is continuous. -/
@[fun_prop] theorem continuous_ofMatrix_symm :
    Continuous (ofMatrix.symm : CStarMatrix m n A → Matrix m n A) := by
  rw [ofMatrix_symm_eq_ofMatrixL_symm]; exact ofMatrixL.symm.continuous
/-- A map into `CStarMatrix m n A` is continuous iff every entry function is continuous. -/
theorem continuous_iff {f : X → CStarMatrix m n A} :
    Continuous f ↔ ∀ i j, Continuous fun x => f x i j :=
  ⟨fun hf i j => by
     simpa [ofMatrix_symm_apply] using (continuous_ofMatrix_symm.comp hf).matrix_elem i j,
   fun hf => (funext fun x => (ofMatrix.apply_symm_apply (f x)).symm) ▸ continuous_ofMatrix.comp
     (continuous_matrix fun i j => by simpa [ofMatrix_symm_apply] using hf i j)⟩
end Continuity

end CStarMatrix

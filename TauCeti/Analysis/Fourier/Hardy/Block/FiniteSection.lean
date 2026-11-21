/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI gpt-6.1-sol
-/
module

public import TauCeti.Analysis.Fourier.Hardy.Block.Basic
public import TauCeti.Analysis.InnerProductSpace.Compression
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.FiniteSection.Basic

/-!
# Finite block Hardy sections

Compression to the first `n + 1` block positions, with matrix coordinates indexed by
`Fin (n + 1) × Fin r`. For positive block size, flattening these coordinates in block order
identifies this matrix with the ordinary Hilbert-basis finite section.
-/

public noncomputable section

open scoped InnerProductSpace

namespace TauCeti

/-- Include the first `n + 1` block Hardy positions. -/
def blockFiniteInclusion (r n : ℕ) :
    EuclideanSpace ℂ (Fin (n + 1) × Fin r) →L[ℂ] BlockHardySpace r :=
  ((EuclideanSpace.basisFun (Fin (n + 1) × Fin r) ℂ).toBasis.constr ℂ
    (fun i => blockHardyBasis r (i.1, i.2))).toContinuousLinearMap

/-- A coordinate unit vector includes as the corresponding block Hardy basis vector. -/
@[simp] theorem blockFiniteInclusion_single (r n : ℕ) (i : Fin (n + 1) × Fin r) :
    blockFiniteInclusion r n (EuclideanSpace.single i 1) =
      blockHardyBasis r (i.1, i.2) := by
  rw [← EuclideanSpace.basisFun_apply]
  exact Module.Basis.constr_basis _ ℂ _ i

/-- Matrix of compression to the first `n + 1` block positions. -/
def blockFiniteSectionMatrix {r : ℕ}
    (T : BlockHardySpace r →L[ℂ] BlockHardySpace r) (n : ℕ) :
    Matrix (Fin (n + 1) × Fin r) (Fin (n + 1) × Fin r) ℂ :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm (T.compression (blockFiniteInclusion r n))

/-- Entries of a finite block section are the operator's block Hardy coefficients. -/
@[simp] theorem blockFiniteSectionMatrix_apply {r : ℕ}
    (T : BlockHardySpace r →L[ℂ] BlockHardySpace r) (n : ℕ)
    (i j : Fin (n + 1) × Fin r) :
    blockFiniteSectionMatrix T n i j =
      ⟪blockHardyBasis r (i.1, i.2), T (blockHardyBasis r (j.1, j.2))⟫_ℂ := by
  have h := T.inner_compression_apply (blockFiniteInclusion r n)
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  rw [blockFiniteInclusion_single, blockFiniteInclusion_single] at h
  change LinearMap.toMatrixOrthonormal
    (EuclideanSpace.basisFun (Fin (n + 1) × Fin r) ℂ)
    (T.compression (blockFiniteInclusion r n)).toLinearMap i j = _
  rw [LinearMap.toMatrixOrthonormal_apply_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_apply]
  exact h

/-- Enumerate the block Hardy basis by increasing position, then coordinate within the block. -/
def blockHardyBasisNat (r : ℕ) [NeZero r] : HilbertBasis ℕ ℂ (BlockHardySpace r) :=
  (blockHardyBasis r).reindex (Nat.divModEquiv r).symm

/-- Block order sends position `k` and coordinate `i` to `k * r + i`. -/
@[simp] theorem blockHardyBasisNat_apply (r : ℕ) [NeZero r] (k : ℕ) (i : Fin r) :
    blockHardyBasisNat r (k * r + i) = blockHardyBasis r (k, i) := by
  rw [blockHardyBasisNat, HilbertBasis.reindex_apply]
  exact congrArg (blockHardyBasis r) ((Nat.divModEquiv r).apply_symm_apply (k, i))

/-- Reindex the first `n + 1` full blocks as the first `(n + 1) * r` scalar coordinates. -/
def blockFiniteSectionIndexEquiv (r n : ℕ) [NeZero r] :
    (Fin (n + 1) × Fin r) ≃ Fin ((n + 1) * r - 1 + 1) :=
  finProdFinEquiv.trans (finCongr (Nat.sub_add_cancel (by
    have := NeZero.pos r
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))).symm)

/-- Flattening block coordinates gives the matrix of the native Hilbert-basis finite section. -/
theorem reindex_blockFiniteSectionMatrix {r : ℕ} [NeZero r]
    (T : BlockHardySpace r →L[ℂ] BlockHardySpace r) (n : ℕ) :
    Matrix.reindex (blockFiniteSectionIndexEquiv r n) (blockFiniteSectionIndexEquiv r n)
      (blockFiniteSectionMatrix T n) =
        (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm
          (T.finiteSection (blockHardyBasisNat r) ((n + 1) * r - 1)) := by
  apply Matrix.ext
  intro i j
  obtain ⟨i, rfl⟩ := (blockFiniteSectionIndexEquiv r n).surjective i
  obtain ⟨j, rfl⟩ := (blockFiniteSectionIndexEquiv r n).surjective j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    blockFiniteSectionMatrix_apply]
  have h := T.finiteSection_single_apply (blockHardyBasisNat r) ((n + 1) * r - 1)
    (blockFiniteSectionIndexEquiv r n i) (blockFiniteSectionIndexEquiv r n j)
  change _ = LinearMap.toMatrixOrthonormal
    (EuclideanSpace.basisFun (Fin ((n + 1) * r - 1 + 1)) ℂ)
    (T.finiteSection (blockHardyBasisNat r) ((n + 1) * r - 1)).toLinearMap _ _
  rw [LinearMap.toMatrixOrthonormal_apply_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  have hb (p : Fin (n + 1) × Fin r) :
      blockHardyBasisNat r (blockFiniteSectionIndexEquiv r n p) =
        blockHardyBasis r (p.1, p.2) := by
    change blockHardyBasisNat r (p.2.val + r * p.1.val) = _
    rw [Nat.add_comm, Nat.mul_comm r p.1.val, blockHardyBasisNat_apply]
  simpa only [hb, map_one, one_mul, EuclideanSpace.single, ContinuousLinearMap.coe_coe]
    using h.symm

end TauCeti

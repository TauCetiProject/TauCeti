/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI gpt-6.1-sol
-/
module

public import TauCeti.Analysis.Fourier.Hardy.Block.Basic
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.FiniteSection.Basic

/-!
# Finite block Hardy sections

Compression to the first `n + 1` block positions, with matrix coordinates indexed by
`Fin (n + 1) × Fin r`. For positive block size, flattening these coordinates in block order
identifies this matrix with the ordinary Hilbert-basis finite section.

## Provenance

Generalizes the example compression matrix from the Kitware DKPS donor
`ForTauCeti/Analysis/Fourier/Hardy/OppositeShifts.lean` at
[d1c0bf02e](https://github.com/AIQ-Kitware/aiq-dkps-formalization/blob/d1c0bf02e/ForTauCeti/Analysis/Fourier/Hardy/OppositeShifts.lean).
The generalization uses native orthonormal synthesis, operator compression and
Hilbert-basis finite sections. Jon Crall / OpenAI gpt-6.1-sol, Kitware 2026, Apache-2.0.
-/

public noncomputable section

open scoped InnerProductSpace

namespace TauCeti

/-- Include the first `n + 1` block Hardy positions. -/
def blockFiniteInclusion (r n : ℕ) :
    EuclideanSpace ℂ (Fin (n + 1) × Fin r) →ₗᵢ[ℂ] BlockHardySpace r :=
  ((blockHardyBasis r).orthonormal.comp
    (Prod.map (Fin.val : Fin (n + 1) → ℕ) id)
    (Fin.val_injective.prodMap Function.injective_id)).synthesisMapIsometry

/-- The inclusion is the finite expansion in the selected block basis vectors. -/
theorem blockFiniteInclusion_apply (r n : ℕ)
    (x : EuclideanSpace ℂ (Fin (n + 1) × Fin r)) :
    blockFiniteInclusion r n x = ∑ i, x i • blockHardyBasis r (i.1, i.2) :=
  Orthonormal.synthesisMapIsometry_apply _ x

/-- A coordinate unit vector includes as the corresponding block Hardy basis vector. -/
@[simp] theorem blockFiniteInclusion_single (r n : ℕ) (i : Fin (n + 1) × Fin r) :
    blockFiniteInclusion r n (EuclideanSpace.single i 1) =
      blockHardyBasis r (i.1, i.2) := by
  have h := (((blockHardyBasis r).orthonormal.comp
    (Prod.map (Fin.val : Fin (n + 1) → ℕ) id)
    (Fin.val_injective.prodMap Function.injective_id)).synthesisMapIsometry_single i (1 : ℂ))
  -- The native lemma fixes classical equality; finite coordinates use their concrete instance.
  rw [show (fun a b : Fin (n + 1) × Fin r => Classical.propDecidable (a = b)) =
    (inferInstance : DecidableEq (Fin (n + 1) × Fin r)) from Subsingleton.elim _ _] at h
  simpa only [blockFiniteInclusion, one_smul, Function.comp_apply, Prod.map_apply, id_eq] using! h

/-- The adjoint inclusion reads the selected block Hardy coefficients. -/
@[simp] theorem adjoint_blockFiniteInclusion_apply (r n : ℕ) (f : BlockHardySpace r)
    (i : Fin (n + 1) × Fin r) :
    ((blockFiniteInclusion r n).toContinuousLinearMap.adjoint f) i =
      (blockHardyBasis r).repr f (i.1, i.2) := by
  rw [blockFiniteInclusion, Orthonormal.adjoint_synthesisMapIsometry_apply]
  exact ((blockHardyBasis r).repr_apply_apply f (i.1, i.2)).symm

/-- Matrix of compression to the first `n + 1` block positions. -/
def blockFiniteSectionMatrix {r : ℕ}
    (T : BlockHardySpace r →L[ℂ] BlockHardySpace r) (n : ℕ) :
    Matrix (Fin (n + 1) × Fin r) (Fin (n + 1) × Fin r) ℂ :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm
    (T.compression (blockFiniteInclusion r n).toContinuousLinearMap)

/-- Converting the finite block matrix to an operator gives its defining compression. -/
@[simp] theorem toEuclideanCLM_blockFiniteSectionMatrix {r : ℕ}
    (T : BlockHardySpace r →L[ℂ] BlockHardySpace r) (n : ℕ) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (blockFiniteSectionMatrix T n) =
      T.compression (blockFiniteInclusion r n).toContinuousLinearMap :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ)).apply_symm_apply _

/-- Entries of a finite block section are the operator's block Hardy coefficients. -/
@[simp] theorem blockFiniteSectionMatrix_apply {r : ℕ}
    (T : BlockHardySpace r →L[ℂ] BlockHardySpace r) (n : ℕ)
    (i j : Fin (n + 1) × Fin r) :
    blockFiniteSectionMatrix T n i j =
      ⟪blockHardyBasis r (i.1, i.2), T (blockHardyBasis r (j.1, j.2))⟫_ℂ := by
  rw [blockFiniteSectionMatrix, Matrix.toEuclideanCLM_symm_apply_single]
  simpa only [EuclideanSpace.inner_single_left, map_one, one_mul,
    LinearIsometry.coe_toContinuousLinearMap,
    blockFiniteInclusion_single] using T.inner_compression_apply
      (blockFiniteInclusion r n).toContinuousLinearMap
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

/-- Reindex the first `n + 1` full blocks as the first `(n + 1) * r` scalar coordinates. -/
def blockFiniteSectionIndexEquiv (r n : ℕ) [NeZero r] :
    (Fin (n + 1) × Fin r) ≃ Fin ((n + 1) * r - 1 + 1) :=
  finProdFinEquiv.trans (finCongr (Nat.sub_add_cancel (by
    have := NeZero.pos r
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))).symm)

/-- Flattening lists coordinates in increasing block position, then within the block. -/
@[simp] theorem blockFiniteSectionIndexEquiv_val (r n : ℕ) [NeZero r]
    (p : Fin (n + 1) × Fin r) :
    (blockFiniteSectionIndexEquiv r n p).val = p.1.val * r + p.2.val := by
  rw [blockFiniteSectionIndexEquiv, Equiv.trans_apply, finCongr_apply_coe,
    finProdFinEquiv_apply_val]
  ac_rfl

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
  rw [Matrix.toEuclideanCLM_symm_apply_single]
  have hb (p : Fin (n + 1) × Fin r) :
      blockHardyBasisNat r (blockFiniteSectionIndexEquiv r n p) =
        blockHardyBasis r (p.1, p.2) := by
    rw [blockFiniteSectionIndexEquiv_val, blockHardyBasisNat_apply]
  simpa only [hb] using h.symm

/-- The determinant of a native full-block finite section is the block compression determinant. -/
theorem det_finiteSection_eq_blockFiniteSectionMatrix {r : ℕ} [NeZero r]
    (T : BlockHardySpace r →L[ℂ] BlockHardySpace r) (n : ℕ) :
    (T.finiteSection (blockHardyBasisNat r) ((n + 1) * r - 1)).toLinearMap.det =
      (blockFiniteSectionMatrix T n).det := by
  rw [← Matrix.det_reindex_self (blockFiniteSectionIndexEquiv r n),
    reindex_blockFiniteSectionMatrix, ← Matrix.det_toEuclideanCLM,
    StarAlgEquiv.apply_symm_apply]

end TauCeti

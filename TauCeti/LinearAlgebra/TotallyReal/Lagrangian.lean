/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Polar.Deformation
public import TauCeti.LinearAlgebra.TotallyReal.Euclidean

/-!
# Deforming closed frames of totally real subspaces to unitary frames

A continuous path `M` of invertible complex matrices whose real spans `M t ℝⁿ`
(`Matrix.realImage`) close up, `M 0 ℝⁿ = M 1 ℝⁿ`, is deformed through such closed paths to a path
of unitary matrices (`TauCeti.exists_realImage_homotopy_unitaryGroup`). The subspaces `U ℝⁿ` with
`U` unitary are Lagrangian for the standard symplectic form `Im ⟪·, ·⟫` of `ℂⁿ`
(`TauCeti.im_inner_eq_zero_of_mem_realImage`), so this deforms loops of maximal totally real
subspaces of `ℂⁿ` with a continuous frame to loops of Lagrangian subspaces.

The homotopy has two stages. The closedness of the path says `M 1 = M 0 G` for a real invertible
matrix `G` (`Matrix.exists_eq_mul_map_ofReal`).

* **Orthonormalization.** Replacing `M` by `B = M Re (Mᴴ M) ^ (-1/2)` does not change the real
  spans `M t ℝⁿ`, because the correction is real and invertible, and it makes the columns of
  `B t` orthonormal for the real inner product `Re ⟪·, ·⟫`. Two such frames with the same real
  span differ by a real orthogonal matrix (`Matrix.exists_mem_orthogonalGroup_eq_mul_map_ofReal`),
  so `B 1 = B 0 O` with `O` orthogonal, hence unitary.
* **Polar contraction.** Contracting the positive factor of the polar decomposition
  `B t = P t V t`, through `P t ^ (1 - s) V t`
  (`Matrix.GeneralLinearGroup.polarDeformation`), is equivariant under right multiplication by
  the unitary monodromy `O` (`Matrix.GeneralLinearGroup.polarDeformation_mul_toUnits`). So every
  intermediate path still closes up, and at `s = 1` it reaches the unitary path `V`.

Without the orthonormalization the monodromy `G` need not be orthogonal, and the polar
contraction of `M` need not close up.

## Main declarations

* `TauCeti.exists_realImage_homotopy_unitaryGroup`: a closed frame deforms through closed frames
  to a path of unitary matrices.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C.3 (loops of totally real subspaces and the
  comparison with Lagrangian loops).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Section 2.3 (the Lagrangian Grassmannian `U(n) / O(n)`).
-/

public section

noncomputable section

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator unitInterval

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Orthonormalizing a frame by a real change of basis -/

/-- The real Gram matrix `Re (Mᴴ M)` of the columns of `M`, for the real inner product
`Re ⟪v, w⟫` of `ℂⁿ`. -/
private abbrev realGram (M : Matrix n n ℂ) : Matrix n n ℝ := (Mᴴ * M).map Complex.re

/-- The real Gram matrix of an invertible complex matrix is positive definite. -/
private theorem posDef_realGram (M : GL n ℂ) : (realGram (M : Matrix n n ℂ)).PosDef :=
  PosDef.map_re_conjTranspose_mul_self _ (mulVec_injective_of_isUnit M.isUnit)

/-- The real matrix `Re (Mᴴ M) ^ (-1/2)`. Multiplying `M` by it on the right makes the columns
orthonormal for `Re ⟪·, ·⟫`. -/
private abbrev gramNormalizer (M : GL n ℂ) : Matrix n n ℝ :=
  realGram (M : Matrix n n ℂ) ^ (-(1 / 2) : ℝ)

private theorem posDef_gramNormalizer (M : GL n ℂ) : (gramNormalizer M).PosDef :=
  isStrictlyPositive_iff_posDef.1 <|
    IsStrictlyPositive.rpow _ _ (isStrictlyPositive_iff_posDef.2 (posDef_realGram M))

private theorem gramNormalizer_mul_realGram_mul (M : GL n ℂ) :
    (gramNormalizer M)ᵀ * realGram (M : Matrix n n ℂ) * gramNormalizer M = 1 := by
  have hH := isStrictlyPositive_iff_posDef.2 (posDef_realGram M)
  have hT : (gramNormalizer M)ᵀ = gramNormalizer M := by
    exact (by simpa [conjTranspose_eq_transpose_of_trivial] using (posDef_gramNormalizer M).1 :
      (gramNormalizer M).IsSymm).eq
  rw [hT, gramNormalizer]
  nth_rw 2 [← CFC.rpow_one (realGram (M : Matrix n n ℂ)) hH.nonneg]
  rw [← CFC.rpow_add hH.isUnit, ← CFC.rpow_add hH.isUnit]
  norm_num [CFC.rpow_zero _ hH.nonneg]

private theorem isUnit_gramNormalizer_map (M : GL n ℂ) :
    IsUnit ((gramNormalizer M).map ((↑) : ℝ → ℂ)) :=
  (posDef_gramNormalizer M).isUnit.map Complex.ofRealHom.mapMatrix

/-- The frame `M Re (Mᴴ M) ^ (-1/2)`. It spans the same real subspace as `M`, and its columns are
orthonormal for `Re ⟪·, ·⟫`. -/
private def orthoFrame (M : GL n ℂ) : GL n ℂ :=
  M * (isUnit_gramNormalizer_map M).unit

private theorem coe_orthoFrame (M : GL n ℂ) :
    (orthoFrame M : Matrix n n ℂ) = M * (gramNormalizer M).map ((↑) : ℝ → ℂ) :=
  rfl

private theorem realImage_orthoFrame (M : GL n ℂ) :
    (orthoFrame M : Matrix n n ℂ).realImage = (M : Matrix n n ℂ).realImage := by
  rw [coe_orthoFrame]
  exact realImage_mul_map_ofReal _ (posDef_gramNormalizer M).isUnit

private theorem realGram_orthoFrame (M : GL n ℂ) :
    realGram (orthoFrame M : Matrix n n ℂ) = 1 := by
  rw [coe_orthoFrame, realGram, map_re_conjTranspose_mul_self_mul_map_ofReal,
    gramNormalizer_mul_realGram_mul]

private theorem continuous_orthoFrame {X : Type*} [TopologicalSpace X] {M : X → GL n ℂ}
    (hM : Continuous M) : Continuous fun x ↦ orthoFrame (M x) := by
  refine Units.isOpenEmbedding_val.continuous_iff.2 ?_
  have hval : Continuous fun x ↦ (M x : Matrix n n ℂ) := Units.continuous_val.comp hM
  have hG : Continuous fun x ↦ realGram (M x : Matrix n n ℂ) :=
    (hval.matrix_conjTranspose.mul hval).matrix_map Complex.continuous_re
  have hQ : Continuous fun x ↦ gramNormalizer (M x) :=
    (Matrix.contDiffOn_rpow (𝕜 := ℝ) (n := n) (-(1 / 2)) (k := 0)).continuousOn.comp_continuous
      hG fun x ↦ posDef_realGram (M x)
  exact hval.mul (hQ.matrix_map Complex.continuous_ofReal)

/-! ### The deformation to unitary frames -/

/-- **The Lagrangian deformation of a closed frame.** A continuous path `M` of invertible complex
matrices with `M 0 ℝⁿ = M 1 ℝⁿ` is deformed, through continuous paths `F (s, ·)` with
`F (s, 0) ℝⁿ = F (s, 1) ℝⁿ`, from a path with the same real spans as `M` to a path of unitary
matrices. First orthonormalize the real frames, so that the endpoint monodromy is orthogonal;
then contract the positive factor of the polar decomposition, which is equivariant under that
monodromy. -/
theorem exists_realImage_homotopy_unitaryGroup {M : I → GL n ℂ} (hM : Continuous M)
    (h01 : (M 0 : Matrix n n ℂ).realImage = (M 1 : Matrix n n ℂ).realImage) :
    ∃ F : I × I → GL n ℂ, Continuous F ∧
      (∀ t, (F (0, t) : Matrix n n ℂ).realImage = (M t : Matrix n n ℂ).realImage) ∧
      (∀ s, (F (s, 0) : Matrix n n ℂ).realImage = (F (s, 1) : Matrix n n ℂ).realImage) ∧
      ∀ t, (F (1, t) : Matrix n n ℂ) ∈ unitaryGroup n ℂ := by
  obtain ⟨O, hOO, hO⟩ := exists_mem_orthogonalGroup_eq_mul_map_ofReal (M := orthoFrame (M 0))
    (M' := orthoFrame (M 1)) (by rw [realImage_orthoFrame, realImage_orthoFrame, h01])
    (realGram_orthoFrame _) (realGram_orthoFrame _)
  have hOu := map_ofReal_mem_unitaryGroup hOO
  have hO1 : orthoFrame (M 1) = orthoFrame (M 0) * Unitary.toUnits ⟨_, hOu⟩ := Units.ext hO
  have hOunit : IsUnit O := (Matrix.isUnit_iff_isUnit_det O).2
    (Matrix.isUnit_det_of_left_inverse ((mem_orthogonalGroup_iff' n ℝ).1 hOO))
  refine ⟨fun p ↦ GeneralLinearGroup.polarDeformation (orthoFrame (M p.2)) p.1, ?_,
    fun t ↦ ?_, fun s ↦ ?_, fun t ↦ ?_⟩
  · have h := (GeneralLinearGroup.contMDiff_polarDeformation (n := n) (𝕜 := ℂ) (k := 0)).continuous
    exact h.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      ((continuous_orthoFrame hM).comp continuous_snd))
  · simp [realImage_orthoFrame]
  · simp only
    rw [hO1, GeneralLinearGroup.polarDeformation_mul_toUnits, Units.val_mul,
      Unitary.val_toUnits_apply]
    exact (realImage_mul_map_ofReal _ hOunit).symm
  · simp

end TauCeti

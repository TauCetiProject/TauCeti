/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Similitude.Basic
import TauCeti.Data.Matrix.Block

/-!
# The Siegel parabolic subgroup of the symplectic similitude group

Write a similitude `γ ∈ GSp(l ⊕ l, R)` in `l × l` blocks as `γ = (A B; C D)`, with multiplier
`c(γ)`. Reading the defining identity `γ J γᵀ = c(γ) • J` block by block gives
`A Dᵀ - B Cᵀ = c(γ) • 1` (`TauCeti.GSp.toBlocks₁₁_mul_transpose_toBlocks₂₂_sub`).

The block upper-triangular similitudes, those with `C = 0`, form the **Siegel parabolic subgroup**
(`TauCeti.GSp.siegelParabolic`). On it `A Dᵀ = c(γ) • 1`, and the upper-left block `A` is a group
morphism to `GL l R` (`TauCeti.GSp.upperLeftHom`): the lower-left block vanishes, so
`(γδ)₁₁ = A_γ A_δ`.

## Main definitions

* `TauCeti.GSp.siegelParabolic`: the similitudes with vanishing lower-left block.
* `TauCeti.GSp.upperLeftHom`: the upper-left block, a morphism from the Siegel parabolic to `GL`.

## Main results

* `TauCeti.GSp.toBlocks₁₁_mul_transpose_toBlocks₂₂_sub`: `A Dᵀ - B Cᵀ = c(γ) • 1`.
* `TauCeti.GSp.toBlocks₁₁_mul_transpose_toBlocks₂₂_of_toBlocks₂₁_eq_zero`: `A Dᵀ = c(γ) • 1` when
  `C = 0`.

## References

* P. Scholze, *On torsion in the cohomology of locally symmetric varieties*, Ann. of Math. 182
  (2015), §3.1: the block upper-triangular condition defining `Γ₀(pᵐ)`.
-/

public section

open Matrix

namespace TauCeti

namespace GSp

universe u

variable {l : Type*} [DecidableEq l] [Fintype l] {R : Type u} [CommRing R] [Nonempty l]

/-! ### The block form of the similitude condition -/

/-- **The block form of the similitude condition**: for a similitude `γ = (A B; C D)` with
multiplier `c`, `A Dᵀ - B Cᵀ = c • 1`. -/
theorem toBlocks₁₁_mul_transpose_toBlocks₂₂_sub (M : GSp l R) :
    ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₁₁ *
        ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₂₂ᵀ -
      ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₁₂ *
        ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₂₁ᵀ =
      (multiplier l R M : R) • 1 := by
  have h := congrArg Matrix.toBlocks₁₂ (mul_J_mul_transpose M)
  rw [← fromBlocks_toBlocks ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R)] at h
  simp only [Matrix.J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_smul,
    toBlocks_fromBlocks₁₂, Matrix.mul_zero, Matrix.mul_neg, Matrix.mul_one, zero_add, add_zero,
    smul_neg, Matrix.neg_mul] at h
  rw [← neg_inj, ← h]
  abel

/-- For a block upper-triangular similitude `γ = (A B; 0 D)` with multiplier `c`,
`A Dᵀ = c • 1`. -/
theorem toBlocks₁₁_mul_transpose_toBlocks₂₂_of_toBlocks₂₁_eq_zero {M : GSp l R}
    (hM : ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₂₁ = 0) :
    ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₁₁ *
        ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₂₂ᵀ =
      (multiplier l R M : R) • 1 := by
  simpa [hM] using toBlocks₁₁_mul_transpose_toBlocks₂₂_sub M

/-! ### The Siegel parabolic and its upper-left block -/

variable (l R) in
/-- The **Siegel parabolic subgroup**: the similitudes `(A B; 0 D)` with vanishing lower-left
block. -/
def siegelParabolic : Subgroup (GSp l R) where
  carrier := {M | ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₂₁ = 0}
  mul_mem' {M N} hM hN := by
    simp only [Set.mem_ofPred_eq, Subgroup.coe_mul, Units.val_mul, toBlocks₂₁_mul] at hM hN ⊢
    rw [hM, hN, Matrix.zero_mul, Matrix.mul_zero, add_zero]
  one_mem' := by
    simp only [Set.mem_ofPred_eq, OneMemClass.coe_one, Units.val_one]
    exact toBlocks₂₁_one
  inv_mem' {M} hM := by
    simp only [Set.mem_ofPred_eq] at hM ⊢
    rw [coe_inv_eq_neg_smul_J_mul_transpose_mul_J,
      ← fromBlocks_toBlocks ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R), hM]
    simp [Matrix.J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_smul, fromBlocks_neg]

/-- Membership in the Siegel parabolic: the lower-left block vanishes. -/
@[simp]
theorem mem_siegelParabolic_iff {M : GSp l R} :
    M ∈ siegelParabolic l R ↔ ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₂₁ = 0 :=
  Iff.rfl

/-- The upper-left block of an element of the Siegel parabolic is invertible, with inverse the
upper-left block of its inverse. -/
private theorem toBlocks₁₁_mul_toBlocks₁₁_inv (M : siegelParabolic l R) :
    ((M : GSp l R) : GL (l ⊕ l) R).val.toBlocks₁₁ *
        ((M⁻¹ : siegelParabolic l R) : GSp l R).val.val.toBlocks₁₁ = 1 := by
  rw [← toBlocks₁₁_mul_of_toBlocks₂₁_eq_zero (M⁻¹).property]
  simp only [InvMemClass.coe_inv, Units.mul_inv]
  exact toBlocks₁₁_one

variable (l R) in
/-- The **upper-left block** `A` of an element `(A B; 0 D)` of the Siegel parabolic, as a group
morphism to `GL l R`. -/
def upperLeftHom : siegelParabolic l R →* GL l R where
  toFun M := ⟨((M : GSp l R) : GL (l ⊕ l) R).val.toBlocks₁₁,
    ((M⁻¹ : siegelParabolic l R) : GSp l R).val.val.toBlocks₁₁,
    toBlocks₁₁_mul_toBlocks₁₁_inv M, by
      simpa only [inv_inv] using toBlocks₁₁_mul_toBlocks₁₁_inv M⁻¹⟩
  map_one' := Units.ext <| by
    simp only [OneMemClass.coe_one, Units.val_one]
    exact toBlocks₁₁_one
  map_mul' M N := Units.ext <| by
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact toBlocks₁₁_mul_of_toBlocks₂₁_eq_zero N.property

/-- The upper-left block morphism takes an element to its upper-left block. -/
@[simp]
theorem coe_upperLeftHom (M : siegelParabolic l R) :
    (upperLeftHom l R M : Matrix l l R) = ((M : GSp l R) : GL (l ⊕ l) R).val.toBlocks₁₁ :=
  (rfl)

end GSp

end TauCeti

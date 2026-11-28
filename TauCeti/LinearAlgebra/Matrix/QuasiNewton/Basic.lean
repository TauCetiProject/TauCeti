/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
import TauCeti.LinearAlgebra.Matrix.OneSubVecMulVec
import TauCeti.LinearAlgebra.Matrix.Symmetric

/-!
# The BFGS and DFP updates and their secant equations

A quasi-Newton method keeps a matrix `B` that approximates a Hessian, or a matrix `H` that
approximates an inverse Hessian, and corrects it after a step `s` with gradient change `y`. The
corrected matrix `B₊` should satisfy the secant equation `B₊ s = y`, and the corrected inverse
`H₊` the inverse secant equation `H₊ y = s`. This file defines the updates of
Broyden-Fletcher-Goldfarb-Shanno (BFGS) and of Davidon-Fletcher-Powell (DFP), in direct and in
inverse form. With `ρ = (yᵀ s)⁻¹` they are

* `bfgsUpdate B s y = B - (sᵀ B s)⁻¹ (B s)(sᵀ B) + ρ y yᵀ`;
* `bfgsInvUpdate H s y = (1 - ρ s yᵀ) H (1 - ρ y sᵀ) + ρ s sᵀ`;
* `dfpUpdate B s y = (1 - ρ y sᵀ) B (1 - ρ s yᵀ) + ρ y yᵀ`;
* `dfpInvUpdate H s y = H - (yᵀ H y)⁻¹ (H y)(yᵀ H) + ρ s sᵀ`.

Reciprocals of zero are zero, as everywhere in Mathlib, so the updates are defined for all
arguments. For instance, both direct updates return `B` when `s = 0`. The updates are rational
expressions in the entries, so they are stated over an arbitrary field `𝕜`; quasi-Newton methods
use `𝕜 = ℝ`.

The inverse form of each method is the direct form of the other method with `s` and `y`
interchanged. This duality turns the secant equations of the direct updates into the inverse
secant equations, and the symmetry of the direct updates into that of the inverse updates.

## Main definitions

* `Matrix.bfgsUpdate`, `Matrix.bfgsInvUpdate`: the BFGS update of a Hessian approximation and of
  an inverse Hessian approximation.
* `Matrix.dfpUpdate`, `Matrix.dfpInvUpdate`: the DFP update of a Hessian approximation and of an
  inverse Hessian approximation.

## Main results

* `Matrix.bfgsUpdate_mulVec`, `Matrix.dfpUpdate_mulVec`: the secant equations `B₊ s = y`.
* `Matrix.bfgsInvUpdate_eq_dfpUpdate`, `Matrix.dfpInvUpdate_eq_bfgsUpdate`: the duality between
  the two methods.
* `Matrix.bfgsInvUpdate_mulVec`, `Matrix.dfpInvUpdate_mulVec`: the inverse secant equations
  `H₊ y = s`.
* `Matrix.IsSymm.bfgsUpdate`, `Matrix.IsSymm.dfpUpdate`, `Matrix.IsSymm.bfgsInvUpdate`,
  `Matrix.IsSymm.dfpInvUpdate`: the updates of a symmetric matrix are symmetric.
* `Matrix.bfgsUpdate_zero`, `Matrix.dfpUpdate_zero`: with the step `s = 0` both direct updates
  return `B`.

## References

* J. E. Dennis and J. J. Moré, *Quasi-Newton methods, motivation and theory*, SIAM Review 19
  (1977), 46-89: equations (7.18), (7.19) and (7.25), Theorem 7.8, and the duality (7.30).
-/

public section

namespace Matrix

variable {𝕜 ι : Type*} [Field 𝕜] [Fintype ι]

/-- The BFGS update `B - (sᵀ B s)⁻¹ (B s)(sᵀ B) + (yᵀ s)⁻¹ y yᵀ` of a Hessian approximation `B`
along a step `s` with gradient change `y`. -/
def bfgsUpdate (B : Matrix ι ι 𝕜) (s y : ι → 𝕜) : Matrix ι ι 𝕜 :=
  B - (s ⬝ᵥ (B *ᵥ s))⁻¹ • vecMulVec (B *ᵥ s) (s ᵥ* B) + (y ⬝ᵥ s)⁻¹ • vecMulVec y y

variable [DecidableEq ι] in
/-- The BFGS update `(1 - ρ s yᵀ) H (1 - ρ y sᵀ) + ρ s sᵀ`, with `ρ = (yᵀ s)⁻¹`, of an inverse
Hessian approximation `H` along a step `s` with gradient change `y`. -/
def bfgsInvUpdate (H : Matrix ι ι 𝕜) (s y : ι → 𝕜) : Matrix ι ι 𝕜 :=
  (1 - (y ⬝ᵥ s)⁻¹ • vecMulVec s y) * H * (1 - (y ⬝ᵥ s)⁻¹ • vecMulVec y s) +
    (y ⬝ᵥ s)⁻¹ • vecMulVec s s

variable [DecidableEq ι] in
/-- The DFP update `(1 - ρ y sᵀ) B (1 - ρ s yᵀ) + ρ y yᵀ`, with `ρ = (yᵀ s)⁻¹`, of a Hessian
approximation `B` along a step `s` with gradient change `y`. -/
def dfpUpdate (B : Matrix ι ι 𝕜) (s y : ι → 𝕜) : Matrix ι ι 𝕜 :=
  (1 - (y ⬝ᵥ s)⁻¹ • vecMulVec y s) * B * (1 - (y ⬝ᵥ s)⁻¹ • vecMulVec s y) +
    (y ⬝ᵥ s)⁻¹ • vecMulVec y y

/-- The DFP update `H - (yᵀ H y)⁻¹ (H y)(yᵀ H) + (sᵀ y)⁻¹ s sᵀ` of an inverse Hessian
approximation `H` along a step `s` with gradient change `y`. -/
def dfpInvUpdate (H : Matrix ι ι 𝕜) (s y : ι → 𝕜) : Matrix ι ι 𝕜 :=
  H - (y ⬝ᵥ (H *ᵥ y))⁻¹ • vecMulVec (H *ᵥ y) (y ᵥ* H) + (s ⬝ᵥ y)⁻¹ • vecMulVec s s

section Defs

variable (B H : Matrix ι ι 𝕜) (s y : ι → 𝕜)

/-- The defining formula of `bfgsUpdate`. -/
theorem bfgsUpdate_def : bfgsUpdate B s y =
    B - (s ⬝ᵥ (B *ᵥ s))⁻¹ • vecMulVec (B *ᵥ s) (s ᵥ* B) + (y ⬝ᵥ s)⁻¹ • vecMulVec y y := (rfl)

variable [DecidableEq ι] in
/-- The defining formula of `bfgsInvUpdate`. -/
theorem bfgsInvUpdate_def : bfgsInvUpdate H s y =
    (1 - (y ⬝ᵥ s)⁻¹ • vecMulVec s y) * H * (1 - (y ⬝ᵥ s)⁻¹ • vecMulVec y s) +
      (y ⬝ᵥ s)⁻¹ • vecMulVec s s := (rfl)

variable [DecidableEq ι] in
/-- The defining formula of `dfpUpdate`. -/
theorem dfpUpdate_def : dfpUpdate B s y =
    (1 - (y ⬝ᵥ s)⁻¹ • vecMulVec y s) * B * (1 - (y ⬝ᵥ s)⁻¹ • vecMulVec s y) +
      (y ⬝ᵥ s)⁻¹ • vecMulVec y y := (rfl)

/-- The defining formula of `dfpInvUpdate`. -/
theorem dfpInvUpdate_def : dfpInvUpdate H s y =
    H - (y ⬝ᵥ (H *ᵥ y))⁻¹ • vecMulVec (H *ᵥ y) (y ᵥ* H) + (s ⬝ᵥ y)⁻¹ • vecMulVec s s := (rfl)

end Defs

/-! ### Duality -/

variable [DecidableEq ι] in
/-- The inverse BFGS update is the DFP update with the step and the gradient change
interchanged. -/
theorem bfgsInvUpdate_eq_dfpUpdate (H : Matrix ι ι 𝕜) (s y : ι → 𝕜) :
    bfgsInvUpdate H s y = dfpUpdate H y s := by
  rw [bfgsInvUpdate_def, dfpUpdate_def, dotProduct_comm y s]

/-- The inverse DFP update is the BFGS update with the step and the gradient change
interchanged. -/
theorem dfpInvUpdate_eq_bfgsUpdate (H : Matrix ι ι 𝕜) (s y : ι → 𝕜) :
    dfpInvUpdate H s y = bfgsUpdate H y s := by
  rw [dfpInvUpdate_def, bfgsUpdate_def]

/-! ### The secant equations -/

/-- The secant equation for the BFGS update: if `sᵀ y ≠ 0` and `sᵀ B s ≠ 0`, then
`bfgsUpdate B s y` sends `s` to `y`. -/
theorem bfgsUpdate_mulVec (B : Matrix ι ι 𝕜) {s y : ι → 𝕜} (hsy : s ⬝ᵥ y ≠ 0)
    (hsBs : s ⬝ᵥ (B *ᵥ s) ≠ 0) : bfgsUpdate B s y *ᵥ s = y := by
  rw [bfgsUpdate_def, add_mulVec, sub_mulVec, smul_mulVec, smul_mulVec, vecMulVec_mulVec,
    vecMulVec_mulVec, op_smul_eq_smul, op_smul_eq_smul, ← dotProduct_mulVec, smul_smul,
    smul_smul, inv_mul_cancel₀ hsBs, inv_mul_cancel₀ (dotProduct_comm s y ▸ hsy), one_smul,
    one_smul, sub_self, zero_add]

variable [DecidableEq ι] in
/-- The secant equation for the DFP update: if `sᵀ y ≠ 0`, then `dfpUpdate B s y` sends `s`
to `y`, for every square matrix `B`. -/
theorem dfpUpdate_mulVec (B : Matrix ι ι 𝕜) {s y : ι → 𝕜} (hsy : s ⬝ᵥ y ≠ 0) :
    dfpUpdate B s y *ᵥ s = y := by
  have hys : (y ⬝ᵥ s)⁻¹ * (y ⬝ᵥ s) = 1 := inv_mul_cancel₀ (dotProduct_comm s y ▸ hsy)
  rw [dfpUpdate_def, add_mulVec, ← mulVec_mulVec, one_sub_smul_vecMulVec_mulVec,
    op_smul_eq_smul, smul_smul, hys, one_smul, sub_self, mulVec_zero, zero_add,
    smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul, hys, one_smul]

variable [DecidableEq ι] in
/-- The inverse secant equation for the inverse BFGS update: if `sᵀ y ≠ 0`, then
`bfgsInvUpdate H s y` sends `y` to `s`, for every square matrix `H`. -/
theorem bfgsInvUpdate_mulVec (H : Matrix ι ι 𝕜) {s y : ι → 𝕜} (hsy : s ⬝ᵥ y ≠ 0) :
    bfgsInvUpdate H s y *ᵥ y = s := by
  rw [bfgsInvUpdate_eq_dfpUpdate, dfpUpdate_mulVec H (dotProduct_comm s y ▸ hsy)]

/-- The inverse secant equation for the inverse DFP update: if `sᵀ y ≠ 0` and `yᵀ H y ≠ 0`,
then `dfpInvUpdate H s y` sends `y` to `s`. -/
theorem dfpInvUpdate_mulVec (H : Matrix ι ι 𝕜) {s y : ι → 𝕜} (hsy : s ⬝ᵥ y ≠ 0)
    (hyHy : y ⬝ᵥ (H *ᵥ y) ≠ 0) : dfpInvUpdate H s y *ᵥ y = s := by
  rw [dfpInvUpdate_eq_bfgsUpdate, bfgsUpdate_mulVec H (dotProduct_comm s y ▸ hsy) hyHy]

/-! ### The step zero -/

/-- With the step `s = 0` the BFGS update returns `B`, since both reciprocals vanish. -/
@[simp]
theorem bfgsUpdate_zero (B : Matrix ι ι 𝕜) (y : ι → 𝕜) : bfgsUpdate B 0 y = B := by
  simp [bfgsUpdate_def]

variable [DecidableEq ι] in
/-- With the step `s = 0` the DFP update returns `B`, since the reciprocal vanishes. -/
@[simp]
theorem dfpUpdate_zero (B : Matrix ι ι 𝕜) (y : ι → 𝕜) : dfpUpdate B 0 y = B := by
  simp [dfpUpdate_def]

/-! ### Symmetry -/

/-- The BFGS update of a symmetric matrix is symmetric. -/
theorem IsSymm.bfgsUpdate {B : Matrix ι ι 𝕜} (hB : B.IsSymm) (s y : ι → 𝕜) :
    (B.bfgsUpdate s y).IsSymm := by
  have hBs : s ᵥ* B = B *ᵥ s := by rw [← vecMul_transpose, hB.eq]
  rw [bfgsUpdate_def, hBs]
  refine (hB.sub (IsSymm.smul ?_ _)).add (IsSymm.smul ?_ _) <;>
    rw [IsSymm, transpose_vecMulVec]

variable [DecidableEq ι] in
/-- The DFP update of a symmetric matrix is symmetric. -/
theorem IsSymm.dfpUpdate {B : Matrix ι ι 𝕜} (hB : B.IsSymm) (s y : ι → 𝕜) :
    (B.dfpUpdate s y).IsSymm := by
  have hT : (1 - (y ⬝ᵥ s)⁻¹ • vecMulVec y s)ᵀ = 1 - (y ⬝ᵥ s)⁻¹ • vecMulVec s y := by
    rw [transpose_sub, transpose_one, transpose_smul, transpose_vecMulVec]
  rw [dfpUpdate_def, ← hT]
  exact (hB.mul_mul_transpose _).add (IsSymm.smul (by rw [IsSymm, transpose_vecMulVec]) _)

variable [DecidableEq ι] in
/-- The inverse BFGS update of a symmetric matrix is symmetric. -/
theorem IsSymm.bfgsInvUpdate {H : Matrix ι ι 𝕜} (hH : H.IsSymm) (s y : ι → 𝕜) :
    (H.bfgsInvUpdate s y).IsSymm := by
  rw [bfgsInvUpdate_eq_dfpUpdate]
  exact hH.dfpUpdate y s

/-- The inverse DFP update of a symmetric matrix is symmetric. -/
theorem IsSymm.dfpInvUpdate {H : Matrix ι ι 𝕜} (hH : H.IsSymm) (s y : ι → 𝕜) :
    (H.dfpInvUpdate s y).IsSymm := by
  rw [dfpInvUpdate_eq_bfgsUpdate]
  exact hH.bfgsUpdate y s

end Matrix

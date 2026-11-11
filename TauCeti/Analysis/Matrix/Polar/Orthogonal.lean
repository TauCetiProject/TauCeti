/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Polar
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Orthogonal.Basic

/-!
# The polar decomposition of an orthogonal matrix

Over `𝕜 = ℝ` or `ℂ`, an invertible matrix factors uniquely as `A = P U` with `P = √(A Aᴴ)` positive
definite and `U` unitary (`Matrix.GeneralLinearGroup.existsUnique_posDef_mul_unitary`). This file
shows that both factors of a transpose-orthogonal matrix, `Aᵀ A = 1`, are again orthogonal.

The proof uses only the uniqueness of the polar decomposition. Inverse transpose is an
automorphism of `GL n 𝕜` fixing `A`, so `A = (P⁻¹)ᵀ (U⁻¹)ᵀ`. The matrix `(P⁻¹)ᵀ` is positive
definite, being the transpose of the inverse of a positive definite matrix, and `(U⁻¹)ᵀ = (Uᴴ)ᵀ`
is unitary. By uniqueness `U = (U⁻¹)ᵀ` and `P = (P⁻¹)ᵀ`, which say that `U` and `P` are orthogonal.

Over `ℂ` this is the statement that the polar decomposition of `O(n, ℂ)` takes place inside
`O(n, ℂ)`: its unitary factor lies in `O(n, ℂ) ∩ U(n)`, which is the real orthogonal group `O(n)`,
and its positive factor in `O(n, ℂ)`. It is the input for the maximal compactness of `O(n)` in
`O(n, ℂ)`. Over `ℝ` the unitary factor is orthogonal by definition, and the content is that the
positive factor is orthogonal too.

## Main results

* `TauCeti.GLOrthogonal.toUnits_polarUnitary_mem`: the unitary factor of an orthogonal matrix is
  orthogonal.
* `TauCeti.GLOrthogonal.transpose_sqrt_mul_star_mul_self`: the positive factor `P` of an
  orthogonal matrix satisfies `Pᵀ P = 1`.
* `TauCeti.GLSpecialOrthogonal.toUnits_polarUnitary_mem`: the unitary factor of a special
  orthogonal matrix is special orthogonal.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts
  in Mathematics 222, Springer, 2015, Section 2.5.
-/

public section

noncomputable section

open Matrix Matrix.GeneralLinearGroup
open scoped MatrixOrder ComplexOrder

namespace TauCeti

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

namespace GLOrthogonal

/-- **The unitary polar factor of an orthogonal matrix is orthogonal.** If `A = P U` is the polar
decomposition of a matrix with `Aᵀ A = 1`, then `Uᵀ U = 1` as well. -/
theorem toUnits_polarUnitary_mem {A : GL n 𝕜} (hA : A ∈ GLOrthogonal n 𝕜) :
    Unitary.toUnits (Units.polarUnitary A) ∈ GLOrthogonal n 𝕜 := by
  set U := Units.polarUnitary A
  set P : GL n 𝕜 := A * (Unitary.toUnits U)⁻¹
  -- Inverse transpose fixes `A = P U`, so `A = (P⁻¹)ᵀ (U⁻¹)ᵀ`.
  have hmul : ((inverseTranspose P : GL n 𝕜) : Matrix n n 𝕜) *
      (inverseTranspose (Unitary.toUnits U) : GL n 𝕜) = A := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel_right, inverseTranspose_eq hA]
  -- The second factor `(U⁻¹)ᵀ = (Uᴴ)ᵀ` is unitary.
  have hV : ((inverseTranspose (Unitary.toUnits U) : GL n 𝕜) : Matrix n n 𝕜) ∈
      unitary (Matrix n n 𝕜) := by
    rw [coe_inverseTranspose, Unitary.val_inv_toUnits_apply]
    exact transpose_mem_unitaryGroup_iff.mpr (U⁻¹).2
  -- The first factor `(P⁻¹)ᵀ` is positive, `P` being positive definite.
  have hQ : 0 ≤ ((inverseTranspose P : GL n 𝕜) : Matrix n n 𝕜) := by
    rw [coe_inverseTranspose, GeneralLinearGroup.coe_inv, coe_mul_inv_toUnits_polarUnitary]
    exact nonneg_iff_posSemidef.mpr (posDef_sqrt_mul_star A).posSemidef.inv.transpose
  -- By uniqueness of the polar decomposition, `U = (U⁻¹)ᵀ`.
  have hU := Units.polarUnitary_eq_of_mul_eq A hQ (v := ⟨_, hV⟩) hmul
  rw [mem_iff_inverseTranspose_eq, Units.ext_iff, Unitary.val_toUnits_apply]
  exact congrArg Subtype.val hU.symm

/-- **The positive polar factor of an orthogonal matrix is orthogonal.** If `A = P U` is the polar
decomposition of a matrix with `Aᵀ A = 1`, then `Pᵀ P = 1`. -/
theorem transpose_sqrt_mul_star_mul_self {A : GL n 𝕜} (hA : A ∈ GLOrthogonal n 𝕜) :
    (CFC.sqrt ((A : Matrix n n 𝕜) * star (A : Matrix n n 𝕜)))ᵀ *
      CFC.sqrt ((A : Matrix n n 𝕜) * star (A : Matrix n n 𝕜)) = 1 := by
  rw [← coe_mul_inv_toUnits_polarUnitary, ← mem_iff]
  exact mul_mem hA (inv_mem (toUnits_polarUnitary_mem hA))

end GLOrthogonal

namespace GLSpecialOrthogonal

/-- **The unitary polar factor of a special orthogonal matrix is special orthogonal.** -/
theorem toUnits_polarUnitary_mem {A : GL n 𝕜} (hA : A ∈ GLSpecialOrthogonal n 𝕜) :
    Unitary.toUnits (Units.polarUnitary A) ∈ GLSpecialOrthogonal n 𝕜 := by
  rw [mem_iff] at hA ⊢
  exact ⟨GLOrthogonal.toUnits_polarUnitary_mem hA.1, det_polarUnitary_of_det_eq_one A hA.2⟩

end GLSpecialOrthogonal

end TauCeti

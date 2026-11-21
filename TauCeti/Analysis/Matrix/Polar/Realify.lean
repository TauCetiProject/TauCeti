/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Polar.Deformation
public import TauCeti.Analysis.Matrix.Realify

/-!
# The polar decomposition of a realified matrix

Over `𝕜 = ℝ` or `ℂ`, every invertible matrix `A : GL n 𝕜` is uniquely `A = P U` with
`P = √(A Aᴴ)` positive definite and `U = Units.polarUnitary A` unitary
(`Matrix.GeneralLinearGroup.existsUnique_posDef_mul_unitary`). This file shows that realification
`Matrix.GeneralLinearGroup.realify n 𝕜 : GL n 𝕜 →* GL (n ⊕ n) ℝ`, which identifies `GL(n, ℂ)` with
the invertible real matrices commuting with `J`, carries this decomposition to the polar
decomposition of the real matrix `A_ℝ`:

`√(A_ℝ A_ℝᵀ) = P_ℝ`,  `polarUnitary A_ℝ = U_ℝ`.

The square root identity holds because realification commutes with the continuous functional
calculus (`Matrix.realify_sqrt`) and turns the conjugate transpose into the transpose. The second
identity follows from uniqueness of the polar decomposition, since `P_ℝ` is positive definite
(`Matrix.posDef_realify_iff`) and `U_ℝ` is orthogonal (`Matrix.realify_mem_orthogonalGroup_iff`).
As realification also commutes with real powers (`Matrix.realify_rpow`), it intertwines the polar
contractions `A ↦ P ^ (1 - t) U` of `Matrix.GeneralLinearGroup.polarDeformation`.

Consequently the realified group `(realify n 𝕜).range` contains both polar factors of each of its
elements, and the polar deformation `P ^ (1 - t) U` of each of its elements stays inside it, ending
at the realified unitary factor. For `𝕜 = ℂ` this is the
polar decomposition of the realified `GL(n, ℂ)` inside `GL(2n, ℝ)`, whose orthogonal part is the
realified `U(n)`.

## Main results

* `Matrix.GeneralLinearGroup.sqrt_mul_star_realify`: the positive polar factor of `A_ℝ` is the
  realification of that of `A`.
* `Matrix.GeneralLinearGroup.coe_polarUnitary_realify`: the orthogonal polar factor of `A_ℝ` is the
  realification of the unitary polar factor of `A`.
* `Matrix.GeneralLinearGroup.polarDeformation_realify`: realification intertwines the polar
  deformations.
* `Matrix.GeneralLinearGroup.toUnits_polarUnitary_mem_range_realify`,
  `Matrix.GeneralLinearGroup.polarDeformation_mem_range_realify`: the realified group contains the
  orthogonal polar factors and the polar deformations of its elements.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts
  in Mathematics 222, Springer, 2015, Section 2.5 (polar decomposition).
* Anthony W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics
  140, Birkhäuser, 2002, Chapter I, Section 17 (polar decomposition of a closed linear group stable
  under transpose).
-/

public section

noncomputable section

open scoped MatrixOrder ComplexOrder

namespace Matrix.GeneralLinearGroup

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- **The positive polar factor of a realified matrix** is the realification of the positive polar
factor: `√(A_ℝ A_ℝᵀ) = (√(A Aᴴ))_ℝ`. -/
theorem sqrt_mul_star_realify (A : GL n 𝕜) :
    CFC.sqrt ((realify n 𝕜 A : Matrix (n ⊕ n) (n ⊕ n) ℝ) *
        star (realify n 𝕜 A : Matrix (n ⊕ n) (n ⊕ n) ℝ)) =
      (CFC.sqrt ((A : Matrix n n 𝕜) * star (A : Matrix n n 𝕜))).realify := by
  rw [coe_realify, ← realify_star, ← realify_mul, realify_sqrt]

/-- **The orthogonal polar factor of a realified matrix** is the realification of the unitary polar
factor. -/
@[simp]
theorem coe_polarUnitary_realify (A : GL n 𝕜) :
    ((realify n 𝕜 A).polarUnitary : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      ((A.polarUnitary : unitaryGroup n 𝕜) : Matrix n n 𝕜).realify := by
  have hU : ((A.polarUnitary : unitaryGroup n 𝕜) : Matrix n n 𝕜).realify ∈
      unitary (Matrix (n ⊕ n) (n ⊕ n) ℝ) :=
    realify_mem_orthogonalGroup_iff.2 A.polarUnitary.2
  -- `A_ℝ = P_ℝ U_ℝ` with `P_ℝ` positive and `U_ℝ` orthogonal, so this is its polar decomposition.
  have hP : 0 ≤ (CFC.sqrt ((A : Matrix n n 𝕜) * star (A : Matrix n n 𝕜))).realify :=
    realify_nonneg_iff.2 (posDef_sqrt_mul_star A).posSemidef.nonneg
  have h : (CFC.sqrt ((A : Matrix n n 𝕜) * star (A : Matrix n n 𝕜))).realify *
      ((⟨_, hU⟩ : unitary (Matrix (n ⊕ n) (n ⊕ n) ℝ)) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
        (realify n 𝕜 A : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
    rw [coe_realify, Subtype.coe_mk, ← realify_mul, Units.sqrt_mul_star_mul_polarUnitary]
  exact congrArg Subtype.val (Units.polarUnitary_eq_of_mul_eq _ hP h)

/-- The orthogonal polar factor of a realified matrix, as an invertible matrix, is the
realification of the unitary polar factor. -/
@[simp]
theorem toUnits_polarUnitary_realify (A : GL n 𝕜) :
    Unitary.toUnits (realify n 𝕜 A).polarUnitary = realify n 𝕜 (Unitary.toUnits A.polarUnitary) :=
  Units.ext (by simp)

/-- **Realification intertwines the polar deformations** `P ^ (1 - t) U`. -/
@[simp]
theorem polarDeformation_realify (A : GL n 𝕜) (t : ℝ) :
    polarDeformation (realify n 𝕜 A) t = realify n 𝕜 (polarDeformation A t) :=
  Units.ext (by simp [coe_polarDeformation, realify_mul])

/-- **The realified group contains the orthogonal polar factors of its elements.** -/
theorem toUnits_polarUnitary_mem_range_realify {M : GL (n ⊕ n) ℝ}
    (hM : M ∈ (realify n 𝕜).range) : Unitary.toUnits M.polarUnitary ∈ (realify n 𝕜).range := by
  obtain ⟨A, rfl⟩ := hM
  exact ⟨_, (toUnits_polarUnitary_realify A).symm⟩

/-- **The polar deformation stays in the realified group**: for an element `M = P U` of the
realified group, every `P ^ (1 - t) U` is again realified. -/
theorem polarDeformation_mem_range_realify {M : GL (n ⊕ n) ℝ} (hM : M ∈ (realify n 𝕜).range)
    (t : ℝ) : polarDeformation M t ∈ (realify n 𝕜).range := by
  obtain ⟨A, rfl⟩ := hM
  exact ⟨_, (polarDeformation_realify A t).symm⟩

end Matrix.GeneralLinearGroup

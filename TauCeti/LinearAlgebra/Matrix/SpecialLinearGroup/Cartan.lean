/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Cartan

/-!
# The KAK decomposition of the real and complex special linear groups

Every real or complex matrix of determinant one is `U * diagonal d * V`, with `U`, `V` special
orthogonal or special unitary and `d` positive, decreasing and of product one. The diagonal `d`
is unique, even when entries repeat. Thus the closed positive chamber of the determinant-one
positive diagonal subgroup parametrizes the double cosets of the maximal compact subgroup of
`SLₙ(ℝ)` and `SLₙ(ℂ)`.

The diagonal factor is that of the `GLₙ` decomposition
`Matrix.GeneralLinearGroup.existsUnique_pos_antitone_and_eq_unitary_mul_diagonal_mul_unitary`:
its product is the absolute value of the determinant. Its compact factors are corrected to
determinant one through the classification of the two-sided special unitary orbits of square
matrices by singular values and determinant,
`Matrix.exists_specialUnitary_mul_mul_specialUnitary_iff_singularValues_eq_and_det_eq`.

## Main results

* `existsUnique_pos_antitone_and_eq_specialUnitary_mul_diagonal_mul_specialUnitary`, in the
  namespace `Matrix.SpecialLinearGroup`: the KAK decomposition of `SLₙ(ℝ)` and `SLₙ(ℂ)`, with
  uniqueness of the diagonal factor.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Chapter VII.
* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Section 2.6.
-/

public section

namespace Matrix.SpecialLinearGroup

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- The KAK decomposition of `SLₙ(ℝ)` and `SLₙ(ℂ)`: each matrix of determinant one has a unique
positive decreasing diagonal factor of product one between two special orthogonal or special
unitary factors. Uniqueness concerns the diagonal only, so repeated singular values are
allowed. -/
theorem existsUnique_pos_antitone_and_eq_specialUnitary_mul_diagonal_mul_specialUnitary
    (g : SpecialLinearGroup (Fin n) 𝕜) :
    ∃! d : Fin n → ℝ, (∀ i, 0 < d i) ∧ Antitone d ∧ ∏ i, d i = 1 ∧
      ∃ U V : specialUnitaryGroup (Fin n) 𝕜,
        (g : Matrix (Fin n) (Fin n) 𝕜) =
          (U : Matrix (Fin n) (Fin n) 𝕜) * diagonal (fun i ↦ (d i : 𝕜)) * V := by
  obtain ⟨d, ⟨hd, hanti, U, V, hg⟩, huniq⟩ :=
    GeneralLinearGroup.existsUnique_pos_antitone_and_eq_unitary_mul_diagonal_mul_unitary
      (toGL g)
  rw [coe_GL_coe_matrix] at hg
  -- The product of the diagonal is the absolute value of `det g = 1`.
  have hprod : ∏ i, d i = 1 := by
    have hnorm := congrArg (‖·‖) (congrArg det hg)
    simp only [det_coe, norm_one, det_mul, norm_mul, det_diagonal, ← RCLike.ofReal_prod,
      RCLike.norm_ofReal, CStarRing.norm_of_mem_unitary (det_of_mem_unitary U.2),
      CStarRing.norm_of_mem_unitary (det_of_mem_unitary V.2), one_mul, mul_one] at hnorm
    rw [hnorm, abs_of_pos (Finset.prod_pos fun i _ ↦ hd i)]
  refine ⟨d, ⟨hd, hanti, hprod, ?_⟩, fun d' ⟨hd', hanti', _, U', V', hg'⟩ ↦
    huniq d' ⟨hd', hanti', ⟨U', U'.2.1⟩, ⟨V', V'.2.1⟩, by rwa [coe_GL_coe_matrix]⟩⟩
  -- `g` and the diagonal factor have the same singular values and the same determinant.
  refine (exists_specialUnitary_mul_mul_specialUnitary_iff_singularValues_eq_and_det_eq _ _).mpr
    ⟨(exists_unitary_mul_mul_unitary_iff_singularValues_eq _ _).mp ⟨U, V, hg⟩, ?_⟩
  rw [det_coe, det_diagonal, ← RCLike.ofReal_prod, hprod, RCLike.ofReal_one]

end Matrix.SpecialLinearGroup

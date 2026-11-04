/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Polar
public import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# The polar decomposition of a real symplectic matrix

A real symplectic matrix `A`, one with `A J Aᵀ = J`, is invertible, so it has a polar
decomposition `A = P U` with `P = √(A Aᵀ)` positive definite and `U` orthogonal (see
`TauCeti/Analysis/Matrix/Polar.lean`). This file proves that both factors are again symplectic,
and so is every real power `P ^ s` of the positive factor. Consequently `U` lies in the
intersection of the symplectic and orthogonal groups, and `t ↦ P ^ (1 - t) U` is a path inside
the symplectic group from `A` to `U`. This is the input for the connectedness of the real
symplectic group, and for its maximal compact subgroup, from the corresponding facts about this
intersection.

The key identity concerns a positive semidefinite symplectic matrix `S`. Being symmetric, it
satisfies `S J S = J`, so conjugation by `J` inverts it: `J S J⁻¹ = S⁻¹`. Since `J` is orthogonal,
conjugation by `J` commutes with the continuous functional calculus, which turns this into
`J S ^ s J⁻¹ = S ^ (-s)` for every real `s`, and that is the symplectic condition for the
symmetric matrix `S ^ s`.

## Main results

* `SymplecticGroup.rpow_neg_eq_J_conj_rpow`: for a positive semidefinite symplectic matrix `S`,
  `S ^ (-s) = J S ^ s J⁻¹`.
* `SymplecticGroup.rpow_mem`: every real power of a positive semidefinite symplectic matrix is
  symplectic.
* `SymplecticGroup.sqrt_mul_star_mem`: the positive factor `√(A Aᵀ)` of a symplectic matrix is
  symplectic.
* `SymplecticGroup.polarUnitary_mem`: the orthogonal factor of a symplectic matrix is symplectic.
* `SymplecticGroup.joinedIn_polarUnitary`: a symplectic matrix is joined to its orthogonal factor
  by a path of symplectic matrices.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  Graduate Texts in Mathematics 27, Oxford University Press, 2017, Section 2.2 (the symplectic
  linear group and the polar decomposition of its elements).
-/

public section

open scoped MatrixOrder

open Matrix

namespace SymplecticGroup

variable {l : Type*} [Fintype l] [DecidableEq l]

variable {S : Matrix (l ⊕ l) (l ⊕ l) ℝ}

/-- **Conjugation by `J` inverts the real powers of a positive symplectic matrix.** For a positive
semidefinite symplectic matrix `S` and every real `s`, `S ^ (-s) = J S ^ s J⁻¹`; for `s = 1` this
is `S⁻¹ = J S J⁻¹`. -/
theorem rpow_neg_eq_J_conj_rpow (hS : S.PosSemidef) (hSp : S ∈ symplecticGroup l ℝ) (s : ℝ) :
    S ^ (-s) = J l ℝ * S ^ s * (J l ℝ)⁻¹ := by
  obtain ⟨S', rfl⟩ := (isUnit_iff_isUnit_det S).2 (symplectic_det hSp)
  -- For symmetric `S`, the symplectic inverse formula `S⁻¹ = -J Sᵀ J` reads `S⁻¹ = J S Jᵀ`.
  have hSym : (S' : Matrix (l ⊕ l) (l ⊕ l) ℝ)ᵀ = S' := by
    simpa [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hS.isHermitian
  have hinv : J l ℝ * S' * star (J l ℝ) = ↑S'⁻¹ := by
    rw [coe_units_inv, inv_eq_symplectic_inv _ hSp, hSym, star_J]
    simp only [mul_neg, neg_mul]
  -- Conjugation by the orthogonal matrix `J` commutes with real powers.
  have h := CFC.rpow_unitary_mul_mul_star ⟨J l ℝ, J_mem_unitaryGroup l ℝ⟩ (S' : Matrix _ _ ℝ) s
  rw [Subtype.coe_mk, hinv, ← CFC.rpow_neg S' s hS.nonneg, star_J] at h
  rw [h, J_inv]

/-- **Every real power of a positive symplectic matrix is symplectic.** For a positive
semidefinite symplectic matrix `S`, the matrix `S ^ s` is symplectic for every real `s`. -/
theorem rpow_mem (hS : S.PosSemidef) (hSp : S ∈ symplecticGroup l ℝ) (s : ℝ) :
    S ^ s ∈ symplecticGroup l ℝ := by
  have hpos : IsStrictlyPositive S := IsStrictlyPositive.iff_of_unital.2
    ⟨hS.nonneg, (isUnit_iff_isUnit_det S).2 (symplectic_det hSp)⟩
  have hSym : (S ^ s)ᵀ = S ^ s := by
    simpa [IsHermitian, conjTranspose_eq_transpose_of_trivial] using
      (nonneg_iff_posSemidef.1 (CFC.rpow_nonneg (a := S) (y := s))).isHermitian
  -- `J S ^ s = S ^ (-s) J`, so `S ^ s J S ^ s = S ^ s S ^ (-s) J = J`.
  have hJ : J l ℝ * S ^ s = S ^ (-s) * J l ℝ :=
    ((eq_J_conj_iff_mul_J_eq _ _).1 (rpow_neg_eq_J_conj_rpow hS hSp s)).symm
  rw [mem_iff, hSym, mul_assoc, hJ, ← mul_assoc, CFC.rpow_mul_rpow_neg s hpos, one_mul]

/-- **The positive polar factor of a symplectic matrix is symplectic.** If `A` is symplectic,
then so is `√(A Aᵀ)`. -/
theorem sqrt_mul_star_mem {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ symplecticGroup l ℝ) :
    CFC.sqrt (A * star A) ∈ symplecticGroup l ℝ := by
  have hAA : (A * star A).PosSemidef := nonneg_iff_posSemidef.1 (mul_star_self_nonneg A)
  rw [CFC.sqrt_eq_rpow]
  refine rpow_mem hAA (Submonoid.mul_mem _ hA ?_) _
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  exact transpose_mem hA

/-- **The orthogonal polar factor of a symplectic matrix is symplectic.** If `A = P U` is the
polar decomposition of an invertible symplectic matrix, then `U` is symplectic as well as
orthogonal. -/
theorem polarUnitary_mem {A : GL (l ⊕ l) ℝ}
    (hA : (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) ∈ symplecticGroup l ℝ) :
    ((Units.polarUnitary A : unitary (Matrix (l ⊕ l) (l ⊕ l) ℝ)) : Matrix (l ⊕ l) (l ⊕ l) ℝ) ∈
      symplecticGroup l ℝ := by
  have hP := sqrt_mul_star_mem hA
  rw [Units.coe_polarUnitary,
    CFC.inverse_eq_rpow_neg_one (Units.isStrictlyPositive_sqrt_mul_star A)]
  exact Submonoid.mul_mem _ (rpow_mem (nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg _)) hP _) hA

/-- **The positive factor contracts inside the symplectic group.** An invertible symplectic
matrix `A = P U` is joined to its orthogonal factor `U` by the path `t ↦ P ^ (1 - t) U` of
symplectic matrices. -/
theorem joinedIn_polarUnitary {A : GL (l ⊕ l) ℝ}
    (hA : (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) ∈ symplecticGroup l ℝ) :
    JoinedIn (symplecticGroup l ℝ : Set (Matrix (l ⊕ l) (l ⊕ l) ℝ)) A
      (Units.polarUnitary A : Matrix (l ⊕ l) (l ⊕ l) ℝ) := by
  set P := CFC.sqrt ((A : Matrix (l ⊕ l) (l ⊕ l) ℝ) * star (A : Matrix (l ⊕ l) (l ⊕ l) ℝ))
  have hP : P.PosDef := Matrix.GeneralLinearGroup.posDef_sqrt_mul_star A
  refine JoinedIn.ofLine (f := fun t : ℝ ↦ P ^ (1 - t) * Units.polarUnitary A)
    ((hP.continuous_const_rpow.comp (continuous_sub_left 1)).mul continuous_const).continuousOn
    ?_ ?_ ?_
  · simp only [sub_zero, CFC.rpow_one P hP.posSemidef.nonneg]
    exact Units.sqrt_mul_star_mul_polarUnitary A
  · simp only [sub_self, CFC.rpow_zero P hP.posSemidef.nonneg, one_mul]
  · rintro _ ⟨t, -, rfl⟩
    exact Submonoid.mul_mem _ (rpow_mem hP.posSemidef (sqrt_mul_star_mem hA) _)
      (polarUnitary_mem hA)

end SymplecticGroup

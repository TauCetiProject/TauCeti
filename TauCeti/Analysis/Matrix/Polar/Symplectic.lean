/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Polar
public import TauCeti.LinearAlgebra.SymplecticGroup

import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Cartan

/-!
# The polar decomposition of a symplectic matrix

Over `𝕜 = ℝ` or `ℂ`, a symplectic matrix `A`, one with `A J Aᵀ = J`, is invertible, so it has a
polar decomposition `A = P U` with `P = √(A Aᴴ)` positive definite and `U` unitary (see
`TauCeti/Analysis/Matrix/Polar.lean`). This file proves that both factors are again symplectic, so
that `U` lies in the intersection of the symplectic and unitary groups. Over `ℝ` this intersection
is the orthogonal symplectic group, the realified unitary group; over `ℂ` it is the compact
symplectic group `Sp(n)`. This is the input for the maximal compact subgroups of the real and
complex symplectic groups. Over `ℝ`, every real power `P ^ s` of the positive factor is symplectic
too, so `t ↦ P ^ (1 - t) U` is a path inside the symplectic group from `A` to `U`; this is the input
for the connectedness of the real symplectic group.

For the two factors, write the symplectic condition as `(A⁻¹)ᵀ = J A J⁻¹`. Inverse transpose
carries the polar decomposition `A = P U` to the polar decomposition `(A⁻¹)ᵀ = (P⁻¹)ᵀ (U⋆)ᵀ`
(`Matrix.GeneralLinearGroup.sqrt_inverseTranspose` and
`Matrix.GeneralLinearGroup.polarUnitary_inverseTranspose`), and conjugation by the unitary matrix
`J` carries it to the polar decomposition `J A J⁻¹ = (J P J⁻¹) (J U J⁻¹)`. By uniqueness of the
polar decomposition, `(P⁻¹)ᵀ = J P J⁻¹` and `(U⋆)ᵀ = J U J⁻¹`, which are the symplectic conditions
for `P` and for `U`. Over `ℂ` the condition involves the transpose rather than the conjugate
transpose, which is why the factors of `(A⁻¹)ᵀ` are needed and not those of `A⋆`.

The real powers rest on a sharper identity for a positive semidefinite real symplectic matrix `S`.
Being symmetric, it satisfies `S J S = J`, so conjugation by `J` inverts it: `J S J⁻¹ = S⁻¹`. Since
`J` is orthogonal, conjugation by `J` commutes with the continuous functional calculus, which turns
this into `J S ^ s J⁻¹ = S ^ (-s)` for every real `s`, and that is the symplectic condition for the
symmetric matrix `S ^ s`.

## Main results

* `SymplecticGroup.sqrt_mul_star_mem`: the positive factor `√(A Aᴴ)` of a symplectic matrix is
  symplectic.
* `SymplecticGroup.polarUnitary_mem`: the unitary factor of a symplectic matrix is symplectic.
* `SymplecticGroup.rpow_neg_eq_J_conj_rpow`: for a positive semidefinite real symplectic matrix
  `S`, `S ^ (-s) = J S ^ s J⁻¹`.
* `SymplecticGroup.rpow_mem`: every real power of a positive semidefinite real symplectic matrix is
  symplectic.
* `SymplecticGroup.joinedIn_polarUnitary`: a real symplectic matrix is joined to its orthogonal
  factor by a path of symplectic matrices.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  Graduate Texts in Mathematics 27, Oxford University Press, 2017, Section 2.2 (the symplectic
  linear group and the polar decomposition of its elements).
* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts
  in Mathematics 222, Springer, 2015, Section 2.5 (polar decompositions of matrix groups closed
  under conjugate transpose).
-/

public section

open scoped MatrixOrder

open Matrix

namespace SymplecticGroup

variable {l : Type*} [Fintype l] [DecidableEq l]

section RCLike

open scoped ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The matrix `J` as a unitary matrix. -/
private def unitaryJ : unitary (Matrix (l ⊕ l) (l ⊕ l) 𝕜) :=
  ⟨J l 𝕜, J_mem_unitaryGroup l 𝕜⟩

private theorem coe_unitaryJ : ((unitaryJ : unitary (Matrix (l ⊕ l) (l ⊕ l) 𝕜)) :
    Matrix (l ⊕ l) (l ⊕ l) 𝕜) = J l 𝕜 :=
  (rfl)

/-- On an invertible symplectic matrix, inverse transpose is conjugation by `J`
(`TauCeti.GLSymplectic.coe_cartanInvolution`), here with `J` as a unitary, so that `J⁻¹ = J⋆`. -/
private theorem inverseTranspose_eq {A : GL (l ⊕ l) 𝕜}
    (hA : (A : Matrix (l ⊕ l) (l ⊕ l) 𝕜) ∈ symplecticGroup l 𝕜) :
    GeneralLinearGroup.inverseTranspose A =
      Unitary.toUnits unitaryJ * A * Unitary.toUnits (star unitaryJ) := by
  rw [← TauCeti.GLSymplectic.coe_cartanInvolution
      ⟨A, TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup.2 hA⟩,
    TauCeti.GLSymplectic.cartanInvolution_apply]
  refine Units.ext ?_
  simp [TauCeti.GLSymplectic.coe_symJ, coe_unitaryJ, coe_units_inv, J_inv, star_J]

/-- **The unitary polar factor of a symplectic matrix is symplectic.** If `A = P U` is the polar
decomposition of an invertible symplectic matrix over `ℝ` or `ℂ`, then `U` is symplectic as well as
unitary. -/
theorem polarUnitary_mem {A : GL (l ⊕ l) 𝕜}
    (hA : (A : Matrix (l ⊕ l) (l ⊕ l) 𝕜) ∈ symplecticGroup l 𝕜) :
    ((Units.polarUnitary A : unitary (Matrix (l ⊕ l) (l ⊕ l) 𝕜)) : Matrix (l ⊕ l) (l ⊕ l) 𝕜) ∈
      symplecticGroup l 𝕜 := by
  -- the unitary factor of `(A⁻¹)ᵀ = J A J⁻¹` is both `J U J⁻¹` and the conjugate `(U⋆)ᵀ` of `U`
  have h := GeneralLinearGroup.polarUnitary_inverseTranspose A
  rw [inverseTranspose_eq hA, Units.polarUnitary_unitary_mul_mul_unitary] at h
  set U := Units.polarUnitary A
  have hJU : J l 𝕜 * U * star (J l 𝕜) = (star (U : Matrix (l ⊕ l) (l ⊕ l) 𝕜))ᵀ := by
    rw [star_eq_conjTranspose (U : Matrix (l ⊕ l) (l ⊕ l) 𝕜), conjTranspose_transpose,
      ← UnitaryGroup.map_star_coe, ← h]
    simp [coe_unitaryJ]
  exact mem_of_J_conj_eq_transpose (Unitary.star_mul_self_of_mem U.2) (by rwa [J_inv, ← star_J])

/-- **The positive polar factor of a symplectic matrix is symplectic.** If `A` is symplectic over
`ℝ` or `ℂ`, then so is `√(A Aᴴ)`. -/
theorem sqrt_mul_star_mem {A : Matrix (l ⊕ l) (l ⊕ l) 𝕜} (hA : A ∈ symplecticGroup l 𝕜) :
    CFC.sqrt (A * star A) ∈ symplecticGroup l 𝕜 := by
  obtain ⟨A, rfl⟩ := (isUnit_iff_isUnit_det A).2 (symplectic_det hA)
  set P := CFC.sqrt ((A : Matrix (l ⊕ l) (l ⊕ l) 𝕜) * star (A : Matrix (l ⊕ l) (l ⊕ l) 𝕜))
  -- the positive factor of `(A⁻¹)ᵀ = J A J⁻¹` is both `J P J⁻¹` and `(P⁻¹)ᵀ`
  have h := GeneralLinearGroup.sqrt_inverseTranspose A
  rw [inverseTranspose_eq hA, Units.sqrt_unitary_mul_mul_unitary, coe_unitaryJ] at h
  have hP : IsUnit P.det :=
    (isUnit_iff_isUnit_det P).1 (GeneralLinearGroup.posDef_sqrt_mul_star A).isUnit
  exact mem_of_J_conj_eq_transpose (nonsing_inv_mul P hP) (by rwa [J_inv, ← star_J])

end RCLike

section Real

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

end Real

end SymplecticGroup

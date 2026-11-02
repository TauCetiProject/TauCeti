/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# Existence of Smith normal forms

A square matrix `A` of nonzero determinant over a principal ideal domain is equivalent to a
diagonal matrix: `L * A * Q = diagonal s` with `L`, `Q` of unit determinant. This is the
matrix-level form of Mathlib's basis-level `Submodule.exists_smith_normal_form_of_rank_eq`,
applied to the image lattice of `A`. Over a discrete valuation ring, sorting the diagonal by
valuation makes it a divisibility chain `s₀ ∣ s₁ ∣ ⋯`, a Smith normal form of `A`.

The refinement over `ℤ` with transformations of determinant `1` and a positive diagonal is in
`TauCeti.LinearAlgebra.Matrix.SmithNormalForm.Int`, and the characterisation of the invariant
factors by minors is in `TauCeti.LinearAlgebra.Matrix.InvariantFactor`.

## Main results

* `Matrix.exists_mul_mul_eq_diagonal_of_det_ne_zero`: over a principal ideal domain, a square
  matrix of nonzero determinant is equivalent to a diagonal matrix.
* `Matrix.exists_smith_normal_form_of_isDiscreteValuationRing`: over a discrete valuation ring,
  the diagonal can be chosen to be a divisibility chain.
-/

public section

namespace Matrix

variable {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}

/-- **Diagonalisation over a principal ideal domain.** A square matrix of nonzero determinant over
a principal ideal domain is equivalent to a diagonal matrix: there are `L`, `Q` of unit
determinant with `L * A * Q = diagonal s`. -/
theorem exists_mul_mul_eq_diagonal_of_det_ne_zero [IsPrincipalIdealRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R) (hA : A.det ≠ 0) :
    ∃ (L Q : Matrix ι ι R) (s : ι → R),
      IsUnit L.det ∧ IsUnit Q.det ∧ L * A * Q = diagonal s := by
  set e := Pi.basisFun R ι
  have hinj : Function.Injective A.mulVecLin := fun x y hxy ↦
    mulVec_injective_of_det_ne_zero hA (by simpa using hxy)
  obtain ⟨b, s, c, hc⟩ := Submodule.exists_smith_normal_form_of_rank_eq e
    (LinearMap.finrank_range_of_inj hinj)
  -- transport the basis `c` of the image back to the source along `A`
  set r := c.map (LinearEquiv.ofInjective A.mulVecLin hinj).symm
  have hr (i : ι) : A.mulVecLin (r i) = s i • b i := by
    rw [← hc i]
    exact congrArg Subtype.val ((LinearEquiv.ofInjective A.mulVecLin hinj).apply_symm_apply (c i))
  have hdiag : LinearMap.toMatrix r b A.mulVecLin = diagonal s := by
    ext i j
    rw [LinearMap.toMatrix_apply, hr, map_smul, b.repr_self, diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  refine ⟨b.toMatrix e, e.toMatrix r, s, ?_, ?_, ?_⟩
  · exact isUnit_det_of_right_inverse (b.toMatrix_mul_toMatrix_flip e)
  · exact isUnit_det_of_right_inverse (e.toMatrix_mul_toMatrix_flip r)
  · have hA' : LinearMap.toMatrix e e A.mulVecLin = A := by
      rw [LinearMap.toMatrix_eq_toMatrix', ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
    rw [← hdiag, ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix r e b e, hA']

/-- **Smith normal form over a discrete valuation ring.** A square matrix of nonzero determinant
over a discrete valuation ring has a Smith normal form: there are `L`, `Q` of unit determinant and
a divisibility chain `s₀ ∣ s₁ ∣ ⋯` with `L * A * Q = diagonal s`. -/
theorem exists_smith_normal_form_of_isDiscreteValuationRing [IsDiscreteValuationRing R]
    (A : Matrix (Fin n) (Fin n) R) (hA : A.det ≠ 0) :
    ∃ (L Q : Matrix (Fin n) (Fin n) R) (s : Fin n → R), IsUnit L.det ∧ IsUnit Q.det ∧
      (∀ ⦃i j : Fin n⦄, i ≤ j → s i ∣ s j) ∧ L * A * Q = diagonal s := by
  obtain ⟨L, Q, s, hL, hQ, h⟩ := exists_mul_mul_eq_diagonal_of_det_ne_zero A hA
  -- reorder the diagonal by increasing valuation
  set σ := Tuple.sort (IsDiscreteValuationRing.addVal R ∘ s)
  refine ⟨L.submatrix σ id, Q.submatrix id σ, s ∘ σ, ?_, ?_, fun i j hij ↦ ?_, ?_⟩
  · rw [det_permute]
    exact (σ.sign.isUnit.map (Int.castRingHom R)).mul hL
  · rw [det_permute']
    exact (σ.sign.isUnit.map (Int.castRingHom R)).mul hQ
  · exact IsDiscreteValuationRing.addVal_le_iff_dvd.mp
      (Tuple.monotone_sort (IsDiscreteValuationRing.addVal R ∘ s) hij)
  · rw [← submatrix_id_id A, ← submatrix_mul L A σ id id Function.bijective_id,
      ← submatrix_mul (L * A) Q σ id σ Function.bijective_id, h, submatrix_diagonal_equiv]

end Matrix

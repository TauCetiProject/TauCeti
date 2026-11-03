/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SmithNormalForm.Diagonal
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Existence of Smith normal forms

Over a discrete valuation ring, sorting the diagonal supplied by
`Matrix.exists_mul_mul_eq_diagonal` by valuation makes it a divisibility chain
`s₀ ∣ s₁ ∣ ⋯`, a Smith normal form of the matrix. Singular matrices are included:
zero entries have infinite valuation and appear at the end of the chain.

The refinement over `ℤ` with transformations of determinant `1` and a positive diagonal is in
`TauCeti.LinearAlgebra.Matrix.SmithNormalForm.Int`, and the characterisation of the invariant
factors by minors is in `TauCeti.LinearAlgebra.Matrix.InvariantFactor`.

## Main results

* `Matrix.exists_smith_normal_form_of_isDiscreteValuationRing`: over a discrete valuation ring,
  the diagonal can be chosen to be a divisibility chain.
-/

public section

namespace Matrix

variable {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}

/-- **Smith normal form over a discrete valuation ring.** Every square matrix over a discrete
valuation ring has a Smith normal form: there are `L`, `Q` of unit determinant and a divisibility
chain `s₀ ∣ s₁ ∣ ⋯` with `L * A * Q = diagonal s`. Zero diagonal entries are allowed. -/
theorem exists_smith_normal_form_of_isDiscreteValuationRing [IsDiscreteValuationRing R]
    (A : Matrix (Fin n) (Fin n) R) :
    ∃ (L Q : Matrix (Fin n) (Fin n) R) (s : Fin n → R), IsUnit L.det ∧ IsUnit Q.det ∧
      (∀ ⦃i j : Fin n⦄, i ≤ j → s i ∣ s j) ∧ L * A * Q = diagonal s := by
  obtain ⟨L, Q, s, hL, hQ, h⟩ := exists_mul_mul_eq_diagonal A
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

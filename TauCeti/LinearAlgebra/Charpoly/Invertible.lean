/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Charpoly.Newton

/-!
# Recovering invertible operators from traces of positive powers

Traces of positive powers do not see zero eigenvalues, so in general they do not determine
the dimension. For an operator with nonzero determinant, the degree of `det (1 - X A)` is
the dimension. Over an additively torsion-free ring, Newton's identities therefore recover both
the dimension and the characteristic polynomial, even when comparing different finite free modules.

This is the characteristic polynomial step in the determinant method of grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`),
`src/Lib/Adelic/TraceFormula/LineDeterminant.lean` (`New.charpoly_eq_of_trace_pow_eq`).
The proofs here use Tau Ceti's Newton identities.
-/

public section

namespace Matrix

variable {R ι κ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- For a matrix with nonzero determinant, `det (1 - X A)` has degree equal to its size. -/
theorem natDegree_charpolyRev_of_det_ne_zero {A : Matrix ι ι R} (hA : A.det ≠ 0) :
    A.charpolyRev.natDegree = Fintype.card ι := by
  apply le_antisymm (natDegree_charpolyRev_le A)
  apply Polynomial.le_natDegree_of_ne_zero
  rw [coeff_charpolyRev_card]
  exact (isUnit_neg_one.pow _).mul_right_eq_zero.not.mpr hA

/-- Over an additively torsion-free ring, matrices with nonzero determinants and equal traces
of positive powers have equal sizes. No equality of sizes is assumed. -/
theorem card_eq_of_trace_pow_eq_of_det_ne_zero [IsAddTorsionFree R]
    {A : Matrix ι ι R} {B : Matrix κ κ R} (hA : A.det ≠ 0) (hB : B.det ≠ 0)
    (h : ∀ j, 0 < j → (A ^ j).trace = (B ^ j).trace) : Fintype.card ι = Fintype.card κ := by
  have : Nontrivial R := ⟨⟨A.det, 0, hA⟩⟩
  have hrev := charpolyRev_eq_iff_trace_pow_eq.mpr h
  rw [← natDegree_charpolyRev_of_det_ne_zero hA,
    ← natDegree_charpolyRev_of_det_ne_zero hB, hrev]

end Matrix

namespace LinearMap

variable {R M N : Type*} [CommRing R] [IsAddTorsionFree R]
  [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
  [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
  {f : Module.End R M} {g : Module.End R N}

/-- Over an additively torsion-free ring, positive power traces determine the rank of a
finite free module carrying an endomorphism with nonzero determinant. -/
theorem finrank_eq_of_trace_pow_eq_of_det_ne_zero (hf : f.det ≠ 0) (hg : g.det ≠ 0)
    (h : ∀ j, 0 < j → trace R M (f ^ j) = trace R N (g ^ j)) :
    Module.finrank R M = Module.finrank R N := by
  have : Nontrivial R := ⟨⟨f.det, 0, hf⟩⟩
  let b := Module.Free.chooseBasis R M
  let c := Module.Free.chooseBasis R N
  rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis c]
  apply Matrix.card_eq_of_trace_pow_eq_of_det_ne_zero
    (A := toMatrix b b f) (B := toMatrix c c g)
  · rwa [det_toMatrix]
  · rwa [det_toMatrix]
  · intro j hj
    simpa only [toMatrix_pow, ← trace_eq_matrix_trace] using h j hj

/-- Over an additively torsion-free ring, endomorphisms with nonzero determinants and the same
positive power traces have the same characteristic polynomial, even on different modules. -/
theorem charpoly_eq_of_trace_pow_eq_of_det_ne_zero (hf : f.det ≠ 0) (hg : g.det ≠ 0)
    (h : ∀ j, 0 < j → trace R M (f ^ j) = trace R N (g ^ j)) : f.charpoly = g.charpoly := by
  apply charpoly_eq_of_trace_pow_eq (finrank_eq_of_trace_pow_eq_of_det_ne_zero hf hg h)
  exact fun j hj _ ↦ h j hj

end LinearMap

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Matrix.MvPolynomial
public import TauCeti.LinearAlgebra.Matrix.Rank
public import TauCeti.Topology.Algebra.MvPolynomial.ZeroLocus

/-!
# Rank bounds are closed conditions

For a matrix `Z` and `r : ℕ`, the condition `rank Z ≤ r` says that every `(r + 1) × (r + 1)` minor
of `Z` vanishes (`Matrix.rank_le_iff_forall_det_submatrix_eq_zero`). Each such minor is a
polynomial in the entries of `Z`, with integer coefficients, and so is each minor of a power
`Z ^ j` of a square matrix. Hence the conditions `rank Z ≤ r` and `rank (Z ^ j) ≤ r` are Zariski
closed: they pass from a set of matrices to every point of the zero locus of the polynomials
vanishing on that set. Over a field with continuous ring operations and closed points, such as
`ℂ`, they are also closed in the usual topology. The Zariski closure is expressed through
Mathlib's `MvPolynomial.zeroLocus` and `MvPolynomial.vanishingIdeal`.

## Main results

* `Matrix.rank_le_of_mem_zeroLocus_vanishingIdeal` and
  `Matrix.rank_pow_le_of_mem_zeroLocus_vanishingIdeal`: a bound on the rank of a matrix, or of its
  `j`-th power, holding on a set of matrices holds on its Zariski closure.
* `Matrix.isClosed_setOfPred_rank_le` and `Matrix.isClosed_setOfPred_rank_pow_le`: the matrices of
  rank at most `r`, and the square matrices `Z` with `rank (Z ^ j) ≤ r`, form closed sets.
-/

public section

open MvPolynomial

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section Zariski

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

omit [DecidableEq n] in
/-- **Rank bounds are Zariski closed.** If `rank Z ≤ r` for every matrix `Z` of a set `S`, then
`rank Y ≤ r` for every `Y` on which all polynomials vanishing on `S` vanish. -/
theorem rank_le_of_mem_zeroLocus_vanishingIdeal {m : Type*} [Finite m] {S : Set (Matrix m n K)}
    {r : ℕ} (hS : ∀ Z ∈ S, Z.rank ≤ r) {Y : Matrix m n K}
    (hY : Function.uncurry Y ∈ zeroLocus K (vanishingIdeal k (Function.uncurry '' S))) :
    Y.rank ≤ r := by
  rw [rank_le_iff_forall_det_submatrix_eq_zero]
  intro a b
  -- The minor of `Y` at `(a, b)` is the value at `Y` of a polynomial vanishing on `S`.
  rw [← aeval_det_submatrix_mvPolynomialX (R := k)]
  refine mem_zeroLocus_iff.1 hY _ (mem_vanishingIdeal_iff.2 ?_)
  -- The image under `Function.uncurry` sees `Z` as a function, so it is retyped as a matrix.
  rintro - ⟨Z, hZ, rfl⟩
  exact (aeval_det_submatrix_mvPolynomialX (Z : Matrix m n K) a b).trans
    (rank_le_iff_forall_det_submatrix_eq_zero.1 (hS Z hZ) a b)

/-- **Rank bounds are Zariski closed.** If `rank (Z ^ j) ≤ r` for every matrix `Z` of a set `S`,
then `rank (Y ^ j) ≤ r` for every `Y` on which all polynomials vanishing on `S` vanish. -/
theorem rank_pow_le_of_mem_zeroLocus_vanishingIdeal {S : Set (Matrix n n K)} {j r : ℕ}
    (hS : ∀ Z ∈ S, (Z ^ j).rank ≤ r) {Y : Matrix n n K}
    (hY : Function.uncurry Y ∈ zeroLocus K (vanishingIdeal k (Function.uncurry '' S))) :
    (Y ^ j).rank ≤ r := by
  rw [rank_le_iff_forall_det_submatrix_eq_zero]
  intro a b
  -- The minor of `Y ^ j` at `(a, b)` is the value at `Y` of a polynomial vanishing on `S`.
  rw [← aeval_det_submatrix_pow_mvPolynomialX (R := k)]
  refine mem_zeroLocus_iff.1 hY _ (mem_vanishingIdeal_iff.2 ?_)
  -- The image under `Function.uncurry` sees `Z` as a function, so it is retyped as a matrix.
  rintro - ⟨Z, hZ, rfl⟩
  exact (aeval_det_submatrix_pow_mvPolynomialX (Z : Matrix n n K) j a b).trans
    (rank_le_iff_forall_det_submatrix_eq_zero.1 (hS Z hZ) a b)

end Zariski

section Topological

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T1Space K]

omit [DecidableEq n] in
/-- Over a field with continuous ring operations and closed points, the matrices of rank at most
`r` form a closed set. -/
theorem isClosed_setOfPred_rank_le {m : Type*} [Finite m] (r : ℕ) :
    IsClosed {A : Matrix m n K | A.rank ≤ r} := by
  refine isClosed_of_closure_subset fun Y hY ↦ rank_le_of_mem_zeroLocus_vanishingIdeal
    (k := K) (S := {A : Matrix m n K | A.rank ≤ r}) (fun _ hA ↦ hA)
    (closure_subset_zeroLocus_vanishingIdeal _ ?_)
  have huncurry : Continuous (Function.uncurry : Matrix m n K → m × n → K) :=
    continuous_pi fun p ↦ continuous_id.matrix_elem p.1 p.2
  exact mem_closure_image huncurry.continuousAt hY

/-- Over a field with continuous ring operations and closed points, the matrices `Z` with
`rank (Z ^ j) ≤ r` form a closed set. -/
theorem isClosed_setOfPred_rank_pow_le (j r : ℕ) :
    IsClosed {Z : Matrix n n K | (Z ^ j).rank ≤ r} :=
  (isClosed_setOfPred_rank_le r).preimage (continuous_pow j)

end Topological

end Matrix

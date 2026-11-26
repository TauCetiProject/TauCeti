/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.MatlisDual

/-!
# Maximal minors and kernel lengths over discrete valuation rings

Let `A` be a matrix over a discrete valuation ring `O` with columns indexed by a finite type `k`,
and let `a ≠ 0` in `O`. The length of the kernel of `A` acting on `(O ⧸ Ideal.span {a}) ^ k`
equals the least additive valuation of a maximal minor of the matrix formed by stacking the rows
of `A` and of `a • 1`.

The proof has two steps:
1. The kernel of `A` on `(O ⧸ Ideal.span {a}) ^ k` is the orthogonal of `A.rowLattice a`, hence
   isomorphic via `Submodule.orthogonalPiEquiv` to
   `Hom_O((k → O) ⧸ A.rowLattice a, O ⧸ Ideal.span {a})`. Since `(k → O) ⧸ A.rowLattice a` is
   annihilated by `a ≠ 0`, `IsDiscreteValuationRing.length_linearMap_quotient_span_singleton_right`
   shows this Hom module has the same length as `(k → O) ⧸ A.rowLattice a`.
2. For any matrix `M : Matrix ι k O` with `Nonempty (k → ι)`, the quotient
   `(k → O) ⧸ Submodule.span O (Set.range M.row)` has length equal to the least valuation of a
   maximal minor `(M.submatrix f id).det` (`Matrix.isLeast_length_quotient_span_range_row`): every
   choice of `k` rows spans a sublattice whose colength is the valuation of the corresponding minor
   (`Matrix.length_quotient_span_range_eq_addVal_det`), while if the quotient has finite length
   the row submodule is spanned by the rows of a square matrix
   (`IsDiscreteValuationRing.exists_matrix_span_range_row_eq`) whose determinant is divisible by
   any common divisor of those minors (`Matrix.dvd_det_of_forall_row_mem_span`).

The general matrix definitions and the kernel/Hom length identity live in
`TauCeti.LinearAlgebra.Matrix.RowLattice`; the general row-span colength theorem lives in
`TauCeti.RingTheory.DiscreteValuationRing.Length`.

## Main results

* `Matrix.isLeast_length_quotient_rowLattice`: specialization to `M = A.fromRows (a • 1)`.
* `Matrix.isLeast_length_ker`: for a ring homomorphism `ev : Λ →+* O` into a discrete
  valuation ring with `ev a ≠ 0`, the length of `(A.map ev).ker (O ⧸ Ideal.span {ev a})`
  is the least `addVal O (ev P)` for `P ∈ A.rowLatticeMinors a`.

## References

* N. Bourbaki, *Algebra*, Chapter VII, §4 (Elementary divisors).
* S. Lang, *Algebra*, Chapter III, §7 (Modules over principal ideal domains).
* Adapted from `grh-lean`, `src/Lib/General/Algebra/SharpMinors.lean`
  (Copyright 2026 Anthropic, PBC, Apache 2.0).
-/

public section

noncomputable section

open Matrix Module Submodule IsDiscreteValuationRing

namespace Matrix

section DVR

variable {Λ O r k : Type*} [CommRing Λ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Fintype k] [DecidableEq k]

/-- Over a discrete valuation ring `O`, the quotient of `k → O` by `A.rowLattice a` has length
equal to the least valuation of a maximal minor in `A.rowLatticeMinors a`. -/
theorem isLeast_length_quotient_rowLattice (A : Matrix r k O) (a : O) :
    IsLeast (addVal O '' A.rowLatticeMinors a) (length O ((k → O) ⧸ A.rowLattice a)) := by
  have : Nonempty (k → r ⊕ k) := ⟨.inr⟩
  rw [rowLatticeMinors_eq_range, rowLattice_eq_span]
  exact isLeast_length_quotient_span_range_row (A.fromRows (a • (1 : Matrix k k O)))

/-- For a matrix `A` over a commutative ring `Λ` with columns indexed by a finite type `k`, and a
ring homomorphism `ev : Λ →+* O` into a discrete valuation ring with `ev a ≠ 0`, the length of
`(A.map ev).ker (O ⧸ Ideal.span {ev a})` is the least `addVal O (ev P)` as `P` ranges
over `A.rowLatticeMinors a`. -/
theorem isLeast_length_ker (A : Matrix r k Λ) (a : Λ) (ev : Λ →+* O) (ha : ev a ≠ 0) :
    IsLeast ((fun P : Λ ↦ addVal O (ev P)) '' A.rowLatticeMinors a)
      (length O ((A.map ev).ker (O ⧸ Ideal.span {ev a}))) := by
  have h_kill (x : (k → O) ⧸ (A.map ev).rowLattice (ev a)) : ev a • x = 0 := by
    obtain ⟨v, rfl⟩ := mkQ_surjective _ x
    rw [← map_smul, mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact (A.map ev).smul_mem_rowLattice (ev a) v
  rw [length_ker_eq_length_linearMap,
    length_linearMap_quotient_span_singleton_right ha h_kill,
    ← Set.image_image (addVal O) ev, image_rowLatticeMinors]
  exact (A.map ev).isLeast_length_quotient_rowLattice (ev a)

end DVR

end Matrix

end

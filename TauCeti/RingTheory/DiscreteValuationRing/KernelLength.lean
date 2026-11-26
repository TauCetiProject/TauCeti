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
   annihilated by `a ≠ 0`, `IsDiscreteValuationRing.quotientEquivTorsionBySet` identifies this Hom
   module with `Hom_O((k → O) ⧸ A.rowLattice a, K/O)`, whose length equals the colength of
   `A.rowLattice a` by Matlis duality (`length_linearMap_fractionRing_quotient`).
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
* `Matrix.isLeast_length_matrixKernel`: for a ring homomorphism `ev : Λ →+* O` into a discrete
  valuation ring with `ev a ≠ 0`, the length of `(A.map ev).matrixKernel (O ⧸ Ideal.span {ev a})`
  is the least `addVal O (ev P)` for `P ∈ A.maximalMinors a`.

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
equal to the least valuation of a maximal minor in `A.maximalMinors a`. -/
theorem isLeast_length_quotient_rowLattice (A : Matrix r k O) (a : O) :
    IsLeast (addVal O '' A.maximalMinors a) (length O ((k → O) ⧸ A.rowLattice a)) := by
  have : Nonempty (k → r ⊕ k) := ⟨.inr⟩
  have hmin : A.maximalMinors a =
      Set.range (fun f : k → r ⊕ k ↦ ((A.fromRows (a • 1)).submatrix f id).det) :=
    Set.ext fun _ ↦ mem_maximalMinors_iff
  rw [hmin, rowLattice_eq_span]
  exact isLeast_length_quotient_span_range_row (A.fromRows (a • (1 : Matrix k k O)))

/-- For a matrix `A` over a commutative ring `Λ` with columns indexed by a finite type `k`, and a
ring homomorphism `ev : Λ →+* O` into a discrete valuation ring with `ev a ≠ 0`, the length of
`(A.map ev).matrixKernel (O ⧸ Ideal.span {ev a})` is the least `addVal O (ev P)` as `P` ranges
over `A.maximalMinors a`. -/
theorem isLeast_length_matrixKernel (A : Matrix r k Λ) (a : Λ) (ev : Λ →+* O) (ha : ev a ≠ 0) :
    IsLeast ((fun P : Λ ↦ addVal O (ev P)) '' A.maximalMinors a)
      (length O ((A.map ev).matrixKernel (O ⧸ Ideal.span {ev a}))) := by
  let Q := (k → O) ⧸ (A.map ev).rowLattice (ev a)
  let K := FractionRing O
  let KO := K ⧸ LinearMap.range (Algebra.linearMap O K)
  have h_kill (x : Q) : ev a • x = 0 := by
    obtain ⟨v, rfl⟩ := mkQ_surjective _ x
    rw [← map_smul, mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact (A.map ev).smul_mem_rowLattice (ev a) v
  let e₁ := IsDiscreteValuationRing.quotientEquivTorsionBySet (K := K) ha
  let eHom : (Q →ₗ[O] O ⧸ Ideal.span {ev a}) ≃ₗ[O] (Q →ₗ[O] KO) :=
    (LinearEquiv.congrRight e₁).trans
    { toFun := fun φ ↦ (Submodule.subtype _).comp φ
      map_add' := fun _ _ ↦ by ext; simp
      map_smul' := fun _ _ ↦ by ext; simp
      invFun := fun ψ ↦ ψ.codRestrict _ fun x ↦ by
        rw [Submodule.torsionBySet_span_singleton_eq, Submodule.mem_torsionBy_iff, ← map_smul,
          h_kill, map_zero]
      left_inv := fun φ ↦ by ext; rfl
      right_inv := fun ψ ↦ by ext x; simp }
  rw [length_matrixKernel_eq_length_linearMap, eHom.length_eq,
    IsDiscreteValuationRing.length_linearMap_fractionRing_quotient (K := K),
    ← Set.image_image (addVal O) ev, image_maximalMinors]
  exact (A.map ev).isLeast_length_quotient_rowLattice (ev a)

end DVR

end Matrix

end

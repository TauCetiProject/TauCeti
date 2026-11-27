/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Length
public import TauCeti.LinearAlgebra.Matrix.ColumnRowPartitioned
public import TauCeti.LinearAlgebra.Pi.Orthogonal

/-!
# Row lattices, maximal minors, and matrix kernels

For a matrix `A` over a commutative semiring, `Matrix.rowLattice A a` is the span of the rows of
`A` together with the rows of `a • 1`. Its generators characterize containment in a submodule.
`Matrix.ker A B` consists of the vectors in `k → B` annihilated by every row of `A`.

Over a commutative ring, `Matrix.rowLatticeMinors A a` records the determinants of all full-column
row selections from `A.fromRows (a • 1)`. In contrast,
`TauCeti.LinearAlgebra.Matrix.MaximalMinor` treats full-row minors selected by column embeddings.

The kernel on `(O ⧸ Ideal.span {a}) ^ k` has the same length as the linear maps from the quotient
by `A.rowLattice a` to `O ⧸ Ideal.span {a}` (`Matrix.length_ker_eq_length_linearMap`).
This relates systems of linear equations modulo `a` to row-span colengths; the valuation formula
for these lengths is developed in `TauCeti.RingTheory.DiscreteValuationRing.KernelLength`.

## References

* Adapted from `grh-lean`, `src/Lib/General/Algebra/SharpMinors.lean`
  (Copyright 2026 Anthropic, PBC, Apache 2.0).
-/

public section

open Module Submodule

namespace Matrix

section CommSemiring

variable {O r k : Type*} [CommSemiring O] [Fintype k]

/-- The kernel of `A` on `k → B`, for an `O`-module `B`: the vectors `w` such that
`∑ j, A i j • w j = 0` for every row index `i`. -/
def ker (A : Matrix r k O) (B : Type*) [AddCommMonoid B] [Module O B] :
    Submodule O (k → B) :=
  ⨅ i : r, LinearMap.ker (∑ j : k, A i j • LinearMap.proj j : (k → B) →ₗ[O] B)

/-- A vector lies in `A.ker B` exactly when every row of `A` sends it to `0`. -/
@[simp]
theorem mem_ker {A : Matrix r k O} {B : Type*} [AddCommMonoid B] [Module O B]
    {w : k → B} :
    w ∈ A.ker B ↔ ∀ i : r, ∑ j : k, A i j • w j = 0 := by
  simp [ker]

/-- The kernel of a matrix on `k → B` is the orthogonal of its row span under the pairing
`⟨v, w⟩ = ∑ j, v j • w j`. -/
theorem ker_eq_orthogonalBilin (A : Matrix r k O) (B : Type*)
    [AddCommMonoid B] [Module O B] :
    A.ker B =
      (span O (Set.range A.row)).orthogonalBilin (Fintype.bilinearCombination O O).flip := by
  ext w
  rw [mem_ker, Submodule.mem_orthogonalBilin_span, Set.forall_mem_range]
  simp [Fintype.linearCombination_apply]

/-- The submodule of `k → O` spanned by the rows of `A` and of `a • 1`. -/
def rowLattice [DecidableEq k] (A : Matrix r k O) (a : O) : Submodule O (k → O) :=
  span O (Set.range (A.fromRows (a • (1 : Matrix k k O))).row)

omit [Fintype k] in
/-- The row lattice is the span of the rows of `A.fromRows (a • 1)`. -/
theorem rowLattice_eq_span [DecidableEq k] (A : Matrix r k O) (a : O) :
    A.rowLattice a = span O (Set.range (A.fromRows (a • (1 : Matrix k k O))).row) :=
  (rfl)

omit [Fintype k] in
/-- Every row of `A` lies in `A.rowLattice a`. -/
theorem row_mem_rowLattice [DecidableEq k] (A : Matrix r k O) (a : O) (i : r) :
    A.row i ∈ A.rowLattice a :=
  subset_span ⟨.inl i, rfl⟩

omit [Fintype k] in
/-- Every `a`-scaled standard basis vector lies in `A.rowLattice a`. -/
theorem smul_single_mem_rowLattice [DecidableEq k] (A : Matrix r k O) (a : O) (j : k) :
    a • Pi.single j (1 : O) ∈ A.rowLattice a :=
  subset_span ⟨.inr j, A.row_fromRows_smul_one_inr a j⟩

omit [Fintype k] in
/-- `A.rowLattice a` is contained in a submodule `N` if and only if `N` contains every row of `A`
and every `a`-scaled standard basis vector. -/
theorem rowLattice_le_iff [DecidableEq k] {A : Matrix r k O} {a : O} {N : Submodule O (k → O)} :
    A.rowLattice a ≤ N ↔ (∀ i : r, A.row i ∈ N) ∧ ∀ j : k, a • Pi.single j (1 : O) ∈ N := by
  refine ⟨fun h ↦ ⟨fun i ↦ h (A.row_mem_rowLattice a i),
      fun j ↦ h (A.smul_single_mem_rowLattice a j)⟩, fun ⟨hA, ha⟩ ↦ span_le.2 ?_⟩
  rintro _ ⟨i | j, rfl⟩
  · exact hA i
  · simpa only [row_fromRows_smul_one_inr, SetLike.mem_coe] using ha j

omit [Fintype k] in
/-- Every multiple of `a` lies in `A.rowLattice a`. -/
theorem smul_mem_rowLattice [Finite k] [DecidableEq k] (A : Matrix r k O) (a : O) (v : k → O) :
    a • v ∈ A.rowLattice a := by
  have := Fintype.ofFinite k
  rw [pi_eq_sum_univ' v, Finset.smul_sum]
  refine sum_mem fun j _ ↦ ?_
  rw [smul_comm]
  exact smul_mem _ _ (A.smul_single_mem_rowLattice a j)

end CommSemiring

section CommRing

variable {Λ O r k : Type*} [CommRing Λ] [CommRing O] [Fintype k] [DecidableEq k]

/-- The minors of size `card k` of the matrix formed by the rows of `A` and of `a • 1`, where `k`
indexes the columns. The family of rows of `A` may be infinite. A choice of rows with a repetition
is allowed; it contributes the minor `0`. -/
def rowLatticeMinors (A : Matrix r k Λ) (a : Λ) : Set Λ :=
  Set.range fun f : k → r ⊕ k ↦ ((A.fromRows (a • 1)).submatrix f id).det

/-- The row-lattice minors are the determinants of all full-column row selections from
`A.fromRows (a • 1)`. -/
theorem rowLatticeMinors_eq_range (A : Matrix r k Λ) (a : Λ) :
    A.rowLatticeMinors a =
      Set.range (fun f : k → r ⊕ k ↦ ((A.fromRows (a • 1)).submatrix f id).det) :=
  (rfl)

/-- An element lies in `A.rowLatticeMinors a` exactly when it is the determinant of a `card k`-row
selection from `A.fromRows (a • 1)`. -/
@[simp]
theorem mem_rowLatticeMinors_iff {A : Matrix r k Λ} {a x : Λ} :
    x ∈ A.rowLatticeMinors a ↔ ∃ f : k → r ⊕ k, ((A.fromRows (a • 1)).submatrix f id).det = x :=
  Iff.rfl

/-- A ring homomorphism `ev` maps the maximal minors of the rows of `A` and `a • 1` onto those of
the rows of `A.map ev` and `ev a • 1`. -/
theorem image_rowLatticeMinors (A : Matrix r k Λ) (a : Λ) (ev : Λ →+* O) :
    ev '' A.rowLatticeMinors a = (A.map ev).rowLatticeMinors (ev a) := by
  have h_map : (A.fromRows (a • (1 : Matrix k k Λ))).map ev = (A.map ev).fromRows (ev a • 1) := by
    ext (i | i) j <;> simp [Matrix.one_apply, apply_ite ev]
  simp [rowLatticeMinors, ← Set.range_comp, Function.comp_def, ev.map_det, ← h_map, submatrix_map]

/-- The kernel of `A` on `(O ⧸ Ideal.span {a}) ^ k` has the length of the module of `O`-linear maps
from `(k → O) ⧸ A.rowLattice a` to `O ⧸ Ideal.span {a}`, since it is the orthogonal of
`A.rowLattice a`. -/
theorem length_ker_eq_length_linearMap (A : Matrix r k O) (a : O) :
    length O (A.ker (O ⧸ Ideal.span {a})) =
      length O (((k → O) ⧸ A.rowLattice a) →ₗ[O] O ⧸ Ideal.span {a}) := by
  have h_orth : A.ker (O ⧸ Ideal.span {a}) =
      (A.rowLattice a).orthogonalBilin (Fintype.bilinearCombination O O).flip := by
    rw [rowLattice_eq_span, ← ker_eq_orthogonalBilin]
    ext w
    simp only [mem_ker, Sum.forall, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, Matrix.smul_apply, smul_eq_mul]
    refine ⟨fun h ↦ ⟨h, fun i ↦ Finset.sum_eq_zero fun j _ ↦ ?_⟩, And.left⟩
    simp [Algebra.smul_def, (Ideal.Quotient.eq_zero_iff_dvd a _).2 (dvd_mul_right a _)]
  rw [h_orth, (Submodule.orthogonalPiEquiv (O ⧸ Ideal.span {a}) (A.rowLattice a)).length_eq]

end CommRing

end Matrix

end

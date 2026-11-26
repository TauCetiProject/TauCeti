/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Length
import TauCeti.LinearAlgebra.Matrix.Determinant.IdealDivisibility
import TauCeti.LinearAlgebra.Pi.Orthogonal
import TauCeti.RingTheory.DiscreteValuationRing.Length
import TauCeti.RingTheory.Length.LinearMap

/-!
# Maximal minors and kernel lengths over discrete valuation rings

Let `A` be a matrix over a discrete valuation ring `O` with columns indexed by a finite type `k`,
and let `a ≠ 0` in `O`. The length of the kernel of `A` acting on `(O ⧸ Ideal.span {a}) ^ k`
equals the least additive valuation of a maximal minor of the matrix formed by stacking the rows
of `A` and of `a • 1`.

The proof has two steps:
1. The kernel of `A` on `(O ⧸ Ideal.span {a}) ^ k` is the orthogonal of `A.rowLattice a`, hence
   isomorphic via `Submodule.orthogonalPiEquiv` to the module of `O`-linear maps from
   `(k → O) ⧸ A.rowLattice a` to `O ⧸ Ideal.span {a}`. Over a principal ideal domain, any finitely
   generated module annihilated by `a ≠ 0` has the same length as its module of linear maps into
   `O ⧸ Ideal.span {a}` (`TauCeti.length_linearMap_quotient_span`).
2. The quotient `(k → O) ⧸ A.rowLattice a` has length equal to the least valuation of a maximal
   minor of `A.fromRows (a • 1)` (for any `a : O`, including `a = 0`): every choice of `k` rows
   spans a sublattice whose colength is the valuation of the corresponding minor
   (`Matrix.length_quotient_span_range_eq_addVal_det`), while if `A.rowLattice a` has finite
   colength it is spanned by the rows of a square matrix
   (`IsDiscreteValuationRing.exists_matrix_span_range_row_eq`) whose determinant is divisible by
   any common divisor of those minors (`Matrix.dvd_det_of_forall_row_mem_span`).

## Main definitions and results

* `Matrix.maximalMinors`: the set of `card k`-by-`card k` minors of `A.fromRows (a • 1)`.
* `Matrix.matrixKernel`: the kernel of `A` acting on `k → B`.
* `Matrix.rowLattice`: the submodule of `k → O` spanned by the rows of `A` and `a • 1`.
* `Matrix.isLeast_length_quotient_rowLattice`: the length of `(k → O) ⧸ A.rowLattice a` is the
  least valuation of a maximal minor in `A.maximalMinors a`.
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

section CommSemiring

variable {O r k : Type*} [CommSemiring O] [Fintype k]

/-- The kernel of `A` on `k → B`, for an `O`-module `B`: the vectors `w` such that
`∑ j, A i j • w j = 0` for every row index `i`. -/
def matrixKernel (A : Matrix r k O) (B : Type*) [AddCommMonoid B] [Module O B] :
    Submodule O (k → B) :=
  ⨅ i : r, LinearMap.ker (∑ j : k, A i j • LinearMap.proj j : (k → B) →ₗ[O] B)

/-- A vector lies in `A.matrixKernel B` exactly when every row of `A` sends it to `0`. -/
@[simp]
theorem mem_matrixKernel {A : Matrix r k O} {B : Type*} [AddCommMonoid B] [Module O B]
    {w : k → B} :
    w ∈ A.matrixKernel B ↔ ∀ i : r, ∑ j : k, A i j • w j = 0 := by
  simp [matrixKernel]

/-- The submodule of `k → O` spanned by the rows of `A` and of `a • 1`. -/
def rowLattice [DecidableEq k] (A : Matrix r k O) (a : O) : Submodule O (k → O) :=
  span O (Set.range (A.fromRows (a • (1 : Matrix k k O))).row)

omit [Fintype k] in
/-- Every row of `A` lies in `A.rowLattice a`. -/
theorem row_mem_rowLattice [DecidableEq k] (A : Matrix r k O) (a : O) (i : r) :
    A.row i ∈ A.rowLattice a :=
  subset_span ⟨.inl i, rfl⟩

omit [Fintype k] in
/-- Every `a`-scaled standard basis vector lies in `A.rowLattice a`. -/
theorem smul_single_mem_rowLattice [DecidableEq k] (A : Matrix r k O) (a : O) (j : k) :
    a • Pi.single j (1 : O) ∈ A.rowLattice a :=
  subset_span ⟨.inr j, by ext i; simp [Matrix.one_apply, Pi.single_apply, eq_comm]⟩

omit [Fintype k] in
/-- `A.rowLattice a` is contained in a submodule `N` if and only if `N` contains every row of `A`
and every `a`-scaled standard basis vector. -/
theorem rowLattice_le_iff [DecidableEq k] {A : Matrix r k O} {a : O} {N : Submodule O (k → O)} :
    A.rowLattice a ≤ N ↔ (∀ i : r, A.row i ∈ N) ∧ ∀ j : k, a • Pi.single j (1 : O) ∈ N := by
  refine ⟨fun h ↦ ⟨fun i ↦ h (A.row_mem_rowLattice a i),
      fun j ↦ h (A.smul_single_mem_rowLattice a j)⟩, fun ⟨hA, ha⟩ ↦ span_le.2 ?_⟩
  rintro _ ⟨i | j, rfl⟩
  · exact hA i
  · have h : (A.fromRows (a • (1 : Matrix k k O))).row (.inr j) = a • Pi.single j (1 : O) := by
      ext i; simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    simpa [h] using ha j

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
def maximalMinors (A : Matrix r k Λ) (a : Λ) : Set Λ :=
  Set.range fun f : k → r ⊕ k ↦ ((A.fromRows (a • 1)).submatrix f id).det

/-- An element lies in `A.maximalMinors a` exactly when it is the determinant of a `card k`-row
selection from `A.fromRows (a • 1)`. -/
@[simp]
theorem mem_maximalMinors_iff {A : Matrix r k Λ} {a x : Λ} :
    x ∈ A.maximalMinors a ↔ ∃ f : k → r ⊕ k, ((A.fromRows (a • 1)).submatrix f id).det = x :=
  Iff.rfl

/-- A ring homomorphism `ev` maps the maximal minors of the rows of `A` and `a • 1` onto those of
the rows of `A.map ev` and `ev a • 1`. -/
theorem image_maximalMinors (A : Matrix r k Λ) (a : Λ) (ev : Λ →+* O) :
    ev '' A.maximalMinors a = (A.map ev).maximalMinors (ev a) := by
  have h_map : (A.fromRows (a • (1 : Matrix k k Λ))).map ev = (A.map ev).fromRows (ev a • 1) := by
    ext (i | i) j <;> simp [Matrix.one_apply, apply_ite ev]
  simp [maximalMinors, ← Set.range_comp, Function.comp_def, ev.map_det, ← h_map, submatrix_map]

/-- The kernel of `A` on `(O ⧸ Ideal.span {a}) ^ k` has the length of the module of `O`-linear maps
from `(k → O) ⧸ A.rowLattice a` to `O ⧸ Ideal.span {a}`, since it is the orthogonal of
`A.rowLattice a`. -/
theorem length_matrixKernel_eq_length_linearMap (A : Matrix r k O) (a : O) :
    length O (A.matrixKernel (O ⧸ Ideal.span {a})) =
      length O (((k → O) ⧸ A.rowLattice a) →ₗ[O] O ⧸ Ideal.span {a}) := by
  have h_orth : A.matrixKernel (O ⧸ Ideal.span {a}) =
      (A.rowLattice a).orthogonalBilin (Fintype.bilinearCombination O O).flip := by
    ext w
    rw [mem_matrixKernel, rowLattice, Submodule.mem_orthogonalBilin_span, Set.forall_mem_range]
    simp only [LinearMap.flip_apply, Fintype.bilinearCombination_apply,
      Fintype.linearCombination_apply, Sum.forall, Matrix.row_apply, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, Matrix.smul_apply, smul_eq_mul]
    refine ⟨fun h ↦ ⟨h, fun i ↦ Finset.sum_eq_zero fun j _ ↦ ?_⟩, And.left⟩
    simp [Algebra.smul_def, (Ideal.Quotient.eq_zero_iff_dvd a _).2 (dvd_mul_right a _)]
  rw [h_orth, (Submodule.orthogonalPiEquiv (O ⧸ Ideal.span {a}) (A.rowLattice a)).length_eq]

end CommRing

section DVR

variable {Λ O r k : Type*} [CommRing Λ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Fintype k] [DecidableEq k]

/-- Over a discrete valuation ring `O`, the quotient of `k → O` by `A.rowLattice a` has length
equal to the least valuation of a maximal minor in `A.maximalMinors a`. -/
theorem isLeast_length_quotient_rowLattice (A : Matrix r k O) (a : O) :
    IsLeast (addVal O '' A.maximalMinors a) (length O ((k → O) ⧸ A.rowLattice a)) := by
  let M : Matrix (r ⊕ k) k O := A.fromRows (a • 1)
  let v (f : k → r ⊕ k) : ℕ∞ := addVal O (M.submatrix f id).det
  have h_lower (f : k → r ⊕ k) : length O ((k → O) ⧸ A.rowLattice a) ≤ v f := by
    have h_le : span O (Set.range (M.submatrix f id).row) ≤ A.rowLattice a :=
      span_mono (Set.range_comp_subset_range f M.row)
    simpa only [length_quotient_span_range_eq_addVal_det] using
      length_le_of_surjective _ (factor_surjective h_le)
  refine ⟨?_, Set.forall_mem_image.2 (Set.forall_mem_range.2 h_lower)⟩
  rcases eq_or_ne (length O ((k → O) ⧸ A.rowLattice a)) ⊤ with h_top | h_fin
  · exact ⟨(M.submatrix .inr id).det, ⟨.inr, rfl⟩,
      (top_le_iff.1 (h_top ▸ h_lower .inr)).trans h_top.symm⟩
  · obtain ⟨N, hN⟩ := IsDiscreteValuationRing.exists_matrix_span_range_row_eq _ h_fin
    have : Nonempty (k → r ⊕ k) := ⟨.inr⟩
    let f₀ : k → r ⊕ k := Function.argmin v
    have h_dvd : (M.submatrix f₀ id).det ∣ N.det :=
      dvd_det_of_forall_row_mem_span
        (fun f ↦ addVal_le_iff_dvd.1 (Function.argmin_le v f))
        fun i ↦ hN.le (subset_span ⟨i, rfl⟩)
    have h_upper : v f₀ ≤ length O ((k → O) ⧸ A.rowLattice a) :=
      (addVal_le_iff_dvd.2 h_dvd).trans_eq (by rw [← hN, length_quotient_span_range_eq_addVal_det])
    exact ⟨(M.submatrix f₀ id).det, ⟨f₀, rfl⟩, h_upper.antisymm (h_lower f₀)⟩

/-- For a matrix `A` over a commutative ring `Λ` with columns indexed by a finite type `k`, and a
ring homomorphism `ev : Λ →+* O` into a discrete valuation ring with `ev a ≠ 0`, the length of
`(A.map ev).matrixKernel (O ⧸ Ideal.span {ev a})` is the least `addVal O (ev P)` as `P` ranges
over `A.maximalMinors a`. -/
theorem isLeast_length_matrixKernel (A : Matrix r k Λ) (a : Λ) (ev : Λ →+* O) (ha : ev a ≠ 0) :
    IsLeast ((fun P : Λ ↦ addVal O (ev P)) '' A.maximalMinors a)
      (length O ((A.map ev).matrixKernel (O ⧸ Ideal.span {ev a}))) := by
  have h_kill (x : (k → O) ⧸ (A.map ev).rowLattice (ev a)) : ev a • x = 0 := by
    obtain ⟨v, rfl⟩ := mkQ_surjective _ x
    simpa [← Quotient.mk_smul] using (A.map ev).smul_mem_rowLattice (ev a) v
  rw [length_matrixKernel_eq_length_linearMap, TauCeti.length_linearMap_quotient_span ha h_kill,
    ← Set.image_image (addVal O) ev, image_maximalMinors]
  exact (A.map ev).isLeast_length_quotient_rowLattice (ev a)

end DVR

end Matrix

end

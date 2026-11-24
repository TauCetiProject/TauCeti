/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.BilinearForm.Dual.Basis
import TauCeti.LinearAlgebra.BilinearForm.LinearIndependent
import TauCeti.LinearAlgebra.Matrix.Adjugate.Basic
import TauCeti.LinearAlgebra.Matrix.Symmetric

/-!
# Bilinear forms attached to matrices

Mathlib's `Matrix.toBilin'` reads a square matrix `M` over a commutative semiring `R` as the
bilinear form `(x, y) ↦ xᵀ M y` on `n → R`. This file records facts about these forms that
Mathlib lacks. The identity matrix gives the standard form `∑ i, x i * y i`, which takes the value
`1` on every standard basis vector, so over a nontrivial `R` it is alternating only when the index
type is empty (over the trivial semiring `1 = 0` and every form is alternating). Since the identity
matrix is symmetric and invertible, the standard form over a nontrivial `R` is in every positive
dimension a nondegenerate symmetric form that is not alternating, the model for the orthonormal
normal form of such forms.

In the other direction, `LinearMap.BilinForm.toMatrix` reads a bilinear form in a basis as its
Gram matrix. For a nondegenerate form, the Gram matrix in the `B`-dual basis is the inverse
transpose of the Gram matrix in the original basis; for a symmetric form it is the inverse Gram
matrix, which is how the dual of a lattice is described in coordinates. The `B`-dual basis itself
is obtained from the original basis by the inverse Gram matrix. Likewise, the
coordinates of a vector are recovered from its pairings with the basis vectors through the inverse
Gram matrix.

The Gram matrix of a family of vectors that is not a basis is used in the same way. A family whose
Gram matrix is `c` times a matrix of unit determinant, for a non-zero-divisor `c`, is a basis of
its span. An isometry `Matrix.toBilin' G ≅ Matrix.toBilin' G'` turns a family with Gram matrix `G`
into one with Gram matrix `G'` and the same span, and the Gram determinant of the span of two
orthogonal such families is determined up to squares by their Gram matrices.

Gram determinants transform by the square of the coordinate-map determinant, and reindexing a
basis does not change them. Consequently, the Gram determinants of equivalent bilinear forms, in
any finite bases, differ by the square of a unit and their product is a square, without symmetry
or nondegeneracy assumptions. A linear map that carries one symmetric form to another only modulo
`a * r`, with `2 ∣ r`, still relates the two Gram determinants: a square times the determinant
of the target form equals a factor in `1 + 2rR` times the determinant of the source form,
provided the source form has a Gram matrix `G` with a partner `H` satisfying `G * H = a • 1` and a
parity condition holds.

Pullback along a rectangular matrix preserves alternation over a commutative semiring. Over a
commutative ring, alternation is equivalent to skew-symmetry together with a zero diagonal;
the diagonal condition remains necessary in characteristic two. In a basis, the Gram matrix of an
alternating form is `Z - Zᵀ`, with `Z` its strictly upper triangular part.

## Main results

* `Matrix.isAlt_toBilin'_transpose_mul_mul`: rectangular pullback preserves alternation.
* `Matrix.sum_sum_transpose_mul_mul_apply_mul`: a bilinear map summed against the entries of
  `Wᵀ A W` on vectors `eₖ` is the bilinear map summed against the entries of `A` on the vectors
  `∑ₖ Wᵢₖ eₖ`.
* `Matrix.isAlt_toBilin'_iff`: alternation is skew-symmetry and a zero diagonal over any
  commutative ring.
* `Matrix.isAlt_toBilin'_one_iff`: for `R` nontrivial, the standard form on `n → R` is alternating
  exactly when `n` is empty.
* `Matrix.toBilin_apply_basis`, `Matrix.toBilin_one_apply`, `Matrix.nondegenerate_toBilin_one`,
  `Matrix.toBilin_one_apply_self_nonneg`: evaluation on basis vectors, coordinate dot-product
  formula, nondegeneracy, and diagonal nonnegativity for the identity-matrix form in a finite basis.
* `TauCeti.isUnit_det_hyperbolic`: the hyperbolic plane `!![0, 1; 1, 0]` is unimodular over every
  commutative ring.
* `LinearMap.BilinForm.toMatrix_dualBasis`: the Gram matrix of a nondegenerate form in a `B`-dual
  basis is the inverse transpose of its Gram matrix in the original basis.
* `LinearMap.BilinForm.det_toMatrix_dualBasis_mul_det_toMatrix`: the Gram determinants of a
  nondegenerate form in a basis and in its `B`-dual basis are inverse to each other.
* `LinearMap.BilinForm.dualBasis_apply_eq_sum_inv_toMatrix_smul`: the `B`-dual basis is obtained
  from the basis by the inverse Gram matrix.
* `LinearMap.BilinForm.Nondegenerate.repr_eq_sum_inv_toMatrix₂_mul_apply`: the coordinates of a
  vector in a basis are its pairings with the basis, contracted against the inverse Gram matrix.
* `LinearMap.BilinForm.separatingLeft_of_toMatrix_mul_eq_smul`: over a domain, a form whose Gram
  matrix has a right inverse up to a nonzero scalar is nondegenerate.
* `LinearMap.BilinForm.toMatrix_collectedBasis`: the Gram matrix of a form in a basis collected
  from a pairwise orthogonal internal direct sum is block diagonal, with the Gram matrices of the
  summands as blocks.
* `LinearMap.BilinForm.exists_basis_toMatrix_mul_toMatrix_eq_smul_of_isInternal`: Gram matrices
  of two forms on the summands of an orthogonal internal direct sum that multiply to `c • 1` give
  Gram matrices on the whole module with the same product; the same holds for the restrictions to
  the supremum of finitely many independent submodules
  (`LinearMap.BilinForm.exists_basis_restrict_biSup_toMatrix_mul_toMatrix_eq_smul`).
* `LinearMap.BilinForm.equivalent_iff_equivalent_of_toMatrix_mul_eq_smul`: if the Gram matrices of
  `B` and `D` in some basis multiply to `c • 1`, for a non-zero-divisor `c`, then `D` is determined
  up to isometry by `B` and conversely: such pairs `(B₁, D₁)` and `(B₂, D₂)` have `B₁ ≅ B₂` exactly
  when `D₁ ≅ D₂`. On a lattice `D` is the form `c B⁻¹`, read on the dual lattice, so this compares
  isometry classes of lattices with those of their `c`-scaled duals.
* `LinearMap.BilinForm.exists_toMatrix_eq_sub_transpose_of_isAlt`: an alternating form has a Gram
  matrix of the form `Z - Zᵀ`.
* `LinearMap.BilinForm.det_toMatrix_comp`, `LinearMap.BilinForm.det_toMatrix_eq_det_sq_mul_det`:
  the Gram determinant under a linear map and under a change of basis.
* `LinearMap.BilinForm.toMatrix_reindex`, `LinearMap.BilinForm.det_toMatrix_reindex`: reindexing
  a basis reindexes the Gram matrix and keeps its determinant.
* `LinearMap.BilinForm.Equivalent.exists_det_eq_unit_sq_mul_det`: equivalent forms have Gram
  determinants differing by a unit square, in any finite bases.
* `LinearMap.BilinForm.Equivalent.isSquare_det_mul_det`: hence the product of their Gram
  determinants is a square.
* `LinearMap.BilinForm.IsSymm.exists_sq_mul_det_toMatrix_eq_of_dvd_sub`: Gram determinants under
  an approximate isometry agree up to a square and a factor in `1 + 2rR`.
* `LinearMap.BilinForm.exists_span_range_eq_of_equivalent_toBilin'`: an isometry of Gram forms
  replaces a family by another of the prescribed Gram matrix with the same span.
* `LinearMap.BilinForm.exists_det_toMatrix_eq_of_eq_span`: the Gram determinant of the span of two
  orthogonal blocks; `LinearMap.BilinForm.isSquare_mul_det_mul_det_of_eq_span` compares it before
  and after one block is exchanged.
-/

public section

universe u

namespace Matrix

/-- Over a nontrivial commutative semiring `R`, the standard form `∑ i, x i * y i` on `n → R` is
alternating only when `n` is empty: it takes the value `1 ≠ 0` on every standard basis vector. -/
@[simp]
theorem isAlt_toBilin'_one_iff {n R : Type*} [Fintype n] [DecidableEq n] [CommSemiring R]
    [Nontrivial R] : (toBilin' (1 : Matrix n n R)).IsAlt ↔ IsEmpty n := by
  refine ⟨fun h => ⟨fun i => by simpa using h (Pi.single i 1)⟩, fun hn x => ?_⟩
  simp [Subsingleton.elim x 0]

/-- Evaluating `Matrix.toBilin b A` on basis vectors `b i` and `b j` recovers the matrix entry
`A i j`. -/
theorem toBilin_apply_basis {n R M : Type*} [Fintype n] [DecidableEq n] [CommSemiring R]
    [AddCommMonoid M] [Module R M] (b : Module.Basis n R M) (A : Matrix n n R) (i j : n) :
    Matrix.toBilin b A (b i) (b j) = A i j := by
  rw [← LinearMap.BilinForm.toMatrix_apply b, LinearMap.BilinForm.toMatrix_toBilin]

/-- The standard bilinear form attached to the identity matrix in a finite basis `b` evaluates to
the coordinate dot product `∑ i, b.repr x i * b.repr y i`. -/
theorem toBilin_one_apply {n R M : Type*} [Fintype n] [DecidableEq n] [CommSemiring R]
    [AddCommMonoid M] [Module R M] (b : Module.Basis n R M) (x y : M) :
    Matrix.toBilin b (1 : Matrix n n R) x y = ∑ i, b.repr x i * b.repr y i := by
  simp only [Matrix.toBilin_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- The standard bilinear form attached to the identity matrix in a finite basis is
nondegenerate. -/
theorem nondegenerate_toBilin_one {n R M : Type*} [Fintype n] [DecidableEq n] [CommSemiring R]
    [AddCommMonoid M] [Module R M] (b : Module.Basis n R M) :
    (Matrix.toBilin b (1 : Matrix n n R)).Nondegenerate := by
  refine ⟨fun x hx ↦ b.repr.injective ?_, fun y hy ↦ b.repr.injective ?_⟩
  · ext i
    have hi := hx (b i)
    rw [toBilin_one_apply] at hi
    simpa [Finsupp.single_apply] using hi
  · ext i
    have hi := hy (b i)
    rw [toBilin_one_apply] at hi
    simpa [Finsupp.single_apply] using hi

/-- Over a linearly ordered commutative ring, the identity-matrix bilinear form in a finite basis
has nonnegative diagonal values. -/
theorem toBilin_one_apply_self_nonneg {n R M : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    [LinearOrder R] [IsOrderedRing R] [AddCommMonoid M] [Module R M]
    (b : Module.Basis n R M) (x : M) :
    0 ≤ Matrix.toBilin b (1 : Matrix n n R) x x := by
  rw [toBilin_one_apply]
  exact Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _

section BilinearAlternation

variable {R I J : Type*} [CommSemiring R] [DecidableEq I] [Fintype I]

/-- Pulling back an alternating matrix form along a rectangular matrix preserves alternation. -/
theorem isAlt_toBilin'_transpose_mul_mul [DecidableEq J] [Fintype J]
    {Λ : Matrix I I R} (hΛ : Λ.toBilin'.IsAlt) (E : Matrix I J R) :
    (Eᵀ * Λ * E).toBilin'.IsAlt := by
  rw [← Matrix.toBilin'_comp]
  exact fun x ↦ hΛ (E.toLin' x)

/-- Every diagonal entry of an alternating matrix form is zero, over any commutative semiring. -/
theorem apply_self_eq_zero_of_isAlt_toBilin' {Λ : Matrix I I R}
    (hΛ : Λ.toBilin'.IsAlt) (i : I) : Λ i i = 0 := by
  simpa using hΛ.self_eq_zero (Pi.single i 1)

end BilinearAlternation

section BilinearSum

/-- Summing a bilinear map `B` against the entries of `Wᵀ A W` on a family of vectors `e` is
summing it against the entries of `A` on the vectors `∑ₖ Wᵢₖ eₖ`. -/
theorem sum_sum_transpose_mul_mul_apply_mul {R M I J : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] [Fintype I] [Fintype J] (A : Matrix I I R) (W : Matrix I J R)
    (B : M →ₗ[R] M →ₗ[R] R) (e : J → M) :
    ∑ k, ∑ l, (Wᵀ * A * W) k l * B (e k) (e l) =
      ∑ i, ∑ j, A i j * B (∑ k, W i k • e k) (∑ l, W j l • e l) := by
  have hcomm (f : J → J → I → I → R) :
      ∑ k, ∑ l, ∑ j, ∑ i, f k l j i = ∑ i, ∑ j, ∑ k, ∑ l, f k l j i :=
    calc ∑ k, ∑ l, ∑ j, ∑ i, f k l j i = ∑ k, ∑ l, ∑ i, ∑ j, f k l j i :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ l, ∑ j, f k l j i := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ i, ∑ k, ∑ l, ∑ j, f k l j i := Finset.sum_comm
      _ = ∑ i, ∑ k, ∑ j, ∑ l, f k l j i :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ k, ∑ l, f k l j i := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [hcomm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end BilinearSum

section BilinearAlternationRing

variable {R I : Type*} [CommRing R] [DecidableEq I] [Fintype I]

/-- Transposing the arguments of an alternating matrix form negates its entry. -/
theorem neg_apply_eq_of_isAlt_toBilin' {Λ : Matrix I I R} (hΛ : Λ.toBilin'.IsAlt) (i j : I) :
    -Λ i j = Λ j i := by
  simpa using hΛ.neg_eq (Pi.single i 1) (Pi.single j 1)

/-- The matrix of an alternating form is the negative of its transpose in every characteristic. -/
theorem transpose_eq_neg_of_isAlt_toBilin' {Λ : Matrix I I R}
    (hΛ : Λ.toBilin'.IsAlt) : Λᵀ = -Λ := by
  ext i j
  exact (neg_apply_eq_of_isAlt_toBilin' hΛ i j).symm

/-- Alternation is equivalent to skew-symmetry together with vanishing diagonal. The diagonal
condition is essential in characteristic two. -/
theorem isAlt_toBilin'_iff (Λ : Matrix I I R) :
    Λ.toBilin'.IsAlt ↔ Λᵀ = -Λ ∧ ∀ i, Λ i i = 0 := by
  refine ⟨fun h ↦ ⟨transpose_eq_neg_of_isAlt_toBilin' h,
    apply_self_eq_zero_of_isAlt_toBilin' h⟩, ?_⟩
  rintro ⟨ht, hd⟩ x
  have hsum : (∑ p : I × I, x p.1 * Λ p.1 p.2 * x p.2) = 0 := by
    apply Finset.sum_ninvolution Prod.swap
    · rintro ⟨i, j⟩
      have hij : Λ j i = -Λ i j := congr_fun (congr_fun ht i) j
      simp only [Prod.fst_swap, Prod.snd_swap]
      rw [hij]
      ring
    · rintro ⟨i, j⟩ hf he
      have hij : j = i := congrArg Prod.fst he
      subst j
      exact hf (by simp [hd])
    · intro p
      exact Finset.mem_univ _
    · intro p
      exact Prod.swap_swap p
  simpa only [Matrix.toBilin'_apply, Fintype.sum_prod_type] using hsum

end BilinearAlternationRing

end Matrix

namespace TauCeti

open Matrix

/-- The hyperbolic plane `U` is unimodular. -/
theorem isUnit_det_hyperbolic {R : Type*} [CommRing R] :
    IsUnit (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) R).det := by
  simp [det_fin_two_of]

end TauCeti

namespace LinearMap.BilinForm

open Matrix Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

/-- The Gram matrix of a nondegenerate bilinear form in the `B`-dual basis of `b` is the inverse of
the transpose of its Gram matrix in `b`. For a symmetric form this is the inverse Gram matrix. -/
theorem toMatrix_dualBasis (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V) :
    toMatrix (B.dualBasis hB b) B = (toMatrix b B)ᵀ⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  ext i j
  calc (toMatrix (B.dualBasis hB b) B * (toMatrix b B)ᵀ) i j
      = ∑ k, B (b j) (b k) • B (B.dualBasis hB b i) (B.dualBasis hB b k) := by
        simp only [Matrix.mul_apply, toMatrix_apply, transpose_apply, smul_eq_mul, mul_comm]
    _ = (1 : Matrix ι ι K) i j := by
        rw [sum_apply_smul_apply_dualBasis B hB b, apply_dualBasis_left, Matrix.one_apply]
        simp only [eq_comm]

/-- The Gram determinants of a nondegenerate bilinear form in a basis and in its `B`-dual basis
are inverse to each other. -/
theorem det_toMatrix_dualBasis_mul_det_toMatrix (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (b : Basis ι K V) : (toMatrix (B.dualBasis hB b) B).det * (toMatrix b B).det = 1 := by
  rw [toMatrix_dualBasis, det_nonsing_inv, det_transpose,
    Ring.inverse_mul_cancel _ (isUnit_iff_ne_zero.mpr ((nondegenerate_iff_det_ne_zero b).mp hB))]

/-- **The dual basis through the inverse Gram matrix**: the `i`-th vector of the `B`-dual basis
of `b` is `∑ⱼ (G⁻¹)ᵢⱼ bⱼ`, where `G = (B (b i) (b j))` is the Gram matrix of `B` in `b`. -/
theorem dualBasis_apply_eq_sum_inv_toMatrix_smul (B : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (b : Basis ι K V) (i : ι) :
    B.dualBasis hB b i = ∑ j, (toMatrix b B)⁻¹ i j • b j := by
  -- Expand `B.dualBasis hB b i` in `b`: its coefficients are entries of the Gram matrix of the
  -- dual basis, which is the inverse transpose of the Gram matrix in `b`.
  conv_lhs => rw [← sum_apply_dualBasis_smul hB b (B.dualBasis hB b i)]
  simp_rw [← toMatrix_apply, toMatrix_dualBasis, ← Matrix.transpose_nonsing_inv,
    Matrix.transpose_apply]

/-- **Coordinates from pairings.** For a nondegenerate bilinear form `B` and a basis `b`, the
`k`-th coordinate of a vector `v` is `Σ_l B^(kl) B(b l, v)`, where `B^(kl)` is the inverse of the
Gram matrix `B_ij = B(b i, b j)`. -/
theorem Nondegenerate.repr_eq_sum_inv_toMatrix₂_mul_apply {B : LinearMap.BilinForm K V}
    (hB : B.Nondegenerate) (b : Basis ι K V) (v : V) (k : ι) :
    b.repr v k = ∑ l, (LinearMap.toMatrix₂ b b B)⁻¹ k l * B (b l) v := by
  set G := LinearMap.toMatrix₂ b b B
  -- The coordinate vector `c` of `v` satisfies `G c = r`, with `r` the pairings `B(b l, v)`.
  set c : ι → K := fun k ↦ b.repr v k
  set r : ι → K := fun l ↦ B (b l) v
  have hG : IsUnit G.det :=
    isUnit_iff_ne_zero.2 ((LinearMap.nondegenerate_iff_det_ne_zero b).1 hB)
  have hGc : G *ᵥ c = r := by
    ext l
    conv_rhs => simp only [r]; rw [← b.sum_repr v]
    simp only [Matrix.mulVec, dotProduct, G, LinearMap.toMatrix₂_apply, c, map_sum, map_smul,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun p _ ↦ mul_comm _ _
  have hc : c = G⁻¹ *ᵥ r := by
    rw [← hGc, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG, Matrix.one_mulVec]
  exact congrFun hc k

section Domain

variable {R M n : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] [Fintype n]
  [DecidableEq n]

/-- A bilinear form whose Gram matrix in some basis, times some matrix, is a nonzero scalar matrix
is nondegenerate: its Gram determinant divides a power of a nonzero element of a domain. -/
theorem separatingLeft_of_toMatrix_mul_eq_smul {B : LinearMap.BilinForm R M} (b : Basis n R M)
    {H : Matrix n n R} {c : R} (hc : c ≠ 0) (hH : B.toMatrix b * H = c • 1) : B.SeparatingLeft := by
  refine ((nondegenerate_iff_det_ne_zero b).mpr fun h ↦ ?_).1
  have := congrArg Matrix.det hH
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ hc this.symm

end Domain

section CollectedBasis

open LinearMap (BilinForm)

variable {R : Type*} [CommSemiring R]

/-- **The Gram matrix of an orthogonal sum.** If `M` is the internal direct sum of submodules
`P i` which are pairwise orthogonal for `B`, the Gram matrix of `B` in the basis collected from
bases `d i` of the `P i` is block diagonal, with blocks the Gram matrices of the restrictions of
`B` to the `P i`. -/
theorem toMatrix_collectedBasis {M o : Type*} [AddCommMonoid M] [Module R M] [Fintype o]
    [DecidableEq o] {B : BilinForm R M} {P : o → Submodule R M} (hP : DirectSum.IsInternal P)
    (horth : ∀ i i', i ≠ i' → ∀ x ∈ P i, ∀ y ∈ P i', B x y = 0) {α : o → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)] (d : ∀ i, Basis (α i) R (P i)) :
    B.toMatrix (hP.collectedBasis d) =
      Matrix.blockDiagonal' fun i ↦ (B.restrict (P i)).toMatrix (d i) := by
  ext ⟨i, a⟩ ⟨i', a'⟩
  rw [toMatrix_apply, DirectSum.IsInternal.collectedBasis_coe]
  by_cases hii : i = i'
  · subst hii
    simp [Matrix.blockDiagonal'_apply_eq, toMatrix_apply]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hii]
    exact horth _ _ hii _ (d i a).property _ (d i' a').property

/-- If two forms are pairwise orthogonal across a family of submodules `P i` of which `M` is the
internal direct sum, and their Gram matrices in bases `d i` of the `P i` multiply to `c • 1`, then
so do their Gram matrices in the collected basis. -/
theorem toMatrix_collectedBasis_mul_toMatrix_collectedBasis {M o : Type*} [AddCommMonoid M]
    [Module R M] [Fintype o] [DecidableEq o] {B D : BilinForm R M} {P : o → Submodule R M}
    (hP : DirectSum.IsInternal P) (hB : ∀ i i', i ≠ i' → ∀ x ∈ P i, ∀ y ∈ P i', B x y = 0)
    (hD : ∀ i i', i ≠ i' → ∀ x ∈ P i, ∀ y ∈ P i', D x y = 0) {α : o → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)] (d : ∀ i, Basis (α i) R (P i)) {c : R}
    (hd : ∀ i, (B.restrict (P i)).toMatrix (d i) * (D.restrict (P i)).toMatrix (d i) = c • 1) :
    B.toMatrix (hP.collectedBasis d) * D.toMatrix (hP.collectedBasis d) = c • 1 := by
  rw [toMatrix_collectedBasis hP hB, toMatrix_collectedBasis hP hD, ← Matrix.blockDiagonal'_mul]
  simp only [hd]
  have := Matrix.blockDiagonal'_smul c (1 : ∀ i, Matrix (α i) (α i) R)
  rwa [Matrix.blockDiagonal'_one] at this

end CollectedBasis

section Dual

open LinearMap (BilinForm)

variable {R M₁ M₂ ι κ : Type*} [CommRing R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
  [Module R M₂] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- If two forms are pairwise orthogonal across a family of submodules `N i` of which `M` is the
internal direct sum, finitely many of them nonzero, and their Gram matrices in some basis of each
nonzero `N i` multiply to `c • 1`, then so do their Gram matrices in some basis of `M`. -/
theorem exists_basis_toMatrix_mul_toMatrix_eq_smul_of_isInternal {M : Type*} {o : Type u}
    [AddCommGroup M] [Module R M] [DecidableEq o] {B D : BilinForm R M} {N : o → Submodule R M}
    (hN : DirectSum.IsInternal N) (hfin : {i | N i ≠ ⊥}.Finite)
    (hB : ∀ i i', i ≠ i' → ∀ x ∈ N i, ∀ y ∈ N i', B x y = 0)
    (hD : ∀ i i', i ≠ i' → ∀ x ∈ N i, ∀ y ∈ N i', D x y = 0) {c : R}
    (hd : ∀ i, N i ≠ ⊥ → ∃ (α : Type u) (_ : Fintype α) (_ : DecidableEq α) (d : Basis α R (N i)),
      (B.restrict (N i)).toMatrix d * (D.restrict (N i)).toMatrix d = c • 1) :
    ∃ (β : Type u) (_ : Fintype β) (_ : DecidableEq β) (b : Basis β R M),
      B.toMatrix b * D.toMatrix b = c • 1 := by
  have : Finite {i // N i ≠ ⊥} := hfin.to_subtype
  have : Fintype {i // N i ≠ ⊥} := Fintype.ofFinite _
  choose α _ _ d hd using fun i : {i // N i ≠ ⊥} ↦ hd i i.property
  have hP : DirectSum.IsInternal fun i : {i // N i ≠ ⊥} ↦ N i :=
    DirectSum.isInternal_ne_bot_iff.mpr hN
  refine ⟨_, inferInstance, inferInstance, hP.collectedBasis d,
    toMatrix_collectedBasis_mul_toMatrix_collectedBasis hP ?_ ?_ d hd⟩
  · exact fun i i' hii ↦ hB i i' fun h ↦ hii (Subtype.ext h)
  · exact fun i i' hii ↦ hD i i' fun h ↦ hii (Subtype.ext h)

/-- The version of `exists_basis_toMatrix_mul_toMatrix_eq_smul_of_isInternal` for the
restrictions of the forms to the supremum of finitely many members `N i`, `i ∈ s`, of an
independent family of submodules. -/
theorem exists_basis_restrict_biSup_toMatrix_mul_toMatrix_eq_smul {M : Type*} {o : Type u}
    [AddCommGroup M] [Module R M] {B D : BilinForm R M} {N : o → Submodule R M}
    (hN : iSupIndep N) (hB : ∀ i i', i ≠ i' → ∀ x ∈ N i, ∀ y ∈ N i', B x y = 0)
    (hD : ∀ i i', i ≠ i' → ∀ x ∈ N i, ∀ y ∈ N i', D x y = 0) {s : Set o} (hs : s.Finite) {c : R}
    (hd : ∀ i ∈ s, ∃ (α : Type u) (_ : Fintype α) (_ : DecidableEq α) (d : Basis α R (N i)),
      (B.restrict (N i)).toMatrix d * (D.restrict (N i)).toMatrix d = c • 1) :
    ∃ (β : Type u) (_ : Fintype β) (_ : DecidableEq β) (b : Basis β R ↥(⨆ i ∈ s, N i)),
      (B.restrict (⨆ i ∈ s, N i)).toMatrix b * (D.restrict (⨆ i ∈ s, N i)).toMatrix b =
        c • 1 := by
  classical
  have : Fintype s := hs.fintype
  choose α _ _ d hd using fun i : s ↦ hd i i.property
  set A := ⨆ i ∈ s, N i
  have hle (i : s) : N i ≤ A := le_biSup N i.property
  -- Transport the bases of the `N i` into `A`.
  let d' (i : s) : Basis (α i) R ((N i).comap A.subtype) :=
    (d i).map (Submodule.comapSubtypeEquivOfLe (hle i)).symm
  have hgram (F : BilinForm R M) (i : s) :
      ((F.restrict A).restrict ((N i).comap A.subtype)).toMatrix (d' i) =
        (F.restrict (N i)).toMatrix (d i) := by
    ext a a'
    simp only [toMatrix_apply, restrict_apply, LinearMap.domRestrict_apply, d', Basis.map_apply,
      Submodule.comapSubtypeEquivOfLe_symm_apply]
  have hP := DirectSum.isInternal_biSup_submodule_of_iSupIndep s (hN.comp Subtype.val_injective)
  refine ⟨_, inferInstance, inferInstance, hP.collectedBasis d',
    toMatrix_collectedBasis_mul_toMatrix_collectedBasis hP ?_ ?_ d' fun i ↦ ?_⟩
  · exact fun i i' hii x hx y hy ↦ hB i i' (fun h ↦ hii (Subtype.ext h)) _ hx _ hy
  · exact fun i i' hii x hx y hy ↦ hD i i' (fun h ↦ hii (Subtype.ext h)) _ hx _ hy
  · rw [hgram, hgram]
    exact hd i

/-- One direction of `LinearMap.BilinForm.equivalent_iff_equivalent_of_toMatrix_mul_eq_smul`. If
`e` is an isometry with matrix `P`, the contragredient map, with matrix the inverse transpose of
`P`, carries `D₁` to `D₂`. -/
private theorem Equivalent.of_toMatrix_mul_eq_smul {B₁ D₁ : BilinForm R M₁}
    {B₂ D₂ : BilinForm R M₂} (b₁ : Basis ι R M₁) (b₂ : Basis κ R M₂) {c : R}
    (hc : c ∈ nonZeroDivisors R) (h₁ : B₁.toMatrix b₁ * D₁.toMatrix b₁ = c • 1)
    (h₂ : B₂.toMatrix b₂ * D₂.toMatrix b₂ = c • 1) (h : B₁.Equivalent B₂) : D₁.Equivalent D₂ := by
  obtain ⟨e⟩ := h
  set P := LinearMap.toMatrix b₁ b₂ e.toLinearEquiv.toLinearMap
  set P' := LinearMap.toMatrix b₂ b₁ e.toLinearEquiv.symm.toLinearMap
  have hP'P : P' * P = 1 := by
    rw [← LinearMap.toMatrix_comp]
    simp
  have hPP' : P * P' = 1 := by
    rw [← LinearMap.toMatrix_comp]
    simp
  have hG : B₁.toMatrix b₁ = Pᵀ * B₂.toMatrix b₂ * P := by
    rw [← toMatrix_comp]
    congr 1
    ext x y
    simp [e.map_app]
  -- The candidate Gram matrix `P' * H₂ * P'ᵀ` of `D₂` pulled back is `D₁`'s, after cancelling `c`.
  have hX := Matrix.mul_mul_transpose_eq_of_mul_eq_smul_one hc hPP' hG h₁ h₂
  let f : M₁ ≃ₗ[R] M₂ := LinearEquiv.ofLinearMap (Matrix.toLin b₁ b₂ P'ᵀ) (Matrix.toLin b₂ b₁ Pᵀ)
    (by rw [← Matrix.toLin_mul, ← Matrix.transpose_mul, hPP', Matrix.transpose_one,
      Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul, ← Matrix.transpose_mul, hP'P, Matrix.transpose_one,
      Matrix.toLin_one])
  have hf : D₂.comp f.toLinearMap f.toLinearMap = D₁ := by
    refine (toMatrix b₁).injective ?_
    rw [toMatrix_comp b₂, LinearEquiv.toLinearMap_ofLinearMap, LinearMap.toMatrix_toLin,
      Matrix.transpose_transpose, hX]
  exact ⟨{ toLinearEquiv := f, map_app' := fun x y ↦ by simpa using LinearMap.congr_fun₂ hf x y }⟩

/-- **Isometry classes of forms and of their scaled duals.** Let `c` be a non-zero-divisor, and
let `B₁, D₁` and `B₂, D₂` be bilinear forms whose Gram matrices in bases `b₁` and `b₂` multiply to
`c • 1`. Then `B₁` and `B₂` are isometric exactly when `D₁` and `D₂` are. On a lattice, `D` is
the form `c B⁻¹` transported from the dual lattice, so the isometry class of a nondegenerate form
determines that of its `c`-scaled dual and conversely. -/
theorem equivalent_iff_equivalent_of_toMatrix_mul_eq_smul {B₁ D₁ : BilinForm R M₁}
    {B₂ D₂ : BilinForm R M₂} (b₁ : Basis ι R M₁) (b₂ : Basis κ R M₂) {c : R}
    (hc : c ∈ nonZeroDivisors R) (h₁ : B₁.toMatrix b₁ * D₁.toMatrix b₁ = c • 1)
    (h₂ : B₂.toMatrix b₂ * D₂.toMatrix b₂ = c • 1) : B₁.Equivalent B₂ ↔ D₁.Equivalent D₂ :=
  ⟨Equivalent.of_toMatrix_mul_eq_smul b₁ b₂ hc h₁ h₂,
    Equivalent.of_toMatrix_mul_eq_smul b₁ b₂ hc ((Matrix.mul_eq_smul_one_comm hc).mp h₁)
      ((Matrix.mul_eq_smul_one_comm hc).mp h₂)⟩

end Dual

section Alternating

open LinearMap (BilinForm)

/-- The Gram matrix of an alternating bilinear form is of the form `Z - Zᵀ`. -/
theorem exists_toMatrix_eq_sub_transpose_of_isAlt {R M ι : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Fintype ι] [DecidableEq ι] (b : Basis ι R M) {D : BilinForm R M}
    (hD : D.IsAlt) : ∃ Z : Matrix ι ι R, D.toMatrix b = Z - Zᵀ := by
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  refine ⟨Matrix.of fun i j => if i < j then D (b i) (b j) else 0, ?_⟩
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [toMatrix_apply, Function.swap, h, h.not_gt]
  · simp [toMatrix_apply, hD.self_eq_zero]
  · simp [toMatrix_apply, Function.swap, h, h.not_gt, ← hD.neg_eq (b j) (b i)]

end Alternating

/-! ### Gram determinants -/

section GramDeterminant

open LinearMap (BilinForm)

/-- Reindexing a basis reindexes the Gram matrix along the same equivalence. -/
theorem toMatrix_reindex {R M ι κ : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (b : Basis ι R M) (e : ι ≃ κ)
    (B : BilinForm R M) :
    B.toMatrix (b.reindex e) = Matrix.reindex e e (B.toMatrix b) := by
  ext i j
  simp [toMatrix_apply]

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {B : BilinForm R M}

/-- Pulling back a bilinear form along a linear map multiplies its Gram determinant by the
square of the coordinate-map determinant. The source and target bases use the same arbitrary
finite index type; no symmetry or nondegeneracy is required. -/
theorem det_toMatrix_comp {N ι : Type*} [AddCommGroup N] [Module R N]
    [Fintype ι] [DecidableEq ι] (b : Basis ι R M) (c : Basis ι R N)
    (C : BilinForm R N) (f : M →ₗ[R] N) :
    ((C.comp f f).toMatrix b).det =
      (LinearMap.toMatrix b c f).det ^ 2 * (C.toMatrix c).det := by
  rw [toMatrix_comp c b, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- A change of basis multiplies the Gram determinant by the square of the basis-change
matrix determinant. -/
theorem det_toMatrix_eq_det_sq_mul_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b c : Basis ι R M) (B : BilinForm R M) :
    (B.toMatrix c).det = (b.toMatrix c).det ^ 2 * (B.toMatrix b).det := by
  simpa only [comp_id_id, LinearMap.toMatrix_id_eq_basis_toMatrix] using
    det_toMatrix_comp c b B LinearMap.id

/-- Reindexing a basis does not change the Gram determinant. -/
@[simp]
theorem det_toMatrix_reindex {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] (b : Basis ι R M) (e : ι ≃ ι') (B : BilinForm R M) :
    (B.toMatrix (b.reindex e)).det = (B.toMatrix b).det := by
  rw [toMatrix_reindex, Matrix.det_reindex_self]

/-- The Gram determinants of equivalent bilinear forms differ by the square of a unit. This
holds over any commutative ring, including for singular and nonsymmetric forms, in any
caller-provided finite bases; their index types need not be the same. -/
theorem Equivalent.exists_det_eq_unit_sq_mul_det {N ι κ : Type*} [AddCommGroup N] [Module R N]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {C : BilinForm R N}
    (h : B.Equivalent C) (b : Basis ι R M) (c : Basis κ R N) :
    ∃ u : Rˣ, (B.toMatrix b).det = (u : R) ^ 2 * (C.toMatrix c).det := by
  cases subsingleton_or_nontrivial R
  · exact ⟨1, Subsingleton.elim _ _⟩
  obtain ⟨e⟩ := h
  -- Compare with `c` reindexed along `κ ≃ ι`, which exists since `M ≃ N` over a nontrivial ring.
  let c' := c.reindex (c.indexEquiv (b.map e.toLinearEquiv))
  have hform : B = C.comp e.toLinearEquiv.toLinearMap e.toLinearEquiv.toLinearMap := by
    ext x y
    simp [e.map_app]
  refine ⟨(e.toLinearEquiv.isUnit_det b c').unit, ?_⟩
  conv_lhs => rw [hform]
  rw [det_toMatrix_comp b c', IsUnit.unit_spec, det_toMatrix_reindex]

/-- The product of Gram determinants of equivalent bilinear forms is a square. This holds over
any commutative ring, including for singular and nonsymmetric forms, in any caller-provided
finite bases; their index types need not be the same. -/
theorem Equivalent.isSquare_det_mul_det {N ι κ : Type*} [AddCommGroup N] [Module R N]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {C : BilinForm R N}
    (h : B.Equivalent C) (b : Basis ι R M) (c : Basis κ R N) :
    IsSquare ((B.toMatrix b).det * (C.toMatrix c).det) := by
  obtain ⟨u, hu⟩ := h.exists_det_eq_unit_sq_mul_det b c
  exact ⟨u * (C.toMatrix c).det, by rw [hu]; ring⟩

/-- **Gram determinants under approximate isometries.** Let `B` and `C` be symmetric, and let `b₀`
be a finite basis of the domain of `C` whose Gram matrix times a matrix `H` is `a • 1`. Let `φ`
carry `C` to `B` modulo `a * r`, where `2 ∣ r`, and suppose that `H` has even diagonal or that `φ`
also carries the self-pairings modulo `2 * (a * r)`. Then in any bases of the same size, the Gram
determinants `d` of `B` and `d'` of `C` satisfy `c ^ 2 * d = (1 + 2 r t) * d'` for some `c` and
`t`. -/
theorem IsSymm.exists_sq_mul_det_toMatrix_eq_of_dvd_sub {N : Type*}
    [AddCommGroup N] [Module R N] {C : BilinForm R N} (hB : B.IsSymm) (hC : C.IsSymm)
    {a r : R} (h2 : 2 ∣ r) {ι₀ : Type*} [Fintype ι₀]
    [DecidableEq ι₀] (b₀ : Basis ι₀ R N) {H : Matrix ι₀ ι₀ R} (hH : C.toMatrix b₀ * H = a • 1)
    (φ : N →ₗ[R] M) (h₁ : ∀ x y, a * r ∣ C x y - B (φ x) (φ y))
    (hd : (∀ k, 2 ∣ H k k) ∨ ∀ x, 2 * (a * r) ∣ C x x - B (φ x) (φ x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι R M) (b' : Basis ι R N) :
    ∃ c t : R, c ^ 2 * (B.toMatrix b).det = (1 + 2 * r * t) * (C.toMatrix b').det := by
  cases subsingleton_or_nontrivial R
  · exact ⟨0, 0, Subsingleton.elim _ _⟩
  -- The difference of the Gram matrices of `C` and of the pullback of `B` is `(a * r) • E` for a
  -- symmetric `E`, with `E` of even diagonal in the second case of `hd`.
  have hG := (isSymm_toMatrix_iff_isSymm b₀).mpr hC
  have hS : (C.toMatrix b₀ - (B.comp φ φ).toMatrix b₀).IsSymm :=
    hG.sub ((isSymm_toMatrix_iff_isSymm b₀).mpr ⟨fun x y ↦ by rw [comp_apply, comp_apply, hB.eq]⟩)
  have hdiv : ∀ k l, a * r ∣ (C.toMatrix b₀ - (B.comp φ φ).toMatrix b₀) k l := fun k l ↦ by
    simpa [toMatrix_apply] using h₁ (b₀ k) (b₀ l)
  obtain ⟨E, hEs, hcomp, hd'⟩ : ∃ E : Matrix ι₀ ι₀ R, E.IsSymm ∧
      (B.comp φ φ).toMatrix b₀ = C.toMatrix b₀ - (a * r) • E ∧
        ((∀ k, 2 ∣ H k k) ∨ ∀ k, 2 ∣ E k k) := by
    rcases hd with hd | hd
    · obtain ⟨E, hE, hSE⟩ := hS.exists_eq_smul (a * r) hdiv
      exact ⟨E, hE, by rw [← hSE, sub_sub_cancel], .inl hd⟩
    · obtain ⟨D, hD⟩ := hS.exists_eq_smul_add_transpose (a * r) hdiv fun k ↦ by
        simpa [toMatrix_apply] using hd (b₀ k)
      exact ⟨D + Dᵀ, isSymm_add_transpose_self D, by rw [← hD, sub_sub_cancel],
        .inr fun k ↦ ⟨D k k, by simp [two_mul]⟩⟩
  obtain ⟨t, ht⟩ := hG.exists_det_sub_smul_eq_mul_det hEs hH hd' h2
  -- Compare with the given bases, reindexed along `ι ≃ ι₀`.
  let e : ι ≃ ι₀ := b'.indexEquiv b₀
  rw [← hcomp, det_toMatrix_comp b₀ (b.reindex e), det_toMatrix_reindex] at ht
  refine ⟨(LinearMap.toMatrix b₀ (b.reindex e) φ).det * (b₀.toMatrix (b'.reindex e)).det, t, ?_⟩
  rw [← det_toMatrix_reindex b' e, det_toMatrix_eq_det_sq_mul_det b₀ (b'.reindex e)]
  linear_combination (b₀.toMatrix (b'.reindex e)).det ^ 2 * ht

end GramDeterminant

section GramFamily

open LinearMap (BilinForm)

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {B : BilinForm R M}

/-- **Transporting a family along an isometry of Gram forms.** If a family `v` has Gram matrix
`G`, and the forms `Matrix.toBilin' G` and `Matrix.toBilin' G'` are isometric, then some family `v'`
spanning the same submodule as `v` has Gram matrix `G'`. -/
theorem exists_span_range_eq_of_equivalent_toBilin' {ι : Type*} [Fintype ι] [DecidableEq ι]
    {v : ι → M} {G G' : Matrix ι ι R} (hG : ∀ i j, B (v i) (v j) = G i j)
    (h : (Matrix.toBilin' G).Equivalent (Matrix.toBilin' G')) :
    ∃ v' : ι → M, (∀ i j, B (v' i) (v' j) = G' i j) ∧
      Submodule.span R (Set.range v') = Submodule.span R (Set.range v) := by
  obtain ⟨ψ⟩ := h
  -- `Φ` sends a coordinate vector to the corresponding combination of `v`.
  let Φ := Fintype.linearCombination R v
  have hΦ (x y : ι → R) : B (Φ x) (Φ y) = Matrix.toBilin' G x y := by
    simp only [Φ, Fintype.linearCombination_apply, Matrix.toBilin'_apply, map_sum, map_smul,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hG]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  let b := (Pi.basisFun R ι).map ψ.symm.toLinearEquiv
  refine ⟨fun i ↦ Φ (b i), fun i j ↦ ?_, ?_⟩
  · simp [b, hΦ, Matrix.toBilin'_single]
  · rw [Set.range_comp' Φ b, ← Submodule.map_span, b.span_eq, Submodule.map_top,
      Fintype.range_linearCombination]

/-- The Gram matrix of the concatenation of two mutually orthogonal families `v` and `t`, with
Gram matrices `c * A` and `c * G`, is `c` times the block-diagonal matrix of `A` and `G`. -/
theorem IsRefl.apply_sum_elim_eq_mul_fromBlocks (hB : B.IsRefl) {c : R} {ι κ : Type*}
    {v : ι → M} {t : κ → M} {A : Matrix ι ι R} {G : Matrix κ κ R}
    (hA : ∀ i j, B (v i) (v j) = c * A i j) (hG : ∀ i j, B (t i) (t j) = c * G i j)
    (hvt : ∀ i j, B (v i) (t j) = 0) (i j : ι ⊕ κ) :
    B (Sum.elim v t i) (Sum.elim v t j) = c * Matrix.fromBlocks A 0 0 G i j := by
  rcases i with i | i <;> rcases j with j | j <;> simp [hA, hG, hvt, hB _ _ (hvt _ _)]

/-- **The Gram determinant of the span of two orthogonal blocks.** Let `v` and `t` be mutually
orthogonal families with Gram matrices `c * A` and `c * G`, where `c` is a non-zero-divisor and
`A` and `G` have unit determinants. Then in every basis of the span of `v` and `t` of size `n`, the
Gram determinant is `c ^ n * det A * det G` times a square. -/
theorem exists_det_toMatrix_eq_of_eq_span [Nontrivial R] (hB : B.IsRefl) {c : R}
    (hc : c ∈ nonZeroDivisors R) {p m : ℕ} {v : Fin p → M} {t : Fin m → M}
    {A : Matrix (Fin p) (Fin p) R} {G : Matrix (Fin m) (Fin m) R}
    (hA : ∀ i j, B (v i) (v j) = c * A i j) (hG : ∀ i j, B (t i) (t j) = c * G i j)
    (hvt : ∀ i j, B (v i) (t j) = 0) (hAu : IsUnit A.det) (hGu : IsUnit G.det)
    {P : Submodule R M} (hP : P = Submodule.span R (Set.range (Sum.elim v t))) {n : ℕ}
    (d : Basis (Fin n) R P) :
    ∃ r : R, ((B.restrict P).toMatrix d).det = r ^ 2 * (c ^ n * (A.det * G.det)) := by
  classical
  have hu := hB.apply_sum_elim_eq_mul_fromBlocks hA hG hvt
  have hli := linearIndependent_of_isUnit_det hc hu
    (by rw [Matrix.det_fromBlocks_zero₂₁]; exact hAu.mul hGu)
  -- The concatenated family is a basis of `P`, in which the Gram matrix is block diagonal.
  let b : Basis (Fin p ⊕ Fin m) R P := (Basis.span hli).map (LinearEquiv.ofEq _ _ hP.symm)
  have hb : (B.restrict P).toMatrix b = c • Matrix.fromBlocks A 0 0 G := by
    ext i j
    simp [toMatrix_apply, b, Basis.span_apply, hu]
  have hcard : Fintype.card (Fin p ⊕ Fin m) = n := by
    rw [← finrank_eq_card_basis b, finrank_eq_card_basis d, Fintype.card_fin]
  let e : Fin p ⊕ Fin m ≃ Fin n := Fintype.equivFinOfCardEq hcard
  refine ⟨((b.reindex e).toMatrix d).det, ?_⟩
  rw [det_toMatrix_eq_det_sq_mul_det (b.reindex e) d, det_toMatrix_reindex, hb, Matrix.det_smul,
    Matrix.det_fromBlocks_zero₂₁, hcard]

/-- **Exchanging a block of an orthogonal sum.** Let `v` and `v'` be families with Gram matrices
`c * A` and `c * A'`, both orthogonal to a family `t` with Gram matrix `c * G`, where `c` is a
non-zero-divisor and `A`, `A'` and `G` have unit determinants. If `u * det A * det A'` is a square,
then so is `u` times the Gram determinants of the spans `P` of `v` and `t` and `P'` of `v'` and
`t`, in any bases of the same size. -/
theorem isSquare_mul_det_mul_det_of_eq_span [Nontrivial R] (hB : B.IsRefl) {c u : R}
    (hc : c ∈ nonZeroDivisors R) {p m : ℕ} {v v' : Fin p → M} {t : Fin m → M}
    {A A' : Matrix (Fin p) (Fin p) R} {G : Matrix (Fin m) (Fin m) R}
    (hA : ∀ i j, B (v i) (v j) = c * A i j)
    (hA' : ∀ i j, B (v' i) (v' j) = c * A' i j) (hG : ∀ i j, B (t i) (t j) = c * G i j)
    (hvt : ∀ i j, B (v i) (t j) = 0) (hv't : ∀ i j, B (v' i) (t j) = 0) (hAu : IsUnit A.det)
    (hA'u : IsUnit A'.det) (hGu : IsUnit G.det) (hu : IsSquare (u * A.det * A'.det))
    {P P' : Submodule R M} (hP : P = Submodule.span R (Set.range (Sum.elim v t)))
    (hP' : P' = Submodule.span R (Set.range (Sum.elim v' t))) {n : ℕ}
    (d : Basis (Fin n) R P) (d' : Basis (Fin n) R P') :
    IsSquare (u * ((B.restrict P).toMatrix d).det * ((B.restrict P').toMatrix d').det) := by
  obtain ⟨r, hr⟩ := exists_det_toMatrix_eq_of_eq_span hB hc hA hG hvt hAu hGu hP d
  obtain ⟨r', hr'⟩ := exists_det_toMatrix_eq_of_eq_span hB hc hA' hG hv't hA'u hGu hP' d'
  obtain ⟨s, hs⟩ := hu
  refine ⟨r * r' * c ^ n * G.det * s, ?_⟩
  rw [hr, hr']
  linear_combination (r * r' * c ^ n * G.det) ^ 2 * hs

end GramFamily

end LinearMap.BilinForm

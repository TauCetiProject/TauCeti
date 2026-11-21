/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Flag
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Flags of triangular bases

Let `e` and `b` be bases of a vector space indexed by `Fin n`, with `b` triangular with respect
to `e`: each `b l` is a combination of `e 0, …, e l`. Then `b` and `e` define the same flag of
subspaces in the sense of `Module.Basis.flag`. Combined with
`Module.Basis.mem_flag_iff_repr_eq_zero`, a vector in the span of `e 0, …, e (j - 1)` has
vanishing `b`-coordinates from the `j`-th on.

For a linearly ordered index type, a family `v` is triangular with respect to a basis `b` with
diagonal coefficients `c` when each `v i - c i • b i` is a combination of the `b j` with `j < i`.
Its matrix in `b` is then upper triangular, so its determinant in `b` is the product of the `c i`.
In the same way, an endomorphism `f` with each `f (b j) - c j • b j` in the span of the earlier
basis vectors has an upper-triangular matrix in `b` with diagonal `c`.

## Main results

* `Module.Basis.flag_eq_of_triangular`: a basis triangular with respect to `e` has the same flag
  as `e`.
* `Module.Basis.det_eq_prod_of_sub_smul_mem_span`: the determinant of a triangular family is the
  product of its diagonal coefficients.
* `Module.Basis.det_pos_of_sub_smul_mem_span`: over an ordered ring, a triangular family with
  positive diagonal coefficients has positive determinant.
* `Module.Basis.det_pos_of_sub_smul_mem_span_image_fst_lt`: the same for a family indexed by a
  product `ι × κ`, triangular with respect to the order on the first factor only.
* `Module.Basis.toMatrix_isUpperTriangular_of_sub_smul_mem_flag` and
  `Module.Basis.toMatrix_apply_self_of_sub_smul_mem_flag`: an endomorphism that is triangular with
  respect to the flag of a basis has an upper-triangular matrix in that basis, with the given
  diagonal.
-/

public section

open Submodule

namespace Module.Basis

variable {K E : Type*} [DivisionRing K] [AddCommGroup E] [Module K E] {n : ℕ}

/-- A basis `b` that is triangular with respect to a basis `e` (each `b l` is a combination of
`e 0, …, e l`) has the same flag as `e`: `b 0, …, b (k - 1)` and `e 0, …, e (k - 1)` span the
same subspace. -/
theorem flag_eq_of_triangular (b : Basis (Fin n) K E) {e : Basis (Fin n) K E}
    (htri : ∀ l i, l < i → e.repr (b l) i = 0) (k : Fin (n + 1)) : b.flag k = e.flag k := by
  have := e.finiteDimensional_of_finite
  refine eq_of_le_of_finrank_eq (b.flag_le_iff.2 fun l hl ↦ e.mem_flag_iff_repr_eq_zero.2
    fun i hi ↦ htri l i (Fin.castSucc_lt_castSucc_iff.1 (hl.trans_le hi))) ?_
  -- The two flags are spans of families indexed by the same set, hence have the same dimension.
  rw [flag, flag, Set.image_eq_range, Set.image_eq_range]
  exact (finrank_span_eq_card (b.linearIndependent.comp _ Subtype.val_injective)).trans
    (finrank_span_eq_card (e.linearIndependent.comp _ Subtype.val_injective)).symm

section Det

variable {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
  [LinearOrder ι]

/-- The determinant of a family `v` that is triangular with respect to a basis `b`, in the sense
that each `v i - c i • b i` is a combination of the `b j` with `j < i`, is the product of the
diagonal coefficients `c i`. -/
theorem det_eq_prod_of_sub_smul_mem_span (b : Basis ι R M) {v : ι → M} {c : ι → R}
    (hv : ∀ i, v i - c i • b i ∈ span R (b '' Set.Iio i)) : b.det v = ∏ i, c i := by
  -- The coordinates of `v i` at the indices `j ≥ i` are those of `c i • b i`.
  have hrepr (i j : ι) (hij : i ≤ j) : b.repr (v i) j = c i * Finsupp.single i 1 j := by
    have h0 : b.repr (v i - c i • b i) j = 0 := by
      by_contra h
      exact not_lt.2 hij (b.mem_span_image.1 (hv i) (Finsupp.mem_support_iff.2 h))
    rwa [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, repr_self, smul_eq_mul,
      sub_eq_zero] at h0
  rw [det_apply, Matrix.det_of_isUpperTriangular]
  · simp [toMatrix_apply, hrepr _ _ le_rfl]
  · intro i j (hji : j < i)
    rw [toMatrix_apply, hrepr _ _ hji.le, Finsupp.single_eq_of_ne hji.ne', mul_zero]

/-- Over an ordered ring, a family `v` that is triangular with respect to a basis `b` with positive
diagonal coefficients `c i`, in the sense of `Module.Basis.det_eq_prod_of_sub_smul_mem_span`, has
positive determinant in `b`. -/
theorem det_pos_of_sub_smul_mem_span [PartialOrder R] [IsStrictOrderedRing R] (b : Basis ι R M)
    {v : ι → M} {c : ι → R} (hc : ∀ i, 0 < c i)
    (hv : ∀ i, v i - c i • b i ∈ span R (b '' Set.Iio i)) : 0 < b.det v := by
  rw [b.det_eq_prod_of_sub_smul_mem_span hv]
  exact Finset.prod_pos fun i _ ↦ hc i

end Det

section Prod

variable {ι κ R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [Fintype κ]
  [LinearOrder ι] [DecidableEq κ] [PartialOrder R] [IsStrictOrderedRing R]

/-- Over an ordered ring, a family `v` indexed by `ι × κ` that is triangular with respect to a
basis `b` with positive diagonal coefficients `c p`, in the sense that each `v p - c p • b p` is a
combination of the `b r` with `r.1 < p.1`, has positive determinant in `b`. This is
`Module.Basis.det_pos_of_sub_smul_mem_span` for a lexicographic order on the index type; the
order on `κ` plays no role, since the hypothesis only compares first coordinates. -/
theorem det_pos_of_sub_smul_mem_span_image_fst_lt (b : Basis (ι × κ) R M) {v : ι × κ → M}
    {c : ι × κ → R} (hc : ∀ p, 0 < c p)
    (hv : ∀ p, v p - c p • b p ∈ span R (b '' {r | r.1 < p.1})) : 0 < b.det v := by
  -- the order on the second factor is irrelevant; choose one by transport along `Fin`
  let : LinearOrder κ := LinearOrder.lift' (Fintype.equivFin κ) (Fintype.equivFin κ).injective
  have hdet := b.det_reindex_symm v (toLex (α := ι × κ)).symm
  rw [Equiv.symm_symm] at hdet
  rw [← hdet]
  convert (b.reindex toLex).det_pos_of_sub_smul_mem_span (fun p ↦ hc (ofLex p)) fun p ↦ ?_
  refine span_mono ?_ (by simpa using hv (ofLex p))
  rintro _ ⟨q, hq, rfl⟩
  exact ⟨toLex q, Prod.Lex.toLex_lt_toLex.2 (.inl hq), by simp⟩

end Prod

section Flag

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
  (b : Basis (Fin n) R M) {f : M →ₗ[R] M} {c : Fin n → R}

/-- On and below the diagonal, the matrix of an endomorphism `f` that is triangular with respect to
the flag of `b`, with diagonal coefficients `c`, is that of `j ↦ c j • b j`. -/
private theorem toMatrix_apply_of_sub_smul_mem_flag
    (h : ∀ j, f (b j) - c j • b j ∈ b.flag j.castSucc) {i j : Fin n} (hji : j ≤ i) :
    LinearMap.toMatrix b b f i j = c j * Finsupp.single j 1 i := by
  have hi := b.mem_flag_iff_repr_eq_zero.mp (h j) i (Fin.castSucc_le_castSucc_iff.mpr hji)
  simp only [map_sub, map_smul, repr_self, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
    sub_eq_zero] at hi
  rw [LinearMap.toMatrix_apply, hi]

/-- The matrix of an endomorphism `f` in a basis `b` is upper triangular when each `f (b j)` is a
multiple of `b j` modulo the span `b.flag j.castSucc` of the earlier basis vectors. -/
theorem toMatrix_isUpperTriangular_of_sub_smul_mem_flag
    (h : ∀ j, f (b j) - c j • b j ∈ b.flag j.castSucc) :
    (LinearMap.toMatrix b b f).IsUpperTriangular := by
  -- `IsUpperTriangular` is `BlockTriangular · id`, so its hypothesis `id j < id i` is `j < i`
  intro i j (hji : j < i)
  rw [toMatrix_apply_of_sub_smul_mem_flag b h hji.le, Finsupp.single_eq_of_ne hji.ne', mul_zero]

/-- The diagonal of the matrix of an endomorphism `f` in a basis `b` is `c` when each
`f (b j) - c j • b j` lies in the span `b.flag j.castSucc` of the earlier basis vectors. -/
theorem toMatrix_apply_self_of_sub_smul_mem_flag
    (h : ∀ j, f (b j) - c j • b j ∈ b.flag j.castSucc) (i : Fin n) :
    LinearMap.toMatrix b b f i i = c i := by
  rw [toMatrix_apply_of_sub_smul_mem_flag b h le_rfl, Finsupp.single_eq_same, mul_one]

end Flag

end Module.Basis

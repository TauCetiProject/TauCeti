/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Flag
public import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Block

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

## Main results

* `Module.Basis.flag_eq_of_triangular`: a basis triangular with respect to `e` has the same flag
  as `e`.
* `Module.Basis.det_eq_prod_of_sub_smul_mem_span`: the determinant of a triangular family is the
  product of its diagonal coefficients.
* `Module.Basis.det_pos_of_sub_smul_mem_span`: over an ordered ring, a triangular family with
  positive diagonal coefficients has positive determinant.
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

variable {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
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

end Module.Basis

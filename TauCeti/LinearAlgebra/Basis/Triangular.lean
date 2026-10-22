/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Flags of triangular bases

Let `e` and `b` be bases of a vector space indexed by `Fin n`, with `b` triangular with respect
to `e`: each `b l` is a combination of `e 0, …, e l`. Then `b` and `e` define the same flag of
subspaces, and a vector in the span of `e 0, …, e (j - 1)` has vanishing `b`-coordinates from the
`j`-th on.

## Main results

* `Module.Basis.span_image_Iio_eq_of_triangular`: a basis triangular with respect to `e` has the
  same flag as `e`.
* `Module.Basis.repr_eq_zero_of_mem_span_image_Iio`: hence a vector in the span of
  `e 0, …, e (j - 1)` has vanishing coordinates from the `j`-th on in any such basis.
-/

public section

open Submodule

namespace Module.Basis

variable {K E : Type*} [DivisionRing K] [AddCommGroup E] [Module K E] {n : ℕ}

/-- A basis `b` that is triangular with respect to a basis `e` (each `b l` is a combination of
`e 0, …, e l`) has the same flag as `e`: `b 0, …, b (j - 1)` and `e 0, …, e (j - 1)` span the
same subspace. -/
theorem span_image_Iio_eq_of_triangular (b : Basis (Fin n) K E) {e : Basis (Fin n) K E}
    (htri : ∀ l i, l < i → e.repr (b l) i = 0) (j : Fin n) :
    span K (b '' Set.Iio j) = span K (e '' Set.Iio j) := by
  have := e.finiteDimensional_of_finite
  refine eq_of_le_of_finrank_eq (span_le.2 (Set.image_subset_iff.2 fun l hl ↦ ?_)) ?_
  · rw [Set.mem_preimage, SetLike.mem_coe, Basis.mem_span_image]
    intro i hi
    by_contra hil
    exact (Finsupp.mem_support_iff.1 hi) (htri l i (lt_of_lt_of_le hl (not_lt.1 hil)))
  -- The two spans have the same dimension.
  rw [Set.image_eq_range, Set.image_eq_range]
  exact (finrank_span_eq_card (b.linearIndependent.comp _ Subtype.val_injective)).trans
    (finrank_span_eq_card (e.linearIndependent.comp _ Subtype.val_injective)).symm

/-- If a basis `b` is triangular with respect to a basis `e` (each `b l` is a combination of
`e 0, …, e l`), then a vector in the span of `e 0, …, e (j - 1)` has vanishing coordinates in `b`
from the `j`-th on. -/
theorem repr_eq_zero_of_mem_span_image_Iio (b : Basis (Fin n) K E) {e : Basis (Fin n) K E}
    (htri : ∀ l i, l < i → e.repr (b l) i = 0) {j : Fin n} {v : E}
    (hv : v ∈ span K (e '' Set.Iio j)) {i : Fin n} (hji : j ≤ i) : b.repr v i = 0 := by
  rw [← b.span_image_Iio_eq_of_triangular htri, Basis.mem_span_image] at hv
  by_contra hvi
  exact absurd (hv (Finsupp.mem_support_iff.2 hvi)) (not_lt.2 hji)

end Module.Basis

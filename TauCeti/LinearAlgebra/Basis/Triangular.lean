/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Flags of triangular bases

Let `e` and `b` be bases of a vector space indexed by `Fin n`, with `b` triangular with respect
to `e`: each `b l` is a combination of `e 0, …, e l`. Then `b` and `e` define the same flag of
subspaces in the sense of `Module.Basis.flag`. Combined with
`Module.Basis.mem_flag_iff_repr_eq_zero`, a vector in the span of `e 0, …, e (j - 1)` has
vanishing `b`-coordinates from the `j`-th on.

## Main results

* `Module.Basis.flag_eq_of_triangular`: a basis triangular with respect to `e` has the same flag
  as `e`.
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

end Module.Basis

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Dimension vanishing for Gram determinants

In a finite-dimensional real or complex semi-inner-product space `E`, any family of vectors indexed
by a finite type of cardinality strictly greater than `finrank 𝕜 E` is linearly dependent, so its
Gram determinant vanishes (`Matrix.det_gram_eq_zero_of_finrank_lt`).

## Main results

* `Matrix.det_gram_eq_zero_of_finrank_lt`: `(gram 𝕜 v).det = 0` when
  `Module.finrank 𝕜 E < Fintype.card n` and `Module.Finite 𝕜 E`.
-/

public section

namespace Matrix

/-- In a finite-dimensional semi-inner-product space of dimension smaller than the cardinality of
the index type, every Gram determinant vanishes. `Module.Finite 𝕜 E` is required because
`Module.finrank` defaults to `0` in infinite dimension. -/
theorem det_gram_eq_zero_of_finrank_lt {𝕜 E n : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Module.Finite 𝕜 E]
    [Fintype n] [DecidableEq n] (h : Module.finrank 𝕜 E < Fintype.card n) (v : n → E) :
    (gram 𝕜 v).det = 0 := by
  by_contra h0
  exact h.not_ge (linearIndependent_of_det_gram_ne_zero h0).fintype_card_le_finrank

end Matrix

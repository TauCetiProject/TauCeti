/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import TauCeti.Algebra.BigOperators.Finset.Fiber

/-!
# Exponent sums at the prevertices

For distinct prevertices `a` the sum of the exponents `e` over the prevertices equal to `a k` is
just `e k`. In particular, exponents greater than `-1` make every such sum greater than `-1`,
which is the finiteness hypothesis the boundary lemmas of the Schwarz--Christoffel formula ask
for.

## Main results

* `TauCeti.neg_one_lt_sum_filter_apply_eq_apply`: exponents greater than `-1` give sums over the
  prevertices equal to `a k` greater than `-1`.
-/

public section

namespace TauCeti

/-- For distinct prevertices and exponents greater than `-1`, the sum of the exponents over the
prevertices equal to `a k` is greater than `-1`. -/
lemma neg_one_lt_sum_filter_apply_eq_apply {ι : Type*} [Fintype ι] (a e : ι → ℝ)
    (ha : Function.Injective a) (he : ∀ k, -1 < e k) (k : ι) :
    -1 < ∑ l with a l = a k, e l := by
  rw [sum_filter_eq_apply_of_injective ha e k]
  exact he k

end TauCeti

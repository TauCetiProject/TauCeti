/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic

/-!
# Exponent sums at the prevertices

For strictly ordered prevertices `a` the prevertices are distinct, so the sum of the exponents `e`
over the prevertices equal to `a k` is just `e k`.  In particular, exponents greater than `-1`
make every such sum greater than `-1`, which is the finiteness hypothesis the boundary lemmas of
the Schwarz--Christoffel formula ask for.

## Main results

* `TauCeti.exponent_sum_at_eq`: the sum of the exponents at the prevertex `a k` is `e k`.
* `TauCeti.neg_one_lt_exponent_sum_at`: exponents greater than `-1` give exponent sums at each
  prevertex greater than `-1`.
-/

public section

namespace TauCeti

variable {n : ℕ}

/-- For strictly ordered prevertices, the sum of the exponents over the prevertices equal to
`a k` is the exponent `e k`. -/
lemma exponent_sum_at_eq (a e : Fin (n + 1) → ℝ) (ha : StrictMono a)
    (k : Fin (n + 1)) :
    ∑ l with a l = a k, e l = e k := by
  classical
  have hfilter : Finset.univ.filter (fun l ↦ a l = a k) = {k} := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ha.injective.eq_iff
  rw [hfilter, Finset.sum_singleton]

/-- For strictly ordered prevertices and exponents greater than `-1`, the exponent sum at every
prevertex is greater than `-1`. -/
lemma neg_one_lt_exponent_sum_at (a e : Fin (n + 1) → ℝ) (ha : StrictMono a)
    (he : ∀ k, -1 < e k) (k : Fin (n + 1)) :
    -1 < ∑ l with a l = a k, e l := by
  rw [exponent_sum_at_eq a e ha]
  exact he k

end TauCeti

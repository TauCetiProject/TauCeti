/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# A term-by-term lower bound, summed with an error budget

If every term of a family `a` is within `η'` below its counterpart in `d`, then summing over a
finite set accumulates that slack at most once per index, so the sum of `a` falls short of the sum
of `d` by at most `#s • η'`.

Stating the conclusion with an arbitrary `η` dominating `#s • η'`, rather than with `#s • η'`
itself, lets a caller fix an error budget first and choose `η'` afterwards — which is how the
bound is used when `η` is a prescribed `ε` and `η'` is solved for.

## Main results

* `Finset.sum_sub_le_sum_of_forall_sub_le`: the summed form of a term-by-term lower bound.
-/

public section

namespace Finset

/-- **A term-by-term lower bound, summed.** If every `a i` is within `η'` below `d i` on `s`, and
`η` dominates the accumulated slack `#s • η'`, then `∑ d - η ≤ ∑ a`.

Purely additive: no multiplication, no linearity and no strict monotonicity are used, so this
lives in an ordered additive group rather than an ordered ring. A caller working in a ring
rewrites the `nsmul` with `nsmul_eq_mul`. -/
theorem sum_sub_le_sum_of_forall_sub_le {ι M : Type*} [AddCommGroup M] [PartialOrder M]
    [IsOrderedAddMonoid M] {s : Finset ι} {d a : ι → M} {η η' : M}
    (ha : ∀ i ∈ s, d i - η' ≤ a i) (hη : s.card • η' ≤ η) :
    (∑ i ∈ s, d i) - η ≤ ∑ i ∈ s, a i := by
  have hlb := Finset.sum_le_sum ha
  rw [Finset.sum_sub_distrib, Finset.sum_const] at hlb
  exact (sub_le_sub_left hη _).trans hlb

end Finset

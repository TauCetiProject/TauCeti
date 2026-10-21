/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Finset.MulAntidiagonal
public import Mathlib.Data.Finset.SMulAntidiagonal

/-!
# Reindexing double sums over antidiagonals of a monoid acting on itself

For partially well-ordered sets `s`, `t`, `u` in an ordered cancellative commutative monoid, a
product over the triples `(a, b, c)` with `a * b * c = d` can be computed by splitting off `a`
first along a multiplication antidiagonal and then `b` along the antidiagonal of the action of
the monoid on itself, or the other way round. This reindexing underlies the compatibility of
convolution products of Hahn series with the action of Hahn series on Hahn modules.

## Main results

* `Finset.prod_sigma_smulAntidiagonal_left_comm`, `Finset.sum_sigma_vaddAntidiagonal_left_comm`:
  exchanging the first two indices of a double product (sum) over antidiagonals.

The bijection follows the proof of `HahnSeries.mul_assoc` in Mathlib's
`Mathlib/RingTheory/HahnSeries/Multiplication.lean`.
-/

public section

open Pointwise

namespace Finset

variable {α M : Type*} [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α] [CommMonoid M]
  {s t u : Set α}

/-- Exchanging the first two indices of a double product, where the inner products are over the
antidiagonals of the action of the monoid on itself. -/
@[to_additive /-- Exchanging the first two indices of a double sum, where the inner sums are over
the antidiagonals of the action of the monoid on itself. -/]
theorem prod_sigma_smulAntidiagonal_left_comm (hs : s.IsPWO) (ht : t.IsPWO) (hu : u.IsPWO)
    (d : α) (F : α → α → α → M) :
    ∏ p ∈ (mulAntidiagonal hs (ht.smul hu) d).sigma fun p ↦
        SMulAntidiagonal p.2 (Set.SMulAntidiagonal.finite_of_isPWO ht hu p.2),
        F p.1.1 p.2.1 p.2.2 =
      ∏ p ∈ (SMulAntidiagonal d (Set.SMulAntidiagonal.finite_of_isPWO ht (hs.mul hu) d)).sigma
          fun p ↦ mulAntidiagonal hs hu p.2,
        F p.2.1 p.1.1 p.2.2 := by
  apply prod_nbij' (fun ⟨⟨i, _⟩, ⟨j, k⟩⟩ ↦ ⟨(j, i * k), (i, k)⟩)
    (fun ⟨⟨j, _⟩, ⟨i, k⟩⟩ ↦ ⟨(i, j * k), (j, k)⟩) <;>
    aesop (add safe [Set.mul_mem_mul, Set.smul_mem_smul]) (add simp [mul_left_comm])

end Finset

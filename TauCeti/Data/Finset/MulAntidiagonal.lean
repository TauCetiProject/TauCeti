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
# Reindexing double sums over multiplication antidiagonals

For partially well-ordered sets `s`, `t`, `u` in an ordered cancellative commutative monoid, a
product over the triples `(a, b, c)` with `a * b * c = d` can be computed by first splitting `d`
as `a * (b * c)` or as `(a * b) * c`, and also by splitting off `b` first instead of `a`. These
reindexings underlie associativity-type identities for convolution products of Hahn series.

## Main results

* `Finset.smulAntidiagonal_eq_mulAntidiagonal`, `Finset.vaddAntidiagonal_eq_antidiagonal`:
  for a monoid acting on itself, the scalar (vector) antidiagonal is the multiplication (addition)
  antidiagonal.
* `Finset.prod_sigma_mulAntidiagonal_assoc`, `Finset.sum_sigma_antidiagonal_assoc`:
  reassociating a double product (sum) over antidiagonals.
* `Finset.prod_sigma_mulAntidiagonal_left_comm`, `Finset.sum_sigma_antidiagonal_left_comm`:
  exchanging the first two indices of a double product (sum) over antidiagonals.

The bijections follow the proof of `HahnSeries.mul_assoc` in Mathlib's
`Mathlib/RingTheory/HahnSeries/Multiplication.lean`.
-/

public section

open Pointwise

namespace Finset

variable {α M : Type*} [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α] [CommMonoid M]
  {s t u : Set α}

/-- For a monoid acting on itself by multiplication, the scalar antidiagonal of two partially
well-ordered sets is their multiplication antidiagonal. -/
@[to_additive /-- For an additive monoid acting on itself by addition, the vector antidiagonal of
two partially well-ordered sets is their addition antidiagonal. -/]
theorem smulAntidiagonal_eq_mulAntidiagonal (hs : s.IsPWO) (ht : t.IsPWO) (a : α) :
    SMulAntidiagonal a (Set.SMulAntidiagonal.finite_of_isPWO hs ht a) =
      mulAntidiagonal hs ht a := by
  ext
  simp

/-- Reassociating a double product over antidiagonals: the products indexed by `(a, (b, c))` and
by `((a, b), c)`, with `a * b * c = d`, agree. -/
@[to_additive /-- Reassociating a double sum over antidiagonals: the
sums indexed by `(a, (b, c))` and by `((a, b), c)`, with `a + b + c = d`, agree. -/]
theorem prod_sigma_mulAntidiagonal_assoc (hs : s.IsPWO) (ht : t.IsPWO) (hu : u.IsPWO) (d : α)
    (F : α → α → α → M) :
    ∏ p ∈ (mulAntidiagonal hs (ht.mul hu) d).sigma fun p ↦ mulAntidiagonal ht hu p.2,
        F p.1.1 p.2.1 p.2.2 =
      ∏ p ∈ (mulAntidiagonal (hs.mul ht) hu d).sigma fun p ↦ mulAntidiagonal hs ht p.1,
        F p.2.1 p.2.2 p.1.2 := by
  apply prod_nbij' (fun ⟨⟨i, _⟩, ⟨j, k⟩⟩ ↦ ⟨(i * j, k), (i, j)⟩)
    (fun ⟨⟨_, k⟩, ⟨i, j⟩⟩ ↦ ⟨(i, j * k), (j, k)⟩) <;>
    aesop (add safe Set.mul_mem_mul) (add simp [mul_assoc])

/-- Exchanging the first two indices of a double product over antidiagonals: the products indexed
by `(a, (b, c))` and by `(b, (a, c))`, with `a * b * c = d`, agree. -/
@[to_additive /-- Exchanging the first two indices of a double
sum over antidiagonals: the sums indexed by `(a, (b, c))` and by `(b, (a, c))`, with
`a + b + c = d`, agree. -/]
theorem prod_sigma_mulAntidiagonal_left_comm (hs : s.IsPWO) (ht : t.IsPWO) (hu : u.IsPWO) (d : α)
    (F : α → α → α → M) :
    ∏ p ∈ (mulAntidiagonal hs (ht.mul hu) d).sigma fun p ↦ mulAntidiagonal ht hu p.2,
        F p.1.1 p.2.1 p.2.2 =
      ∏ p ∈ (mulAntidiagonal ht (hs.mul hu) d).sigma fun p ↦ mulAntidiagonal hs hu p.2,
        F p.2.1 p.1.1 p.2.2 := by
  apply prod_nbij' (fun ⟨⟨i, _⟩, ⟨j, k⟩⟩ ↦ ⟨(j, i * k), (i, k)⟩)
    (fun ⟨⟨j, _⟩, ⟨i, k⟩⟩ ↦ ⟨(i, j * k), (j, k)⟩) <;>
    aesop (add safe Set.mul_mem_mul) (add simp [mul_left_comm])

end Finset

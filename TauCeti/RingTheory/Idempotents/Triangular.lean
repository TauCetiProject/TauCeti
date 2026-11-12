/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Nilpotent.Defs
public import TauCeti.Order.Preorder.Finite
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Strictly triangular elements relative to orthogonal idempotents

Let `e : I → R` be a complete family of orthogonal idempotents of a semiring `R`, indexed by a
finite preordered set `I`. It splits every `a : R` into components `e j * a * e i`, the part of
`a` that sends the summand of `i` to the summand of `j`. We call `a` *strictly triangular* when
its component from `i` to `j` vanishes unless `i < j`, so that `a` only moves strictly up in `I`
(`TauCeti.IsStrictlyTriangular`).

The typical example is a cube of chain complexes, indexed by the subsets `I = Finset (Fin n)`
ordered by inclusion: the arrows of the cube between distinct vertices strictly increase the vertex,
while the internal differentials of the vertices are diagonal. Iterating such an element moves
along strictly increasing chains of `I`, which are shorter than the cardinality of `I`. Hence
strictly triangular elements are nilpotent, with `a ^ Fintype.card I = 0`
(`TauCeti.IsStrictlyTriangular.pow_card_eq_zero`), and over a ring `1 + a` is a unit. This is what
makes homological perturbation along the arrows of a cube a finite computation.

The proof of nilpotence uses the rank `#{k | k < i}`, which strictly increases along `<`
(`TauCeti.card_filter_lt_lt_card_filter_lt`): by induction, the component of `a ^ n` from `i` to
`j` vanishes unless the rank of `j` exceeds the rank of `i` by at least `n`.

## Main definitions

* `TauCeti.IsStrictlyTriangular`: the components of `a` vanish except from `i` to `j > i`.

## Main results

* `CompleteOrthogonalIdempotents.mul_mul_mul_eq_sum`: the component of a product is the sum over
  intermediate indices of the products of components.
* `TauCeti.IsStrictlyTriangular.mul`: strictly triangular elements are closed under products, and
  `TauCeti.IsStrictlyTriangular.mul_mul_mul_eq_sum_Ioo` restricts the intermediate indices of such
  a product to the open interval `Finset.Ioo i j`.
* `TauCeti.IsStrictlyTriangular.pow_card_eq_zero`: a strictly triangular element `a` has
  `a ^ Fintype.card I = 0`; in particular, over a ring, `1 + a` is a unit
  (`TauCeti.IsStrictlyTriangular.isUnit_one_add`).
-/

public section

open Finset

namespace CompleteOrthogonalIdempotents

variable {R I : Type*} [Semiring R] [Fintype I] {e : I → R}

/-- The component of a product relative to a complete family of orthogonal idempotents is the sum,
over the intermediate indices, of the products of the components of the factors. -/
theorem mul_mul_mul_eq_sum (he : CompleteOrthogonalIdempotents e) (a b : R) (i j : I) :
    e j * (a * b) * e i = ∑ k, e j * a * e k * (e k * b * e i) := by
  calc e j * (a * b) * e i = e j * (a * (∑ k, e k) * b) * e i := by
        rw [he.complete, mul_one]
    _ = ∑ k, e j * a * (e k * e k) * b * e i := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc, (he.idem _).eq]
    _ = ∑ k, e j * a * e k * (e k * b * e i) := by
        simp only [mul_assoc]

end CompleteOrthogonalIdempotents

namespace TauCeti

variable {R I : Type*} [Preorder I]

section Semiring

variable [Semiring R] {e : I → R} {a b : R}

/-- An element `a` of a semiring is **strictly triangular** with respect to a family `e` indexed
by a preordered set when its component `e j * a * e i`, from the summand of `i` to the summand of
`j`, vanishes unless `i < j`. For a complete family of orthogonal idempotents this says that `a`
maps each summand into the sum of the strictly larger summands. -/
def IsStrictlyTriangular (e : I → R) (a : R) : Prop :=
  ∀ ⦃i j : I⦄, ¬i < j → e j * a * e i = 0

/-- The defining property of a strictly triangular element. -/
theorem isStrictlyTriangular_iff :
    IsStrictlyTriangular e a ↔ ∀ ⦃i j : I⦄, ¬i < j → e j * a * e i = 0 := Iff.rfl

namespace IsStrictlyTriangular

/-- The component of a strictly triangular element from `i` to `j` vanishes unless `i < j`. -/
@[simp]
theorem mul_mul_eq_zero (ha : IsStrictlyTriangular e a) {i j : I} (h : ¬i < j) :
    e j * a * e i = 0 :=
  ha h

/-- Zero is strictly triangular. -/
@[simp]
theorem zero : IsStrictlyTriangular e (0 : R) := fun _ _ _ ↦ by
  rw [mul_zero, zero_mul]

/-- A sum of strictly triangular elements is strictly triangular. -/
theorem add (ha : IsStrictlyTriangular e a) (hb : IsStrictlyTriangular e b) :
    IsStrictlyTriangular e (a + b) := fun _ _ h ↦ by
  rw [mul_add, add_mul, ha h, hb h, add_zero]

/-- A finite sum of strictly triangular elements is strictly triangular. -/
theorem sum {ι : Type*} {s : Finset ι} {f : ι → R} (hf : ∀ k ∈ s, IsStrictlyTriangular e (f k)) :
    IsStrictlyTriangular e (∑ k ∈ s, f k) := fun _ _ h ↦ by
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_eq_zero fun k hk ↦ hf k hk h

/-- A strictly triangular element stays strictly triangular after multiplication on the right by
an element commuting with the family, that is, by a diagonal element. -/
theorem mul_of_forall_commute (ha : IsStrictlyTriangular e a) (hb : ∀ k, Commute (e k) b) :
    IsStrictlyTriangular e (a * b) := fun i j h ↦ by
  rw [mul_assoc, mul_assoc, ← (hb i).eq, ← mul_assoc, ← mul_assoc, ha h, zero_mul]

/-- A strictly triangular element stays strictly triangular after multiplication on the left by
an element commuting with the family, that is, by a diagonal element. -/
theorem mul_of_forall_commute_left (hb : ∀ k, Commute (e k) b) (ha : IsStrictlyTriangular e a) :
    IsStrictlyTriangular e (b * a) := fun i j h ↦ by
  rw [← mul_assoc, (hb j).eq, mul_assoc b, mul_assoc b, ha h, mul_zero]

variable [Fintype I]

/-- Strictly triangular elements relative to a complete family of orthogonal idempotents are
closed under products. -/
theorem mul (he : CompleteOrthogonalIdempotents e) (ha : IsStrictlyTriangular e a)
    (hb : IsStrictlyTriangular e b) : IsStrictlyTriangular e (a * b) := fun i j h ↦ by
  rw [he.mul_mul_mul_eq_sum]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  by_cases hkj : k < j
  · rw [hb fun hik ↦ h (hik.trans hkj), mul_zero]
  · rw [ha hkj, zero_mul]

/-- The component of a product of two strictly triangular elements from `i` to `j` only involves
the intermediate indices strictly between `i` and `j`. -/
theorem mul_mul_mul_eq_sum_Ioo [LocallyFiniteOrder I] (he : CompleteOrthogonalIdempotents e)
    (ha : IsStrictlyTriangular e a) (hb : IsStrictlyTriangular e b) (i j : I) :
    e j * (a * b) * e i = ∑ k ∈ Ioo i j, e j * a * e k * (e k * b * e i) := by
  rw [he.mul_mul_mul_eq_sum]
  refine (Finset.sum_subset (Finset.subset_univ _) fun k _ hk ↦ ?_).symm
  rw [Finset.mem_Ioo, not_and_or] at hk
  rcases hk with hik | hkj
  · rw [hb hik, mul_zero]
  · rw [ha hkj, zero_mul]

/-- The component of `a ^ n` from `i` to `j` vanishes unless the rank of `j` exceeds the rank of
`i` by at least `n`. -/
private theorem mul_pow_mul_eq_zero [DecidableRel ((· < ·) : I → I → Prop)]
    (he : CompleteOrthogonalIdempotents e) (ha : IsStrictlyTriangular e a) (n : ℕ) {i j : I}
    (h : #{k | k < j} < #{k | k < i} + n) : e j * a ^ n * e i = 0 := by
  induction n generalizing i with
  | zero =>
    have hij : j ≠ i := by
      rintro rfl
      omega
    rw [pow_zero, mul_one]
    exact he.ortho hij
  | succ n ih =>
    rw [pow_succ, he.mul_mul_mul_eq_sum]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    by_cases hik : i < k
    · have := card_filter_lt_lt_card_filter_lt hik
      rw [ih (by omega), zero_mul]
    · rw [ha hik, mul_zero]

/-- **Strictly triangular elements are nilpotent.** An element which is strictly triangular
relative to a complete family of orthogonal idempotents indexed by a finite preordered set `I`
satisfies `a ^ Fintype.card I = 0`. -/
theorem pow_card_eq_zero (he : CompleteOrthogonalIdempotents e) (ha : IsStrictlyTriangular e a) :
    a ^ Fintype.card I = 0 := by
  classical
  have hc (i j : I) : e j * a ^ Fintype.card I * e i = 0 :=
    mul_pow_mul_eq_zero he ha _ (by have := card_filter_lt_lt_card (I := I) j; omega)
  calc a ^ Fintype.card I = (∑ j, e j) * a ^ Fintype.card I * ∑ i, e i := by
        rw [he.complete, one_mul, mul_one]
    _ = 0 := by
        simp only [Finset.sum_mul, Finset.mul_sum, hc, Finset.sum_const_zero]

/-- A strictly triangular element is nilpotent. -/
theorem isNilpotent (he : CompleteOrthogonalIdempotents e) (ha : IsStrictlyTriangular e a) :
    IsNilpotent a :=
  ⟨_, ha.pow_card_eq_zero he⟩

end IsStrictlyTriangular

end Semiring

namespace IsStrictlyTriangular

variable [Ring R] {e : I → R} {a b : R}

/-- The negative of a strictly triangular element is strictly triangular. -/
theorem neg (ha : IsStrictlyTriangular e a) : IsStrictlyTriangular e (-a) := fun _ _ h ↦ by
  rw [mul_neg, neg_mul, ha h, neg_zero]

/-- A difference of strictly triangular elements is strictly triangular. -/
theorem sub (ha : IsStrictlyTriangular e a) (hb : IsStrictlyTriangular e b) :
    IsStrictlyTriangular e (a - b) := by
  rw [sub_eq_add_neg]
  exact ha.add hb.neg

/-- For a strictly triangular `a`, the element `1 + a` is a unit. -/
theorem isUnit_one_add [Fintype I] (he : CompleteOrthogonalIdempotents e)
    (ha : IsStrictlyTriangular e a) : IsUnit (1 + a) :=
  (ha.isNilpotent he).isUnit_one_add

end IsStrictlyTriangular

end TauCeti

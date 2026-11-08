/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finsupp.Weight

/-!
# Multisets of exponent vectors

Mathlib's `Finsupp.toMultiset` sends an exponent vector `e : α →₀ ℕ` to the multiset in which
each `a` occurs `e a` times. Its cardinality is the total degree of `e`. This file also computes it
on exponent vectors built from unit steps `Finsupp.single a 1`: adding one unit step conses its
index, and a sum of unit steps along a finite family is the multiset of values of the family.
The coefficients of such a sum are the letter counts of the family: the number of indices at
which it takes each value.

## Main results

* `Finsupp.card_toMultiset_eq_degree`: `card (toMultiset e) = e.degree`.
* `Finsupp.toMultiset_add_single_one`: `toMultiset (e + single a 1) = a ::ₘ toMultiset e`.
* `Finsupp.toMultiset_sum_single_one`: `toMultiset (∑ i ∈ s, single (p i) 1) = s.val.map p`.
* `Finsupp.sum_single_one_apply`: along a family `f` indexed by a finite type, the coefficient of
  `a` in `∑ t, single (f t) 1` is the number of indices `t` with `f t = a`;
  `Finsupp.sum_sum_single_one_apply` and `Finsupp.sum_single_one_apply_ne_zero_iff` record that
  these letter counts sum to the number of indices and are nonzero exactly at the values of `f`.

The same unit steps summed along a list, with coefficients in any additive commutative monoid
with one, count the occurrences of each letter; in characteristic zero these counts determine a
constant list.

* `List.sum_map_single_one_apply`: `(l.map fun k ↦ single k 1).sum a = l.count a`.
* `List.eq_replicate_of_sum_map_single_one_eq`: a list whose letter counts are those of `m`
  copies of `i` is `m` copies of `i`.
-/

public section

namespace Finsupp

/-- The number of letters of the monomial with exponent vector `d` is its total degree. This is
not a `simp` lemma: `Finsupp.card_toMultiset` already rewrites the left-hand side to
`d.sum fun _ => id`, so tagging it would leave it out of simp-normal form. -/
theorem card_toMultiset_eq_degree {α : Type*} (d : α →₀ ℕ) :
    Multiset.card d.toMultiset = d.degree := by
  rw [card_toMultiset, degree_apply]
  rfl

/-- Adding one unit step at `a` to an exponent vector conses `a` onto its multiset. -/
theorem toMultiset_add_single_one {α : Type*} (e : α →₀ ℕ) (a : α) :
    toMultiset (e + single a 1) = a ::ₘ toMultiset e := by
  simp [toMultiset_add, add_comm]

/-- The multiset of a sum of unit steps along a family `p` indexed by a finset `s` is the
multiset of the values of `p` on `s`. -/
theorem toMultiset_sum_single_one {α ι : Type*} (s : Finset ι) (p : ι → α) :
    toMultiset (∑ i ∈ s, single (p i) 1) = s.val.map p := by
  simpa [toMultiset_sum, one_nsmul, Finset.sum_map_val] using
    Multiset.sum_map_singleton (s.val.map p)

/-- The letter counts of a family: the coefficient of `a` in `∑ₜ single (f t) 1` is the
number of indices `t` with `f t = a`. -/
theorem sum_single_one_apply {α ι : Type*} [Fintype ι] [DecidableEq α] (f : ι → α) (a : α) :
    (∑ t, single (f t) 1 : α →₀ ℕ) a = (Finset.univ.filter fun t => f t = a).card := by
  simp [finsetSum_apply, single_apply]

/-- The letter counts of a family with values in `F` sum, over `F`, to the number of indices. -/
theorem sum_sum_single_one_apply {α ι : Type*} [Fintype ι] {f : ι → α} {F : Finset α}
    (hf : ∀ t, f t ∈ F) : ∑ a ∈ F, (∑ t, single (f t) 1 : α →₀ ℕ) a = Fintype.card ι := by
  classical
  simp only [sum_single_one_apply]
  exact (Finset.card_eq_sum_card_fiberwise fun t _ => hf t).symm

/-- A value is taken by a family exactly when its letter count is nonzero. -/
theorem sum_single_one_apply_ne_zero_iff {α ι : Type*} [Fintype ι] {f : ι → α} {a : α} :
    (∑ t, single (f t) 1 : α →₀ ℕ) a ≠ 0 ↔ ∃ t, f t = a := by
  classical
  simp [sum_single_one_apply]

end Finsupp

namespace List

variable {α R : Type*} [AddCommMonoidWithOne R]

/-- Summing the unit steps `single k 1` along a list counts the occurrences of each letter. -/
theorem sum_map_single_one_apply [DecidableEq α] (l : List α) (a : α) :
    (l.map fun k => Finsupp.single k (1 : R)).sum a = l.count a := by
  induction l with
  | nil => simp
  | cons k l ih =>
    simp only [map_cons, sum_cons, Finsupp.add_apply, ih, count_cons, Finsupp.single_apply]
    split_ifs <;> simp_all [add_comm]

/-- In characteristic zero, a list whose sum of unit steps is `m` times the unit step at `i` is
the list of `m` copies of `i`. -/
theorem eq_replicate_of_sum_map_single_one_eq [CharZero R] {l : List α} {i : α} {m : ℕ}
    (hl : (l.map fun k => Finsupp.single k (1 : R)).sum = Finsupp.single i (m : R)) :
    l = replicate m i := by
  classical
  have hcount : ∀ j, (l.count j : R) = Finsupp.single i (m : R) j := fun j => by
    rw [← hl, sum_map_single_one_apply]
  have hall : ∀ j ∈ l, j = i := by
    intro j hj
    by_contra hji
    have := hcount j
    rw [Finsupp.single_eq_of_ne hji, Nat.cast_eq_zero] at this
    exact (count_pos_iff.2 hj).ne' this
  have hi := hcount i
  rw [Finsupp.single_eq_same, Nat.cast_inj, count_eq_length.2 fun j hj => (hall j hj).symm] at hi
  exact eq_replicate_iff.2 ⟨hi, hall⟩

end List

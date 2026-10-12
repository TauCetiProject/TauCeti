/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Finset.prod_multiset_map_count` and `Finset.sum_count_eq_card`, the two counting identities
-- behind the character and the total degree of a multiset weight.
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
-- `Sym.equivNatSumOfFintype`, the correspondence between unordered tuples and multiplicity
-- vectors.
public import Mathlib.Data.Finsupp.Multiset
-- The characters `TauCeti.weightChar` of a split torus.
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Basic
-- `TauCeti.Sym.ofFn`, the unordered tuple underlying an ordered one.
public import TauCeti.Data.Sym.Basic

/-!
# The weight of a multiset

A weight of the diagonal torus of `GL n k` is an integer vector `l : Fin n → ℤ`, and a multiset `s`
over `Fin n` carries one: its **multiplicity vector** `TauCeti.weightOfMultiset s`, the vector
whose `i`-th entry is the number of times `i` occurs in `s`. This file is the combinatorics of that
vector — the part of the weight theory of the symmetric powers of the standard representation that
mentions no representation.

There are three facts. A multiset over `Fin n` is recovered from its multiplicities, so the
labelling is injective; the entries are nonnegative and sum to the cardinality; and conversely
every nonnegative vector of total degree `d` is the multiplicity vector of an unordered `d`-tuple,
which is `Sym.equivNatSumOfFintype` read in `ℤ`. Together they say that the multiplicity vectors of
the elements of `Sym (Fin n) d` are exactly the exponent vectors of the degree-`d` monomials in `n`
variables. Finally, the torus character of a multiset weight is the product of the entries the
multiset lists, repetitions included, which is the scalar by which a diagonal matrix acts on the
corresponding product of standard basis vectors.

The weight of the unordered tuple of an **ordered** tuple `p : Fin d → Fin n` — its *content* — is
read off `p` directly: the multiplicity of `j` is the number of places at which `p` takes the value
`j`, and `TauCeti.sum_weightOfMultiset_ofFn` counts the entries whose values lie in any finite
set. Its initial-segment form compares two contents in the dominance order.

The subset counterpart, the `0`/`1` indicator `TauCeti.weightOfSubset` carried by a `d`-element
subset, is in `TauCeti.RepresentationTheory.ClassicalGroups.Weight.ExteriorPower` beside its one
consumer.

## Main definitions

* `TauCeti.weightOfMultiset`: the weight of a multiset over `Fin n`, its multiplicity vector.

## Main results

* `TauCeti.weightOfMultiset_injective`: **a multiset is recovered from its weight.**
* `TauCeti.exists_sym_weightOfMultiset_eq_iff`: **the multiplicity vectors of the unordered
  `d`-tuples over `Fin n` are exactly the nonnegative integer vectors summing to `d`.**
* `TauCeti.weightChar_weightOfMultiset`: **the torus character of a multiset weight** is the
  product of the entries it lists.
* `TauCeti.weightOfMultiset_ofFn_apply`: **the content of an ordered tuple counts the places at
  which it takes each value**, and `TauCeti.sum_weightOfMultiset_ofFn`: the multiplicities in a
  finite set count the entries valued in that set. `TauCeti.sum_weightOfMultiset_ofFn_filter_val_lt`
  specializes this to values below a bound.

## Implementation notes

The weight takes a bare `Multiset (Fin n)` rather than an element of `Sym (Fin n) d`: nothing in
the definition or in its injectivity uses the cardinality, and the consumers apply it to the
underlying multiset of a basis index. The cardinality reappears only in
`TauCeti.sum_weightOfMultiset`.

The vector itself is `Multiset.toFinsupp` read in `ℤ`, but it is spelled as a plain function rather
than through that equivalence because a weight is a plain function `Fin n → ℤ`: routing it through
a `Finsupp` coercion would leave every rewrite in the consuming files fighting the coercion for no
gain.
-/

public section

universe u

namespace TauCeti

/-- The **weight of a multiset** over `Fin n`: its multiplicity vector.  This is the weight carried
by the product of the standard basis vectors it lists. -/
def weightOfMultiset {n : ℕ} (s : Multiset (Fin n)) : Fin n → ℤ := fun i => Multiset.count i s

/-- The defining formula for `TauCeti.weightOfMultiset`. -/
@[simp]
theorem weightOfMultiset_apply {n : ℕ} (s : Multiset (Fin n)) (i : Fin n) :
    weightOfMultiset s i = Multiset.count i s :=
  (rfl)

/-- Multiplicities are nonnegative, so the weights of a symmetric power are. -/
theorem weightOfMultiset_nonneg {n : ℕ} (s : Multiset (Fin n)) (i : Fin n) :
    0 ≤ weightOfMultiset s i :=
  Int.natCast_nonneg _

/-- **A multiset is recovered from its weight**, a multiset over `Fin n` being determined by its
multiplicities. -/
theorem weightOfMultiset_injective {n : ℕ} : Function.Injective (weightOfMultiset (n := n)) :=
  fun _ _ h => Multiset.count_injective (funext fun i => Nat.cast_injective (congrFun h i))

/-- The weight of a multiset has total degree its cardinality: the weights of `Symᵈ(kⁿ)` all lie
in degree `d`. -/
theorem sum_weightOfMultiset {n : ℕ} (s : Multiset (Fin n)) :
    ∑ i, weightOfMultiset s i = Multiset.card s := by
  simp only [weightOfMultiset_apply]
  rw [← Nat.cast_sum, Multiset.sum_count_eq_card fun a _ => Finset.mem_univ a]

/-- **The weights of `Symᵈ(kⁿ)` are the exponent vectors of the degree-`d` monomials in `n`
variables**: an integer vector is the multiplicity vector of an unordered `d`-tuple over `Fin n`
exactly when it is nonnegative and sums to `d`. -/
theorem exists_sym_weightOfMultiset_eq_iff {n d : ℕ} (l : Fin n → ℤ) :
    (∃ s : Sym (Fin n) d, weightOfMultiset (s : Multiset (Fin n)) = l) ↔
      (∀ i, 0 ≤ l i) ∧ ∑ i, l i = d := by
  refine ⟨?_, ?_⟩
  · rintro ⟨s, rfl⟩
    exact ⟨weightOfMultiset_nonneg _, by rw [sum_weightOfMultiset, Sym.card_coe]⟩
  · rintro ⟨hnonneg, hsum⟩
    -- `Sym.equivNatSumOfFintype` turns the natural-valued multiplicity vector back into a multiset
    have hnat : ∑ i, (l i).toNat = d := by
      have : ((∑ i, (l i).toNat : ℕ) : ℤ) = (d : ℤ) := by
        rw [Nat.cast_sum, ← hsum]
        exact Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (hnonneg i)
      exact_mod_cast this
    refine ⟨(Sym.equivNatSumOfFintype (Fin n) d).symm ⟨_, hnat⟩, funext fun i => ?_⟩
    rw [weightOfMultiset_apply, ← Sym.coe_equivNatSumOfFintype_apply_apply,
      Equiv.apply_symm_apply]
    exact Int.toNat_of_nonneg (hnonneg i)

/-! ## The content of an ordered tuple -/

/-- **The multiplicity of `j` in the content of an ordered tuple is the number of places at which
the tuple takes the value `j`.** -/
theorem weightOfMultiset_ofFn_apply {n d : ℕ} (p : Fin d → Fin n) (j : Fin n) :
    weightOfMultiset (Sym.ofFn p : Multiset (Fin n)) j =
      ((Finset.univ.filter fun x => p x = j).card : ℤ) := by
  classical
  rw [weightOfMultiset_apply, Sym.count_coe_ofFn]

/-- The multiplicities of the values in `S` add up to the number of entries of the tuple
whose values lie in `S`. -/
theorem sum_weightOfMultiset_ofFn {n d : ℕ} (p : Fin d → Fin n) (S : Finset (Fin n)) :
    ∑ j ∈ S, weightOfMultiset (Sym.ofFn p : Multiset (Fin n)) j =
      ((Finset.univ.filter fun x => p x ∈ S).card : ℤ) := by
  classical
  have hmaps : ∀ x ∈ Finset.univ.filter fun x : Fin d => p x ∈ S, p x ∈ S := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Nat.cast_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hset : (Finset.univ.filter fun x : Fin d => p x ∈ S ∧ p x = j)
      = Finset.univ.filter fun x => p x = j :=
    Finset.filter_congr fun x _ => ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hj, h⟩⟩
  rw [weightOfMultiset_ofFn_apply, Finset.filter_filter, hset]

/-- **The partial sums of the content of an ordered tuple count its small values**: the
multiplicities of the values below `m` add up to the number of places at which the tuple takes
such a value.

This is the form in which the content of a tuple is compared with another in the dominance
order. -/
theorem sum_weightOfMultiset_ofFn_filter_val_lt {n d : ℕ} (p : Fin d → Fin n) (m : ℕ) :
    ∑ j ∈ Finset.univ.filter fun j : Fin n => (j : ℕ) < m,
        weightOfMultiset (Sym.ofFn p : Multiset (Fin n)) j =
      ((Finset.univ.filter fun x => (p x : ℕ) < m).card : ℤ) := by
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
    sum_weightOfMultiset_ofFn p (Finset.univ.filter fun j : Fin n => (j : ℕ) < m)

/-- **The torus character of a multiset weight** is the product of the entries it lists. -/
@[simp]
theorem weightChar_weightOfMultiset {k : Type u} [CommRing k] {n : ℕ} (s : Multiset (Fin n))
    (t : Fin n → kˣ) : weightChar k (weightOfMultiset s) t = (s.map t).prod := by
  rw [weightChar_apply, torusCharacter_def, Finset.prod_multiset_map_count]
  simp only [weightOfMultiset_apply, zpow_natCast]
  refine (Finset.prod_subset (Finset.subset_univ s.toFinset) fun i _ hi => ?_).symm
  rw [Multiset.mem_toFinset] at hi
  rw [Multiset.count_eq_zero_of_notMem hi, pow_zero]

end TauCeti

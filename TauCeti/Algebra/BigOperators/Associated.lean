/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Associated

/-!
# Products of primes none of which divides another

In a commutative monoid with zero, if each member of a finite family of primes divides `n`, and no
member of the family divides another, then the product of the family divides `n`. Mathlib's
`Finset.prod_primes_dvd` states this for a finset of primes in a cancellative monoid with trivial
units, and `Multiset.prod_primes_dvd` for a multiset counted up to association; this is the form
for an indexed family. For instance, in a polynomial ring over a domain the differences
`X j - X i` of pairs of variables with `i < j` are such a family, and their product is the
Vandermonde product.

## Main results

* `Finset.prod_primes_dvd_of_pairwise_not_dvd`: the product of a finite family of primes, each
  dividing `n` and none dividing another, divides `n`.
-/

public section

namespace Finset

variable {ι M : Type*} [CommMonoidWithZero M]

/-- The product of a finite family of primes, each of which divides `n` and none of which divides
another, divides `n`. -/
theorem prod_primes_dvd_of_pairwise_not_dvd {s : Finset ι} {f : ι → M} {n : M}
    (hprime : ∀ i ∈ s, Prime (f i)) (hndvd : (s : Set ι).Pairwise fun i j ↦ ¬ f i ∣ f j)
    (hdvd : ∀ i ∈ s, f i ∣ n) : ∏ i ∈ s, f i ∣ n := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    obtain ⟨w, rfl⟩ := ih (fun i hi ↦ hprime i (mem_insert_of_mem hi))
      (hndvd.mono (by simp)) fun i hi ↦ hdvd i (mem_insert_of_mem hi)
    -- `f a` divides `(∏ i ∈ s, f i) * w` but none of the `f i`, so it divides `w`.
    have hpa := hprime a (mem_insert_self a s)
    have hnot : ¬ f a ∣ ∏ i ∈ s, f i := hpa.not_dvd_finsetProd fun i hi ↦
      hndvd (mem_insert_self a s) (mem_insert_of_mem hi) fun hai ↦ ha (hai ▸ hi)
    obtain ⟨v, rfl⟩ := (hpa.dvd_or_dvd (hdvd a (mem_insert_self a s))).resolve_left hnot
    exact ⟨v, by ac_rfl⟩

end Finset

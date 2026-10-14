/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Orders.Basic
public import TauCeti.Combinatorics.PermutationTriple.ComputedInvariants
public import TauCeti.Combinatorics.PermutationTriple.Enumeration
import TauCeti.Combinatorics.PermutationTriple.Examples

/-!
# Enumerating connected triples with exact orders

The necessary degree and partition bounds on a triangle-group representation do not decide
whether all three generators can have prescribed exact orders. A finite search does:
`connectedTriplesWithExactOrders n a b c` lists every connected degree-`n` permutation triple
whose component orders are exactly `(a, b, c)`. It uses the executable cycle decomposition,
and its membership and nonemptiness lemmas identify the result with the mathematical
exact-order predicate.

The complete order tables in degrees one, two and three give small existence criteria.
In degree three the signature `(2, 2, 2)` is absent although each order individually occurs
in `S₃`. The signature `(6, 2, 2)` is absent too, even though the nonabelian degree-three
triple has orders dividing it.
-/

public section

namespace TauCeti

variable {n a b c : ℕ}

/-- Exact component orders are decidable by taking least common multiples of the executable
cycle partitions. -/
instance (t : PermutationTriple n) (a b c : ℕ) : Decidable (t.HasExactOrders a b c) :=
  decidable_of_iff (t.computedOrderTriple = (a, b, c)) (by
    simp only [PermutationTriple.computedOrderTriple_eq, PermutationTriple.hasExactOrders_iff])

/-- All connected degree-`n` permutation triples with component orders exactly `(a, b, c)`.
This enumerates literal triples, including all relabelings, rather than isomorphism classes. -/
@[expose] def connectedTriplesWithExactOrders (n a b c : ℕ) : Finset (PermutationTriple n) :=
  (connectedTriples n).filter fun t => t.HasExactOrders a b c

/-- Membership in the search result is exactly connectedness and the prescribed exact orders. -/
@[simp] theorem mem_connectedTriplesWithExactOrders {t : PermutationTriple n} :
    t ∈ connectedTriplesWithExactOrders n a b c ↔ t.IsConnected ∧ t.HasExactOrders a b c := by
  simp [connectedTriplesWithExactOrders]

/-- The finite search succeeds if and only if a connected triple with those exact orders exists. -/
theorem nonempty_connectedTriplesWithExactOrders_iff :
    (connectedTriplesWithExactOrders n a b c).Nonempty ↔
      ∃ t : ConnectedTriple n, t.1.HasExactOrders a b c := by
  simp only [Finset.Nonempty, mem_connectedTriplesWithExactOrders]
  constructor
  · rintro ⟨t, ht, ho⟩
    exact ⟨⟨t, ht⟩, ho⟩
  · rintro ⟨t, ho⟩
    exact ⟨t.1, t.2, ho⟩

/-- A connected triple with specified exact orders exists if and only if its signature occurs
in the computed order table for that degree. -/
theorem exists_hasExactOrders_iff_mem_image_computedOrderTriple :
    (∃ t : ConnectedTriple n, t.1.HasExactOrders a b c) ↔
      (a, b, c) ∈ (connectedTriples n).image PermutationTriple.computedOrderTriple := by
  rw [Finset.mem_image]
  simp only [mem_connectedTriples, PermutationTriple.computedOrderTriple_eq,
    ← PermutationTriple.hasExactOrders_iff]
  constructor
  · rintro ⟨t, ho⟩
    exact ⟨t.1, t.2, ho⟩
  · rintro ⟨t, ht, ho⟩
    exact ⟨⟨t, ht⟩, ho⟩

/-- There are no connected triples of degree zero, for any order specification. -/
@[simp] theorem connectedTriplesWithExactOrders_zero (a b c : ℕ) :
    connectedTriplesWithExactOrders 0 a b c = ∅ := by
  ext t
  simp [PermutationTriple.isConnected_iff]

/-- The unique exact order triple realized in degree one. -/
theorem image_computedOrderTriple_connectedTriples_one :
    (connectedTriples 1).image PermutationTriple.computedOrderTriple = {(1, 1, 1)} := by
  decide +kernel

/-- The exact order triples realized in degree two; precisely one branch point is unramified. -/
theorem image_computedOrderTriple_connectedTriples_two :
    (connectedTriples 2).image PermutationTriple.computedOrderTriple =
      {(1, 2, 2), (2, 1, 2), (2, 2, 1)} := by
  decide +kernel

/-- The complete exact order table in degree three, including the Euclidean signature `(3,3,3)`. -/
theorem image_computedOrderTriple_connectedTriples_three :
    (connectedTriples 3).image PermutationTriple.computedOrderTriple =
      {(1, 3, 3), (3, 1, 3), (3, 3, 1), (2, 2, 3), (2, 3, 2), (3, 2, 2), (3, 3, 3)} := by
  decide +kernel

/-- A connected degree-three triple with specified exact orders exists precisely for one of
the seven signatures in the complete table. -/
theorem exists_hasExactOrders_three_iff (a b c : ℕ) :
    (∃ t : ConnectedTriple 3, t.1.HasExactOrders a b c) ↔
      (a, b, c) ∈ ({(1, 3, 3), (3, 1, 3), (3, 3, 1), (2, 2, 3),
        (2, 3, 2), (3, 2, 2), (3, 3, 3)} : Finset (ℕ × ℕ × ℕ)) := by
  rw [exists_hasExactOrders_iff_mem_image_computedOrderTriple,
    image_computedOrderTriple_connectedTriples_three]

/-! The searches below count numbered triples. They exercise exactness, positive genus,
and the distinction between individual orders and a realizable product-one signature. -/

example : (connectedTriplesWithExactOrders 3 3 2 2).card = 6 := by decide +kernel

example : (connectedTriplesWithExactOrders 3 3 3 3).card = 2 := by decide +kernel

example : connectedTriplesWithExactOrders 3 2 2 2 = ∅ := by decide +kernel

example : connectedTriplesWithExactOrders 3 6 2 2 = ∅ := by decide +kernel

example : PermutationTriple.s3Triple.HasDividingOrders 6 2 2 := by
  rw [PermutationTriple.hasDividingOrders_iff_orderTriple_dvd,
    PermutationTriple.orderTriple_s3Triple]
  decide

example : PermutationTriple.torusTriple ∈ connectedTriplesWithExactOrders 4 4 4 2 := by
  simp [PermutationTriple.isConnected_torusTriple, PermutationTriple.hasExactOrders_iff,
    PermutationTriple.orderTriple_torusTriple]

end TauCeti

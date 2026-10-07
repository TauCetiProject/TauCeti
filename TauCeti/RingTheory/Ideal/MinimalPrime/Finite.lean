/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Isolating a minimal prime among finitely many

Let `A` be a commutative ring with finitely many minimal primes, as is every Noetherian ring
(`minimalPrimes.finite_of_isNoetherianRing`). For a minimal prime `P`, the intersection of the
other minimal primes is not contained in `P`, so it has an element `g ∉ P`. Every prime `q` not
containing `g` contains some minimal prime, which must be `P`. Geometrically, the basic open set
`D(g)` of `Spec A` is a nonempty open subset of the irreducible component `V(P)` meeting no other
irreducible component. This reduces statements about a single irreducible component to
statements about a localization `A[1/g]`.

## Main results

* `TauCeti.exists_notMem_forall_le_of_mem_minimalPrimes`: for a minimal prime `P` of a ring with
  finitely many minimal primes, there is `g ∉ P` such that every prime not containing `g`
  contains `P`.
-/

public section

namespace TauCeti

/-- Let `P` be a minimal prime of a ring with finitely many minimal primes. Then there is an
element `g ∉ P` such that every prime `q` with `g ∉ q` contains `P`: the basic open set `D(g)` is
a nonempty open subset of the irreducible component `V(P)`. -/
theorem exists_notMem_forall_le_of_mem_minimalPrimes {A : Type*} [CommRing A]
    (hfin : (minimalPrimes A).Finite) {P : Ideal A} (hP : P ∈ minimalPrimes A) :
    ∃ g ∉ P, ∀ q : Ideal A, q.IsPrime → g ∉ q → P ≤ q := by
  classical
  have hPp : P.IsPrime := hP.1.1
  -- The intersection of the other minimal primes is not contained in `P`.
  let s : Finset (Ideal A) := (hfin.sdiff (t := {P})).toFinset
  have hs : ¬ s.inf id ≤ P := by
    rw [hPp.inf_le']
    rintro ⟨Q, hQs, hQP⟩
    rw [Set.Finite.mem_toFinset, Set.mem_sdiff, Set.mem_singleton_iff] at hQs
    exact hQs.2 (le_antisymm hQP (hP.2 hQs.1.1 hQP))
  obtain ⟨g, hg, hgP⟩ := IsConcreteLE.not_le_iff_exists.mp hs
  refine ⟨g, hgP, fun q hq hgq ↦ ?_⟩
  -- Every prime `q` contains a minimal prime `Q`, and `g ∉ q` forces `Q = P`.
  obtain ⟨Q, hQ, hQq⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ q)
  by_cases hQP : Q = P
  · exact hQP ▸ hQq
  · have hQs : Q ∈ s := by
      rw [Set.Finite.mem_toFinset, Set.mem_sdiff, Set.mem_singleton_iff]
      exact ⟨hQ, hQP⟩
    exact absurd (hQq (Finset.inf_le (f := id) hQs hg)) hgq

end TauCeti

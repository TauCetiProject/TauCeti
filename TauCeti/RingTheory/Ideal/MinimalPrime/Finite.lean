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

Let `I` be an ideal in a commutative semiring with finitely many minimal primes over it. For a
minimal prime `P` over `I`, the intersection of the other minimal primes is not contained in `P`,
so it has an element `g ∉ P`. Every prime `q` over `I` not containing `g` contains some minimal
prime over `I`, which must be `P`. Geometrically, when `I = ⊥`, the basic open set `D(g)` of
`Spec A` is a nonempty open subset of the irreducible component `V(P)` meeting no other
irreducible component. This reduces statements about a single irreducible component to statements
about a localization `A[1/g]`.

## Main results

* `Ideal.exists_notMem_forall_le_of_mem_minimalPrimes`: for a minimal prime `P` over an ideal
  with finitely many minimal primes, there is `g ∉ P` such that every prime over that ideal not
  containing `g` contains `P`.
-/

public section

namespace Ideal

/-- Let `P` be a minimal prime over an ideal `I` with finitely many minimal primes. Then there is
an element `g ∉ P` such that every prime `q` over `I` with `g ∉ q` contains `P`. -/
theorem exists_notMem_forall_le_of_mem_minimalPrimes {A : Type*} [CommSemiring A] (I : Ideal A)
    (hfin : I.minimalPrimes.Finite) {P : Ideal A} (hP : P ∈ I.minimalPrimes) :
    ∃ g ∉ P, ∀ q : Ideal A, q.IsPrime → I ≤ q → g ∉ q → P ≤ q := by
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
  refine ⟨g, hgP, fun q hq hIq hgq ↦ ?_⟩
  -- Every prime `q` contains a minimal prime `Q`, and `g ∉ q` forces `Q = P`.
  obtain ⟨Q, hQ, hQq⟩ := Ideal.exists_minimalPrimes_le hIq
  by_cases hQP : Q = P
  · exact hQP ▸ hQq
  · have hQs : Q ∈ s := by
      rw [Set.Finite.mem_toFinset, Set.mem_sdiff, Set.mem_singleton_iff]
      exact ⟨hQ, hQP⟩
    exact absurd (hQq (Finset.inf_le (f := id) hQs hg)) hgq

end Ideal

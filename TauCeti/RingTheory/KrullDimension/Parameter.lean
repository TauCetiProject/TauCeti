/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-!
# Functions with finite zero fibres on affine curves

In a Noetherian ring of dimension at most one, every maximal ideal contains an element
whose principal quotient has dimension zero. Choose the element by avoiding the finitely
many minimal primes which are not maximal. Every prime containing the element is then
maximal. This also handles isolated zero-dimensional components and nonreduced rings.

For a finite type algebra over an Artinian ring, the quotient is finite over the base. Thus every
closed point of an affine curve lies in the finite zero fibre of a regular function.
This construction works over finite fields as well as infinite fields.

## References

* The Stacks Project, Lemma 55.8.2, https://stacks.math.columbia.edu/tag/0C2T,
  for finiteness of model normalization over a discrete valuation ring.
-/

public section

namespace Ideal

variable {A : Type*} [CommRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]

/-- Every maximal ideal of a Noetherian ring of dimension at most one contains an element
whose principal quotient has dimension zero. The ring need not be a domain or equidimensional. -/
theorem exists_mem_krullDimLE_zero_quotient_span_singleton (m : Ideal A) [m.IsMaximal] :
    ∃ x ∈ m, Ring.KrullDimLE 0 (A ⧸ span {x}) := by
  classical
  let S : Set (Ideal A) := {p ∈ minimalPrimes A | ¬p.IsMaximal}
  have hS : S.Finite := (minimalPrimes.finite_of_isNoetherianRing A).subset
    (fun _ hp ↦ hp.1)
  have hnot : ¬(m : Set A) ⊆ ⋃ p ∈ S, (p : Set A) := by
    intro h
    obtain ⟨p, hp, hmp⟩ := (subset_union_prime_finite hS (f := id) m m
      (fun p hp _ _ ↦ hp.1.isPrime)).mp h
    exact hp.2 ((‹m.IsMaximal›.eq_of_le hp.1.isPrime.ne_top hmp) ▸ ‹m.IsMaximal›)
  obtain ⟨x, hxm, hx⟩ := Set.not_subset.mp hnot
  have hxS (p : Ideal A) (hp : p ∈ S) : x ∉ p := fun hxp ↦
    hx (Set.mem_biUnion hp hxp)
  refine ⟨x, hxm, Ring.KrullDimLE.mk₀ fun q hq ↦ ?_⟩
  let p := q.comap (Ideal.Quotient.mk (span {x}))
  have hp : p.IsPrime := hq.comap _
  have hxp : x ∈ p := by simp [p, Ideal.mem_comap]
  have hpmax : p.IsMaximal := by
    rcases Ring.krullDimLE_one_iff.mp ‹Ring.KrullDimLE 1 A› p hp with hpmin | hpmax
    · by_contra hn
      exact hxS p ⟨hpmin, hn⟩ hxp
    · exact hpmax
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under _ hpmax

end Ideal

namespace Ideal

/-- On an affine scheme of dimension at most one and finite type over an Artinian ring, every closed
point lies on the finite zero fibre of a function. No reducedness, equidimensionality, or
infinitude of a residue field is required. -/
theorem exists_mem_finite_quotient_span_singleton {k A : Type*} [CommRing k] [IsArtinianRing k]
    [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] [Ring.KrullDimLE 1 A]
    (m : Ideal A) [m.IsMaximal] :
    ∃ x ∈ m, Module.Finite k (A ⧸ Ideal.span {x}) := by
  have := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨x, hxm, hx⟩ := m.exists_mem_krullDimLE_zero_quotient_span_singleton
  exact ⟨x, hxm, (Module.finite_iff_krullDimLE_zero k _).mpr hx⟩

end Ideal

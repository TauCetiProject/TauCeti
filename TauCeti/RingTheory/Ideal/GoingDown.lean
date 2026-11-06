/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.GoingDown

/-!
# Minimal primes under going down

If an `R`-algebra `S` satisfies going down, then for every ideal `I` of `R`, the contraction of a
minimal prime over `I S` is a minimal prime over `I`: a strictly smaller prime of `R` containing
`I` would lift, by going down, to a strictly smaller prime of `S` containing `I S`. Taking
`I = ⊥`, minimal primes of `S` contract to minimal primes of `R`. Flat algebras satisfy going down
(`Algebra.HasGoingDown.of_flat`), so geometrically a flat morphism of affine schemes sends generic
points of irreducible components to generic points of irreducible components.

## Main results

* `Ideal.under_mem_minimalPrimes_of_mem_minimalPrimes_map`: under going down, minimal primes
  over `I S` contract to minimal primes over `I`.
* `Ideal.under_mem_minimalPrimes`: under going down, minimal primes contract to minimal primes.
-/

public section

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.HasGoingDown R S]

/-- If `S` satisfies going down over `R`, then for an ideal `I` of `R`, the contraction of a
minimal prime over `I S` is a minimal prime over `I`. -/
theorem under_mem_minimalPrimes_of_mem_minimalPrimes_map {I : Ideal R} {Q : Ideal S}
    (hQ : Q ∈ (I.map (algebraMap R S)).minimalPrimes) : Q.under R ∈ I.minimalPrimes := by
  have : Q.IsPrime := hQ.1.1
  refine ⟨⟨comap_isPrime _ Q, le_comap_of_map_le hQ.1.2⟩, fun P hP hle ↦ ?_⟩
  have : P.IsPrime := hP.1
  by_contra hne
  obtain ⟨Q', hQ'Q, hQ', hQ'P⟩ := exists_ideal_lt_liesOver_of_lt Q (hle.lt_of_not_ge hne)
  exact hQ'Q.not_ge (hQ.2 ⟨hQ', map_le_of_le_comap (hP.2.trans_eq hQ'P.over)⟩ hQ'Q.le)

/-- If `S` satisfies going down over `R`, then the contraction of a minimal prime of `S` is a
minimal prime of `R`. -/
theorem under_mem_minimalPrimes {Q : Ideal S} (hQ : Q ∈ minimalPrimes S) :
    Q.under R ∈ minimalPrimes R :=
  under_mem_minimalPrimes_of_mem_minimalPrimes_map (I := ⊥) (by rwa [map_bot])

end Ideal

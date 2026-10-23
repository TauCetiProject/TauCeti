/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.GoingDown

/-!
# Minimal primes under going down

If an `R`-algebra `S` satisfies going down, then the contraction of a minimal prime of `S` is a
minimal prime of `R`: a strictly smaller prime of `R` would lift, by going down, to a strictly
smaller prime of `S`. Flat algebras satisfy going down (`Algebra.HasGoingDown.of_flat`), so
geometrically a flat morphism of affine schemes sends generic points of irreducible components to
generic points of irreducible components.

## Main results

* `Ideal.under_mem_minimalPrimes`: under going down, minimal primes contract to minimal primes.
-/

public section

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- If `S` satisfies going down over `R`, then the contraction of a minimal prime of `S` is a
minimal prime of `R`. -/
theorem under_mem_minimalPrimes [Algebra.HasGoingDown R S] {Q : Ideal S}
    (hQ : Q ∈ minimalPrimes S) : Q.under R ∈ minimalPrimes R := by
  have : Q.IsPrime := hQ.1.1
  refine ⟨⟨comap_isPrime _ Q, bot_le⟩, fun P hP hle ↦ ?_⟩
  have : P.IsPrime := hP.1
  by_contra hne
  obtain ⟨Q', hQ'Q, hQ', -⟩ := exists_ideal_lt_liesOver_of_lt Q (hle.lt_of_not_ge hne)
  exact hQ'Q.not_ge (hQ.2 ⟨hQ', bot_le⟩ hQ'Q.le)

end Ideal

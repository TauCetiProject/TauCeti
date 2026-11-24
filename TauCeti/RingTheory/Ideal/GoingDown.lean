/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.Height

/-!
# Minimal primes and heights under going down

If an `R`-algebra `S` satisfies going down, then for every ideal `I` of `R`, the contraction of a
minimal prime over `I S` is a minimal prime over `I`: a strictly smaller prime of `R` containing
`I` would lift, by going down, to a strictly smaller prime of `S` containing `I S`. Taking
`I = ⊥`, minimal primes of `S` contract to minimal primes of `R`. Flat algebras satisfy going down
(`Algebra.HasGoingDown.of_flat`), so geometrically a flat morphism of affine schemes sends generic
points of irreducible components to generic points of irreducible components.

Going down also does not lower heights: it lifts every chain of primes of `R` ending at `P ∩ R` to
a chain of the same length ending at a prime `P` of `S`, so `ht (P ∩ R) ≤ ht P`, and the same
holds for every ideal `P` by passing to its minimal primes. Unlike Mathlib's
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`, this needs no Noetherian hypothesis.

## Main results

* `Ideal.under_mem_minimalPrimes_of_mem_minimalPrimes_map`: under going down, minimal primes
  over `I S` contract to minimal primes over `I`.
* `Ideal.under_mem_minimalPrimes`: under going down, minimal primes contract to minimal primes.
* `Ideal.height_under_le_height_of_hasGoingDown`: under going down, `ht (P ∩ R) ≤ ht P`.
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

/-- Going down does not lower heights: every ideal `P` of `S` has height at least that of
`P ∩ R`. -/
theorem height_under_le_height_of_hasGoingDown (P : Ideal S) : (P.under R).height ≤ P.height := by
  -- It suffices to treat the minimal primes `Q` of `P`, which lie over primes containing `P ∩ R`.
  rw [P.height_eq_inf_minimalPrimes]
  refine le_iInf₂ fun Q hQ ↦ ?_
  have := hQ.1.1
  have hPQ : P.under R ≤ Q.under R := by
    rw [Ideal.under_def, Ideal.under_def]
    exact Ideal.comap_mono hQ.1.2
  refine (Ideal.height_mono hPQ).trans ?_
  rw [PrimeSpectrum.height_eq_orderHeight (⟨Q.under R, inferInstance⟩ : PrimeSpectrum R),
    PrimeSpectrum.height_eq_orderHeight (⟨Q, ‹_›⟩ : PrimeSpectrum S)]
  -- Going down lifts a chain of primes ending at `Q ∩ R` to a chain of the same length ending
  -- at `Q`.
  refine Order.height_le fun l hl ↦ ?_
  have : Q.LiesOver l.last.asIdeal := ⟨by rw [hl]⟩
  obtain ⟨L, hlen, hlast, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l Q
  rw [← hlen, ← hlast]
  exact Order.length_le_height_last

end Ideal

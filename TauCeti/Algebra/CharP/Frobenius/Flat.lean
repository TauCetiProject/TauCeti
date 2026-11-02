/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Flat Frobenius forces reducedness

Let `R` be a commutative ring of exponential characteristic `p > 1`. Frobenius induces the
identity on the prime spectrum of `R`, so if it is flat it is faithfully flat, hence injective,
and `R` is reduced. This is the obstruction to flatness of Frobenius on nonreduced rings, such as
`𝔽_p[ε] ⧸ (ε²)`, where Frobenius kills `ε`. Kunz's theorem
`TauCeti.IsRegularRing.flat_frobenius` gives flatness for regular rings.

## Main results

* `TauCeti.isReduced_of_flat_frobenius`: a ring of exponential characteristic `p > 1` with flat
  Frobenius is reduced.
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R] (p : ℕ) [ExpChar R p]

/-- **Flat Frobenius forces reducedness.** If the Frobenius endomorphism of a ring of exponential
characteristic `p > 1` is flat, then the ring is reduced. Frobenius induces the identity on the
prime spectrum, so flatness makes it faithfully flat, hence injective. In particular, regularity
cannot be dropped from `TauCeti.IsRegularRing.flat_frobenius`: Frobenius of `𝔽_p[ε] ⧸ (ε²)` kills
`ε` and is not flat. -/
theorem isReduced_of_flat_frobenius (hp : 1 < p) (h : (frobenius R p).Flat) : IsReduced R := by
  have hcomap : Function.Surjective (PrimeSpectrum.comap (frobenius R p)) := fun P ↦
    ⟨P, PrimeSpectrum.ext <| Ideal.ext fun _ ↦ P.2.pow_mem_iff_mem p (zero_lt_one.trans hp)⟩
  have hinj := (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.2 ⟨h, hcomap⟩).injective
  exact (isReduced_iff_pow_one_lt p hp).2 fun a ha ↦
    hinj (ha.trans (map_zero (frobenius R p)).symm)

end TauCeti

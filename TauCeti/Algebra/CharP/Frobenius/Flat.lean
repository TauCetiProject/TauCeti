/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Algebra.CharP.Reduced
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import TauCeti.Algebra.CharP.Frobenius.Basic
import TauCeti.RingTheory.Flat.Localization

/-!
# Flat Frobenius: reducedness, iterates, and localization

Let `R` be a commutative ring of exponential characteristic `p > 1`. Frobenius induces the
identity on the prime spectrum of `R`, so if it is flat it is faithfully flat, hence injective,
and `R` is reduced. This is the obstruction to flatness of Frobenius on nonreduced rings, such as
`𝔽_p[ε] ⧸ (ε²)`, where Frobenius kills `ε`. Kunz's theorem
`TauCeti.IsRegularRing.flat_frobenius` gives flatness for regular rings.

Flatness of Frobenius is preserved by iteration (`TauCeti.flat_iterateFrobenius`) and by
localization at any submonoid (`TauCeti.flat_frobenius_of_isLocalization`).

## Main results

* `TauCeti.isReduced_of_flat_frobenius`: a ring of exponential characteristic `p > 1` with flat
  Frobenius is reduced.
* `TauCeti.injective_frobenius_of_flat`: flat Frobenius is injective.
* `TauCeti.flat_iterateFrobenius`: if Frobenius is flat, so is each of its iterates.
* `TauCeti.flat_frobenius_of_isLocalization`: if Frobenius of `R` is flat, so is Frobenius of any
  localization of `R`.
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
    ⟨P, PrimeSpectrum.ext (P.isPrime.comap_frobenius p)⟩
  have hinj := (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.2 ⟨h, hcomap⟩).injective
  exact (isReduced_iff_pow_one_lt p hp).2 fun a ha ↦
    hinj (ha.trans (map_zero (frobenius R p)).symm)

/-- Flat Frobenius is injective. -/
theorem injective_frobenius_of_flat (h : (frobenius R p).Flat) :
    Function.Injective (frobenius R p) := by
  rcases expChar_is_prime_or_one R p with hp | rfl
  · have := isReduced_of_flat_frobenius p hp.one_lt h
    exact frobenius_inj R p
  · exact fun x y hxy ↦ by simpa [frobenius_def] using hxy

/-- If the Frobenius endomorphism is flat, then so is each of its iterates. -/
theorem flat_iterateFrobenius (h : (frobenius R p).Flat) (n : ℕ) :
    (iterateFrobenius R p n).Flat := by
  induction n with
  | zero => simpa using RingHom.Flat.id R
  | succ n ih => simpa [iterateFrobenius_add, iterateFrobenius_one] using h.comp ih

/-- If the Frobenius endomorphism of `R` is flat, then so is the Frobenius endomorphism of any
localization of `R`. -/
theorem flat_frobenius_of_isLocalization {Rₘ : Type*} [CommRing Rₘ] (M : Submonoid R)
    [Algebra R Rₘ] [IsLocalization M Rₘ] [ExpChar Rₘ p] (h : (frobenius R p).Flat) :
    (frobenius Rₘ p).Flat := by
  rw [← RingHom.Flat.comp_algebraMap_isLocalization_iff M (frobenius Rₘ p),
    ← RingHom.frobenius_comm]
  exact h.comp (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat Rₘ M))

end TauCeti

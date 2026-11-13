/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.Clopen
import Mathlib.RingTheory.Ideal.IdempotentFG
import TauCeti.RingTheory.LocalRing.Basic

/-!
# Connected prime spectra and idempotents

The prime spectrum of a nontrivial commutative ring is connected exactly when the ring has no
idempotents other than zero and one.  Mathlib identifies idempotents with clopen subsets of the
prime spectrum; this file records the resulting connectedness criterion in the form used by
coordinate rings of geometrically connected affine schemes.

## Main declarations

* `IsIdempotentElem.eq_zero_or_eq_one_of_preconnectedSpace`: an idempotent is zero or one when
  `Spec R` is preconnected.
* `Ideal.eq_bot_of_isIdempotentElem_of_ne_top`: a finitely generated idempotent proper ideal is
  zero when `Spec R` is preconnected.
* `TauCeti.connectedSpace_primeSpectrum_iff_idempotent_eq_zero_or_one`: `Spec R` is connected
  if and only if every idempotent of `R` is zero or one.
* `TauCeti.connectedSpace_primeSpectrum_of_isLocalRing`: the prime spectrum of a local ring is
  connected.

Descent of connectedness along ring homomorphisms with nil kernel is general spectral topology and
lives in `TauCeti.RingTheory.Spectrum.Prime.Topology`.
-/

public section

section CommRing

variable {R : Type*} [CommRing R]

/-- An idempotent in a commutative ring with preconnected prime spectrum is zero or one. -/
theorem IsIdempotentElem.eq_zero_or_eq_one_of_preconnectedSpace
    [PreconnectedSpace (PrimeSpectrum R)] {e : R} (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  rcases isClopen_iff.mp (PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩) with h | h
  · exact .inl <| PrimeSpectrum.basicOpen_injOn_isIdempotentElem he .zero <| by
      simp [← SetLike.coe_set_eq, h]
  · exact .inr <| PrimeSpectrum.basicOpen_injOn_isIdempotentElem he .one <| by
      simp [← SetLike.coe_set_eq, h]

/-- A finitely generated idempotent proper ideal of a commutative ring with preconnected prime
spectrum is zero: its generator is an idempotent, hence `0` or `1`, and `1` would make the ideal
the whole ring. -/
theorem Ideal.eq_bot_of_isIdempotentElem_of_ne_top [PreconnectedSpace (PrimeSpectrum R)]
    {I : Ideal R} (hfg : I.FG) (hI : IsIdempotentElem I) (hne : I ≠ ⊤) : I = ⊥ := by
  obtain ⟨e, he, hspan⟩ := (Ideal.isIdempotentElem_iff_of_fg I hfg).mp hI
  rcases he.eq_zero_or_eq_one_of_preconnectedSpace with rfl | rfl
  · simpa using hspan
  · exact absurd (by simpa using hspan) hne

namespace TauCeti

/-- **The prime spectrum of a nontrivial commutative ring is connected exactly when its only
idempotents are zero and one.** -/
theorem connectedSpace_primeSpectrum_iff_idempotent_eq_zero_or_one [Nontrivial R] :
    ConnectedSpace (PrimeSpectrum R) ↔
      ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  refine ⟨fun _ _ he ↦ he.eq_zero_or_eq_one_of_preconnectedSpace, fun h ↦ ?_⟩
  refine connectedSpace_iff_clopen.mpr ⟨inferInstance, fun s hs ↦ ?_⟩
  obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
  rcases h e he with rfl | rfl <;> simp

/-- **The prime spectrum of a local ring is connected**: the only idempotents of a local ring are
zero and one. -/
instance connectedSpace_primeSpectrum_of_isLocalRing [IsLocalRing R] :
    ConnectedSpace (PrimeSpectrum R) :=
  connectedSpace_primeSpectrum_iff_idempotent_eq_zero_or_one.mpr fun _ he ↦
    he.eq_zero_or_eq_one_of_isLocalRing

end TauCeti

end CommRing

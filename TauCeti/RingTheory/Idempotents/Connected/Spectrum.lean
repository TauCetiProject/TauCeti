/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.Clopen

/-!
# Connected prime spectra and idempotents

The prime spectrum of a nontrivial commutative ring is connected exactly when the ring has no
idempotents other than zero and one.  Mathlib identifies idempotents with clopen subsets of the
prime spectrum; this file records the resulting connectedness criterion in the form used by
coordinate rings of geometrically connected affine schemes.

## Main declarations

* `IsIdempotentElem.eq_zero_or_eq_one_of_preconnectedSpace`: an idempotent is zero or one when
  `Spec R` is preconnected.
* `TauCeti.connectedSpace_primeSpectrum_iff_idempotent_eq_zero_or_one`: `Spec R` is connected
  if and only if every idempotent of `R` is zero or one.
* `TauCeti.connectedSpace_primeSpectrum_of_ker_le_nilradical`: connectedness descends along a
  ring homomorphism whose kernel is nil, i.e. one inducing a dominant map on spectra.
* `TauCeti.connectedSpace_primeSpectrum_of_injective`: in particular, connectedness descends
  along an injective ring homomorphism.
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

end TauCeti

end CommRing

namespace TauCeti

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- Connectedness of prime spectra descends along a ring homomorphism whose kernel consists of
nilpotent elements, i.e. one for which `Spec S → Spec R` has dense range. -/
theorem connectedSpace_primeSpectrum_of_ker_le_nilradical [ConnectedSpace (PrimeSpectrum S)]
    (f : R →+* S) (hf : RingHom.ker f ≤ nilradical R) : ConnectedSpace (PrimeSpectrum R) :=
  have := ((PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).mpr hf).preconnectedSpace
    (PrimeSpectrum.continuous_comap f)
  { toNonempty := .map (PrimeSpectrum.comap f) inferInstance }

/-- Connectedness of prime spectra descends along injective ring homomorphisms. -/
theorem connectedSpace_primeSpectrum_of_injective [ConnectedSpace (PrimeSpectrum S)]
    (f : R →+* S) (hf : Function.Injective f) : ConnectedSpace (PrimeSpectrum R) :=
  connectedSpace_primeSpectrum_of_ker_le_nilradical f fun x hx ↦ by
    rw [hf ((RingHom.mem_ker.mp hx).trans f.map_zero.symm)]
    exact zero_mem _

end TauCeti

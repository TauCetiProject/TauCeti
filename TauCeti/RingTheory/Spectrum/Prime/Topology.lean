/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Dominance and injectivity on prime spectra

An injective ring homomorphism induces a dense map on prime spectra. For a reduced
source ring, the converse holds. These facts supply the coordinate-ring criterion for
dominance used in finite dominant affine group quotients.
-/

public section

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

/-- An injective ring homomorphism induces a dense map on prime spectra. -/
theorem denseRange_comap_of_injective (f : R →+* S) (hf : Function.Injective f) :
    DenseRange (PrimeSpectrum.comap f) := by
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot f).mp hf]
  exact bot_le

/-- A ring homomorphism from a reduced ring is injective exactly when its spectral
comap has dense range. -/
theorem denseRange_comap_iff_injective [IsReduced R] (f : R →+* S) :
    DenseRange (PrimeSpectrum.comap f) ↔ Function.Injective f := by
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, RingHom.injective_iff_ker_eq_bot,
    nilradical_eq_zero, Ideal.zero_eq_bot, le_bot_iff]

end RingHom

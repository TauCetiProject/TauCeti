/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Contraction along surjections on prime spectra

`RingHom.primeSpectrumOrderIsoZeroLocusOfSurj_apply_coe` computes Mathlib's
`Ideal.primeSpectrumOrderIsoZeroLocusOfSurj` as contraction.
`Ideal.primeSpectrumQuotientOrderIsoZeroLocus_apply_coe` specializes this rule to quotients.
-/

public section

/-- For a surjective ring homomorphism `f` with kernel `I`, the order isomorphism onto the
zero locus of `I` sends each prime to its contraction along `f`. -/
@[simp]
theorem RingHom.primeSpectrumOrderIsoZeroLocusOfSurj_apply_coe
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f)
    {I : Ideal R} (hI : RingHom.ker f = I) (r : PrimeSpectrum S) :
    (Ideal.primeSpectrumOrderIsoZeroLocusOfSurj f hf hI r : PrimeSpectrum R) = r.comap f := by
  simp only [Ideal.primeSpectrumOrderIsoZeroLocusOfSurj.eq_1, RelIso.coe_fn_mk, Equiv.coe_fn_mk]

/-- The quotient spectrum order isomorphism sends a prime to its contraction along
`Ideal.Quotient.mk`. -/
@[simp]
theorem Ideal.primeSpectrumQuotientOrderIsoZeroLocus_apply_coe {R : Type*} [CommRing R]
    (I : Ideal R) (r : PrimeSpectrum (R ⧸ I)) :
    (I.primeSpectrumQuotientOrderIsoZeroLocus r : PrimeSpectrum R) =
      r.comap (Ideal.Quotient.mk I) := by
  simp only [Ideal.primeSpectrumQuotientOrderIsoZeroLocus.eq_1,
    RingHom.primeSpectrumOrderIsoZeroLocusOfSurj_apply_coe]

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Idempotents along maps of prime spectra

Idempotents of a commutative ring correspond to clopen subsets of its prime spectrum
(`PrimeSpectrum.isIdempotentElemEquivClopens`), and a ring homomorphism `f : R →+* S` sends the
clopen set `D(e)` of an idempotent `e` to its preimage `D(f e)` under `Spec S → Spec R`: the
idempotent of the preimage of a clopen set is the image of its idempotent
(`PrimeSpectrum.isIdempotentElemEquivClopens_symm_preimage`).
Consequently, topological properties of the spectral map control how `f` acts on idempotents:

* if `Spec S → Spec R` is surjective, then `f` is injective on idempotents;
* if `Spec S → Spec R` is a homeomorphism, then `f` is a bijection between the idempotents of
  `R` and those of `S`.

The second statement is the mechanism by which universal homeomorphisms preserve idempotent
lifting, and hence henselian pairs.

## References

* [Stacks Project, Lemma 10.21.3](https://stacks.math.columbia.edu/tag/00EE), idempotents and
  clopen subsets of the spectrum.
-/

public section

namespace PrimeSpectrum

open TopologicalSpace

/-- **Idempotents of preimages.** For a ring homomorphism `f : R →+* S` and a clopen subset `U` of
`Spec R` with idempotent `e_U`, the idempotent of the clopen preimage of `U` under
`Spec f : Spec S → Spec R` is `f e_U`. -/
theorem isIdempotentElemEquivClopens_symm_preimage {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (U : Clopens (PrimeSpectrum R)) :
    isIdempotentElemEquivClopens.symm
        ⟨comap f ⁻¹' U, U.isClopen.preimage (continuous_comap f)⟩ =
      ⟨f (isIdempotentElemEquivClopens.symm U).val,
        (isIdempotentElemEquivClopens.symm U).prop.map f⟩ := by
  rw [OrderIso.symm_apply_eq]
  -- Both sets are the preimage of the basic open set of `e_U`, which is `U`.
  ext x
  rw [coe_isIdempotentElemEquivClopens_apply, ← comap_basicOpen,
    basicOpen_isIdempotentElemEquivClopens_symm]
  simp

end PrimeSpectrum

namespace RingHom

open PrimeSpectrum

variable {R S : Type*}

/-- If `Spec S → Spec R` is surjective, then two idempotents of `R` with the same image in `S`
are equal. -/
theorem injOn_isIdempotentElem_of_comap_surjective [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (hf : Function.Surjective (comap f)) :
    Set.InjOn f {e | IsIdempotentElem e} := by
  intro e he e' he' hee'
  refine basicOpen_injOn_isIdempotentElem he he' (TopologicalSpace.Opens.ext (Set.ext fun p ↦ ?_))
  obtain ⟨q, rfl⟩ := hf p
  simp only [SetLike.mem_coe, mem_basicOpen, comap_asIdeal, Ideal.mem_comap, hee']

variable [CommRing R] [CommRing S] (f : R →+* S)

/-- If `Spec S → Spec R` is a homeomorphism, then every idempotent of `S` is the image of an
idempotent of `R`. -/
theorem surjOn_isIdempotentElem_of_isHomeomorph_comap (hf : IsHomeomorph (comap f)) :
    Set.SurjOn f {e | IsIdempotentElem e} {e | IsIdempotentElem e} := by
  intro t (ht : IsIdempotentElem t)
  -- The image of the clopen set `D(t)` is clopen, so it is `D(e)` for an idempotent `e`.
  have hU : IsClopen (comap f '' basicOpen t) :=
    ⟨hf.isClosedMap _ (PrimeSpectrum.isClopen_iff.mpr ⟨t, ht, rfl⟩).isClosed,
      hf.isOpenMap _ (basicOpen t).isOpen⟩
  obtain ⟨e, he, hUe⟩ := PrimeSpectrum.isClopen_iff.mp hU
  refine ⟨e, he, basicOpen_injOn_isIdempotentElem (he.map f) ht
    (TopologicalSpace.Opens.ext (Set.ext fun q ↦ ?_))⟩
  have hq : q ∈ basicOpen (f e) ↔ comap f q ∈ basicOpen e := by
    simp only [mem_basicOpen, comap_asIdeal, Ideal.mem_comap]
  exact hq.trans ((Set.ext_iff.mp hUe _).symm.trans hf.injective.mem_set_image)

/-- If `Spec S → Spec R` is a homeomorphism, then `f` restricts to a bijection between the
idempotents of `R` and those of `S`. -/
theorem bijOn_isIdempotentElem_of_isHomeomorph_comap (hf : IsHomeomorph (comap f)) :
    Set.BijOn f {e | IsIdempotentElem e} {e | IsIdempotentElem e} :=
  ⟨fun _ he ↦ he.map f, f.injOn_isIdempotentElem_of_comap_surjective
    hf.surjective, f.surjOn_isIdempotentElem_of_isHomeomorph_comap hf⟩

end RingHom

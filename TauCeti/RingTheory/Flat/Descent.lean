/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Descent of faithful flatness

Faithful flatness of an algebra descends along a faithfully flat extension of the base.
This combines Mathlib's descent of module flatness with surjectivity on prime spectra,
and supplies the ring-homomorphism descent property used for finite faithfully flat morphisms.
-/

public section

open TensorProduct

/-- Faithful flatness of an algebra descends along faithfully flat scalar extension. -/
theorem Module.FaithfullyFlat.of_tensorProduct
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Module.FaithfullyFlat R S]
    [Module.FaithfullyFlat S (S ⊗[R] T)] : Module.FaithfullyFlat R T := by
  let : Module.Flat R T := Module.Flat.of_flat_tensorProduct R T S
  apply Module.FaithfullyFlat.of_comap_surjective
  intro p
  obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := S) p
  obtain ⟨r, hr⟩ :=
    PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := S) (B := S ⊗[R] T) q
  refine ⟨r.comap Algebra.TensorProduct.includeRight.toRingHom, ?_⟩
  rw [← hq, ← hr, ← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
  congr 1
  ext x
  simp [Algebra.TensorProduct.includeRight, Algebra.algebraMap_eq_smul_one,
    TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.TensorProduct.one_def]

/-- Faithfully flat ring maps descend along faithfully flat base change. -/
theorem RingHom.FaithfullyFlat.codescendsAlong_faithfullyFlat :
    RingHom.CodescendsAlong RingHom.FaithfullyFlat RingHom.FaithfullyFlat := by
  refine .mk _ RingHom.FaithfullyFlat.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [RingHom.faithfullyFlat_algebraMap_iff] at h h' ⊢
  exact Module.FaithfullyFlat.of_tensorProduct R S T

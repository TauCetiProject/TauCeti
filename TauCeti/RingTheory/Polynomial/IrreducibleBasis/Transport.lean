/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.IrreducibleBasis.Basic

/-!
# Transport of irreducible polynomial bases

Mapping coefficients through a ring equivalence preserves irreducible bases. The mapped basis
retains positive degrees, nonassociation, factorization of every input, and relevance of every
basis member. No domain or gcd hypotheses are needed for this transport.
-/

public section

open Polynomial

namespace TauCeti

variable {R S : Type*} [CommRing R] [CommRing S]
  {F B : Finset (Polynomial R)}

/-- A coefficient ring equivalence carries an irreducible basis to an irreducible basis of the
mapped family. -/
theorem isIrreducibleBasis_image_map_equiv [DecidableEq (Polynomial S)]
    (hB : F.IsIrreducibleBasis B) (e : R ≃+* S) :
    (F.image (Polynomial.map e.toRingHom)).IsIrreducibleBasis
      (B.image (Polynomial.map e.toRingHom)) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact (hB.irreducible a ha).map (Polynomial.mapEquiv e).toMulEquiv
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    simpa only [natDegree_map_eq_of_injective (f := e.toRingHom) e.injective] using
      hB.natDegree_pos a ha
  · intro b hb b' hb' h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hb'
    have h' : Associated a a' := by
      simpa only [Polynomial.coe_mapRingHom, Polynomial.map_map,
        RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp, Polynomial.map_id] using
          h.map (Polynomial.mapRingHom e.symm.toRingHom)
    exact congrArg (Polynomial.map e.toRingHom) (hB.eq_of_associated a ha a' ha' h')
  · intro f hf
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨c, v, hf⟩ := hB.exists_eq_C_mul_prod a ha
    refine ⟨e c, fun b ↦ v (b.map e.symm.toRingHom), ?_⟩
    rw [hf, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod]
    congr 1
    rw [Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro b hb
      simp [Polynomial.map_map, RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp]
    · exact (Polynomial.map_injective e.toRingHom e.injective).injOn
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨f, hf, hf0, hbf⟩ := hB.exists_dvd a ha
    exact ⟨f.map e, Finset.mem_image_of_mem _ hf,
      (Polynomial.map_ne_zero_iff e.injective).mpr hf0, Polynomial.map_dvd e.toRingHom hbf⟩

end TauCeti

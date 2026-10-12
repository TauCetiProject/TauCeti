/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.RingHom.Flat

/-!
# Transporting local flatness across ring isomorphisms

A commutative square whose horizontal maps are isomorphisms transports flatness after
localizing the target at corresponding primes. This lets symmetry arguments reduce
flatness of a morphism to flatness at one point.
-/

public section

namespace RingHom

variable {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']

/-- A square of ring maps with isomorphic source and target preserves flatness after
localizing the target at corresponding prime ideals. -/
theorem flat_localization_comap_iff (f : R →+* S) (g : R' →+* S')
    (eR : R ≃+* R') (eS : S ≃+* S')
    (h : eS.toRingHom.comp f = g.comp eR.toRingHom) (p : Ideal S') [p.IsPrime] :
    ((algebraMap S (Localization.AtPrime (p.comap eS))).comp f).Flat ↔
      ((algebraMap S' (Localization.AtPrime p)).comp g).Flat := by
  let e := IsLocalization.ringEquivOfRingEquiv
    (Localization.AtPrime (p.comap eS)) (Localization.AtPrime p)
    eS (eS.map_primeCompl_comap_eq p)
  have he : e.toRingHom.comp
      ((algebraMap S (Localization.AtPrime (p.comap eS))).comp f) =
      ((algebraMap S' (Localization.AtPrime p)).comp g).comp eR.toRingHom := by
    ext x
    exact (IsLocalization.ringEquivOfRingEquiv_eq (eS.map_primeCompl_comap_eq p) (f x)).trans
      (congrArg (algebraMap S' (Localization.AtPrime p)) (RingHom.congr_fun h x))
  calc
    _ ↔ (e.toRingHom.comp
        ((algebraMap S (Localization.AtPrime (p.comap eS))).comp f)).Flat :=
      (Flat.comp_iff_of_bijective_left (g := e.toRingHom) e.bijective).symm
    _ ↔ _ := by
      rw [he]
      exact Flat.comp_iff_of_bijective_right (g := eR.toRingHom) eR.bijective

end RingHom

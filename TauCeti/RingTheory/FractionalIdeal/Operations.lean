/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FractionalIdeal.Operations

/-!
# Transport of fractional ideals along ring equivalences

Two facts about Mathlib's `FractionalIdeal.ringEquivOfRingEquiv`, the transport of fractional
ideals along a ring equivalence `f : R ≃+* R'` extended to fraction rings.

## Main results

* `FractionalIdeal.canonicalEquiv_eq_ringEquivOfRingEquiv`: the canonical equivalence between the
  fractional ideals of two fraction rings of `R` is transport along the identity.
* `FractionalIdeal.ringEquivOfRingEquiv_coeIdeal`: transport sends the fractional ideal of an ideal
  `I` to that of `Ideal.map f I`.
-/

public section

open scoped nonZeroDivisors

namespace FractionalIdeal

section RingEquiv

variable {R R' : Type*} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

/-- The canonical equivalence between the fractional ideals of two fraction fields of `R` is
transport along the identity ring equivalence. This lets a change of fraction field and a transport
along a ring equivalence be composed by `FractionalIdeal.ringEquivOfRingEquiv_trans_apply`. -/
theorem canonicalEquiv_eq_ringEquivOfRingEquiv (K K' : Type*) [CommRing K] [CommRing K']
    [Algebra R K] [Algebra R K'] [IsFractionRing R K] [IsFractionRing R K'] :
    canonicalEquiv R⁰ K K' = ringEquivOfRingEquiv K K' (RingEquiv.refl R) := by
  let : RingHomInvPair (RingEquiv.refl R : R →+* R) (RingEquiv.refl R).symm :=
    RingHomInvPair.of_ringEquiv (RingEquiv.refl R)
  let : RingHomInvPair ((RingEquiv.refl R).symm : R →+* R) (RingEquiv.refl R) :=
    RingHomInvPair.of_ringEquiv (RingEquiv.refl R).symm
  ext I x
  rw [FractionalIdeal.mem_canonicalEquiv_apply]
  erw [FractionalIdeal.ringEquivOfRingEquiv_apply]
  -- the right-hand side is the image submodule under the semilinear equivalence, presented by
  -- `erw` through the equivalence's coercion; `change` names it so `Submodule.mem_map` fires.
  change _ ↔ x ∈ Submodule.map
      (IsFractionRing.semilinearEquivOfRingEquiv K K' (RingEquiv.refl R)).toLinearMap I.val
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    erw [IsFractionRing.semilinearEquivOfRingEquiv_apply,
      IsFractionRing.ringEquivOfRingEquiv_apply]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    erw [IsFractionRing.semilinearEquivOfRingEquiv_apply,
      IsFractionRing.ringEquivOfRingEquiv_apply]
    -- what is left is `IsLocalization.map K' (RingHom.id R) _ y = IsLocalization.map K'
    -- ↑(RingEquiv.refl R) _ y`: the coercion of `RingEquiv.refl R` *is* `RingHom.id R`, and the
    -- two remaining field arguments are proofs.
    rfl

/-- Transport of a `coeIdeal` along `FractionalIdeal.ringEquivOfRingEquiv f` is the `coeIdeal` of
the pushforward ideal `Ideal.map f`. This is the fraction-field shadow of `Ideal.map`. -/
theorem ringEquivOfRingEquiv_coeIdeal (K L : Type*)
    [CommRing K] [CommRing L] [Algebra R K] [Algebra R' L] [IsFractionRing R K]
    [IsFractionRing R' L] (f : R ≃+* R')
    (I : Ideal R) :
    ringEquivOfRingEquiv K L f (I : FractionalIdeal R⁰ K) =
      (Ideal.map (f : R →+* R') I : FractionalIdeal R'⁰ L) := by
  -- Pin the `RingHomInvPair` instances to resolve an `f`/`f.symm.symm` defeq diamond, so the `erw`
  -- rewrites below fire without a transparency option.
  let : RingHomInvPair (f : R →+* R') (f.symm : R' →+* R) := RingHomInvPair.of_ringEquiv f
  let : RingHomInvPair (f.symm : R' →+* R) (f : R →+* R') := RingHomInvPair.of_ringEquiv f.symm
  apply FractionalIdeal.coeToSubmodule_injective
  dsimp only
  rw [← FractionalIdeal.val_eq_coe, FractionalIdeal.ringEquivOfRingEquiv_apply_val,
    FractionalIdeal.val_eq_coe, FractionalIdeal.coe_coeIdeal, FractionalIdeal.coe_coeIdeal]
  ext x
  simp only [Submodule.mem_map, FractionalIdeal.mem_coeSubmodule]
  constructor
  · rintro ⟨y, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨f r, Ideal.mem_map_of_mem _ hr, by
      erw [IsFractionRing.semilinearEquivOfRingEquiv_algebraMap]⟩
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨r, hr, rfl⟩ := (Ideal.mem_map_iff_of_surjective (f : R →+* R') f.surjective).mp hs
    exact ⟨algebraMap R K r, ⟨r, hr, rfl⟩, by
      erw [IsFractionRing.semilinearEquivOfRingEquiv_algebraMap]; rfl⟩

end RingEquiv

end FractionalIdeal

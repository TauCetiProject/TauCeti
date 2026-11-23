/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RamificationInertia.Ramification
import TauCeti.RingTheory.Length
import TauCeti.RingTheory.LocalRing.Localization

/-!
# Ramification index under localization

This file relates `Ideal.ramificationIdx` at a prime to local rings:

* `IsLocalRing.ramificationIdx_maximalIdeal`,
  `IsLocalRing.ramificationIdx_maximalIdeal_of_isLocalHom`,
  `IsLocalRing.ramificationIdx_maximalIdeal_eq_one_iff`: length characterization of
  `(maximalIdeal S).ramificationIdx R`.
* `Ideal.ramificationIdx_maximalIdeal_localization`,
  `Ideal.ramificationIdx_maximalIdeal_localization_of_liesOver`: localization invariance.
-/

public section

namespace IsLocalRing

/-- For a local `R`-algebra `S`, the ramification index of `maximalIdeal S` over `R` is the
`S`-length of `S ⧸ ((maximalIdeal S).under R) S`. -/
theorem ramificationIdx_maximalIdeal {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing S]
    [Algebra R S] :
    (maximalIdeal S).ramificationIdx R =
      (Module.length S (S ⧸ ((maximalIdeal S).under R).map (algebraMap R S))).toNat := by
  let Sm := Localization.AtPrime (maximalIdeal S)
  let e : S ≃ₐ[S] Sm := algEquivLocalizationAtMaximalIdeal S S
  have he : (e : S →+* Sm) = algebraMap S Sm :=
    RingHom.ext (algEquivLocalizationAtMaximalIdeal_apply S S)
  have hIJ : (((maximalIdeal S).under R).map (algebraMap R S)).map (e : S →+* Sm) =
      ((maximalIdeal S).under R).map (algebraMap R Sm) := by
    rw [IsScalarTower.algebraMap_eq R S Sm, ← Ideal.map_map, ← he]
  rw [Ideal.ramificationIdx_def, ← hIJ,
    Ideal.length_quotient_map_of_surjective (ψ := (e : S →+* Sm)) _ e.surjective,
    (RingHom.injective_iff_ker_eq_bot (e : S →+* Sm)).mp e.injective, sup_bot_eq]

/-- For a local homomorphism `R → S` of local rings, the ramification index of `maximalIdeal S`
over `R` is the `S`-length of `S ⧸ (maximalIdeal R) S`. -/
theorem ramificationIdx_maximalIdeal_of_isLocalHom {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] :
    (maximalIdeal S).ramificationIdx R =
      (Module.length S (S ⧸ (maximalIdeal R).map (algebraMap R S))).toNat := by
  rw [ramificationIdx_maximalIdeal, Ideal.under, maximalIdeal_comap]

/-- For a local `R`-algebra `S`, `(maximalIdeal S).ramificationIdx R = 1` iff the extended ideal
`((maximalIdeal S).under R) S` is `maximalIdeal S`. -/
theorem ramificationIdx_maximalIdeal_eq_one_iff {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing S] [Algebra R S] :
    (maximalIdeal S).ramificationIdx R = 1 ↔
      ((maximalIdeal S).under R).map (algebraMap R S) = maximalIdeal S := by
  rw [ramificationIdx_maximalIdeal, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
    Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
    IsLocalRing.isMaximal_iff]

end IsLocalRing

namespace Ideal

/-- The ramification index of `maximalIdeal (Localization.AtPrime q)` over `R` equals
`q.ramificationIdx R`. -/
@[simp]
theorem ramificationIdx_maximalIdeal_localization {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (q : Ideal S) [q.IsPrime] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime q)).ramificationIdx R =
      q.ramificationIdx R := by
  rw [IsLocalRing.ramificationIdx_maximalIdeal, ramificationIdx_def,
    ← Ideal.under_under (B := S), Localization.AtPrime.under_maximalIdeal]

/-- The ramification index of `maximalIdeal (Localization.AtPrime q)` over
`Localization.AtPrime p` equals `q.ramificationIdx R` whenever `q` lies over `p`. -/
theorem ramificationIdx_maximalIdeal_localization_of_liesOver {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    [q.LiesOver p] [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q)]
    [IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime q)).ramificationIdx
        (Localization.AtPrime p) = q.ramificationIdx R := by
  rw [IsLocalRing.ramificationIdx_maximalIdeal_of_isLocalHom, ramificationIdx_eq p q,
    ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]

end Ideal

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RamificationInertia.Ramification
import TauCeti.RingTheory.Length
import TauCeti.RingTheory.LocalRing.Localization
import TauCeti.RingTheory.RamificationInertia.Bijective

/-!
# Ramification index under localization

This file relates `Ideal.ramificationIdx` at a prime to local rings:

* `IsLocalRing.ramificationIdx_maximalIdeal`,
  `IsLocalRing.ramificationIdx_maximalIdeal_of_isLocalHom`,
  `IsLocalRing.ramificationIdx_maximalIdeal_eq_one_iff`,
  `IsLocalRing.ramificationIdx_maximalIdeal_eq_one_iff_of_isLocalHom`: length characterization of
  `(maximalIdeal S).ramificationIdx R`.
* `Ideal.ramificationIdx_maximalIdeal_localization`,
  `Ideal.ramificationIdx_maximalIdeal_localization_of_liesOver`: localization invariance.
* `Ideal.ramificationIdx_maximalIdeal_eq_of_ringEquiv_square`: invariance under a commuting square
  of ring isomorphisms of local rings.
* `Ideal.ramificationIdx_eq_of_isLocalHom_square`: horizontal invariance in a local-ring square
  with vertical ramification indices `1` (flatness only on `A → B`).
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

/-- For a local homomorphism `R → S` of local rings, `(maximalIdeal S).ramificationIdx R = 1` iff
the extended maximal ideal `(maximalIdeal R) S` is `maximalIdeal S`. -/
theorem ramificationIdx_maximalIdeal_eq_one_iff_of_isLocalHom {R S : Type*} [CommRing R]
    [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] :
    (maximalIdeal S).ramificationIdx R = 1 ↔
      (maximalIdeal R).map (algebraMap R S) = maximalIdeal S := by
  rw [ramificationIdx_maximalIdeal_eq_one_iff, Ideal.under, maximalIdeal_comap]

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

/-- **Comparison of ramification indices in a square of local rings.** Suppose `R → S → B` and
`R → A → B` commute, `S, A, B` are local rings, `S → B` and `A → B` are local homomorphisms, `A → B`
is flat, `(maximalIdeal B).ramificationIdx A = 1`, and `(maximalIdeal S).ramificationIdx R = 1`.
Then `(maximalIdeal B).ramificationIdx S = (maximalIdeal A).ramificationIdx R`, with no flatness
assumption on `R → A` or `S → B`. -/
theorem ramificationIdx_eq_of_isLocalHom_square {R S A B : Type*} [CommRing R] [CommRing S]
    [CommRing A] [CommRing B] [IsLocalRing S] [IsLocalRing A] [IsLocalRing B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S B] [Algebra A B]
    [IsScalarTower R S B] [IsScalarTower R A B]
    [IsLocalHom (algebraMap S B)] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (hAB : (IsLocalRing.maximalIdeal B).ramificationIdx A = 1)
    (hRS : (IsLocalRing.maximalIdeal S).ramificationIdx R = 1) :
    (IsLocalRing.maximalIdeal B).ramificationIdx S =
      (IsLocalRing.maximalIdeal A).ramificationIdx R := by
  have : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  have hunder : (IsLocalRing.maximalIdeal B).under S = IsLocalRing.maximalIdeal S :=
    IsLocalRing.maximalIdeal_comap (algebraMap S B)
  have hBS : (IsLocalRing.maximalIdeal B).ramificationIdx S =
      (IsLocalRing.maximalIdeal B).ramificationIdx R := by
    rw [IsLocalRing.ramificationIdx_maximalIdeal_of_isLocalHom,
      IsLocalRing.ramificationIdx_maximalIdeal, ← Ideal.under_under (B := S), hunder,
      IsScalarTower.algebraMap_eq R S B, ← Ideal.map_map,
      IsLocalRing.ramificationIdx_maximalIdeal_eq_one_iff.mp hRS]
  rw [hBS, ramificationIdx_tower (R := R) (IsLocalRing.maximalIdeal A)
    (IsLocalRing.maximalIdeal B), hAB, mul_one]

/-- For local rings related by a commuting square of ring isomorphisms, the ramification indices
of their maximal ideals agree. -/
theorem ramificationIdx_maximalIdeal_eq_of_ringEquiv_square {R₁ R₂ S₁ S₂ : Type*}
    [CommRing R₁] [CommRing R₂] [CommRing S₁] [CommRing S₂]
    [IsLocalRing S₁] [IsLocalRing S₂] [Algebra R₁ S₁] [Algebra R₂ S₂]
    (eR : R₁ ≃+* R₂) (eS : S₁ ≃+* S₂)
    (he : ∀ r : R₁, eS (algebraMap R₁ S₁ r) = algebraMap R₂ S₂ (eR r)) :
    (IsLocalRing.maximalIdeal S₂).ramificationIdx R₂ =
      (IsLocalRing.maximalIdeal S₁).ramificationIdx R₁ := by
  let : Algebra R₁ R₂ := eR.toRingHom.toAlgebra
  let : Algebra R₁ S₂ := (eS.toRingHom.comp (algebraMap R₁ S₁)).toAlgebra
  have : IsScalarTower R₁ R₂ S₂ := .of_algebraMap_eq fun r ↦ he r
  let e : S₁ ≃ₐ[R₁] S₂ := AlgEquiv.ofRingEquiv (f := eS) fun _ ↦ rfl
  have : IsLocalHom e.toRingHom := ⟨fun a ha ↦ (isUnit_map_iff e a).mp ha⟩
  have hmax : (IsLocalRing.maximalIdeal S₁).map e = IsLocalRing.maximalIdeal S₂ := by
    rw [← IsLocalRing.maximalIdeal_comap e.toRingHom]
    exact map_comap_of_surjective _ e.surjective _
  rw [ramificationIdx_eq_of_surjective (R := R₁) (S := R₂) eR.surjective, ← hmax,
    ramificationIdx_map_algEquiv e]

end Ideal

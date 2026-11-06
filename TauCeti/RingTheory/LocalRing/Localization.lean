/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Localization at the maximal ideal of a local ring and at its preimages

Every element of a local ring `S` outside its maximal ideal is a unit, so the localization of `S`
at its maximal ideal inverts only units and is `S` itself (Mathlib `IsLocalization.atUnits`).
This file names that equivalence, as an isomorphism of `R`-algebras for any `R`-algebra
structure on `S`, so that statements about `Localization.AtPrime (maximalIdeal S)` transfer to
`S` along a single map.

More generally, a ring homomorphism `f : A →+* R` to a local ring extends to the localization of
`A` at the preimage `f⁻¹(𝔪_R)`, and this extension maps the maximal ideal into `𝔪_R`. Hence an
element whose image under `f` lies outside `𝔪_Rⁿ` stays outside the `n`-th power of the maximal
ideal of that localization. For `f` the constant coefficient map of a polynomial ring over `R`,
this says that a polynomial whose constant coefficient lies outside `𝔪_R²` does not lie in the
square of the maximal ideal of the polynomial ring localized at `(𝔪_R, X_i)`.

## Main results

* `IsLocalRing.algEquivLocalizationAtMaximalIdeal R S`: the `R`-algebra isomorphism from a local
  ring `S` to its localization at its maximal ideal.
* `TauCeti.algebraMap_notMem_maximalIdeal_pow`: an element whose image under `f : A →+* R` is not
  in `𝔪_Rⁿ` does not lie in the `n`-th power of the maximal ideal of `A` localized at `f⁻¹(𝔪_R)`.
-/

public section

namespace IsLocalRing

variable (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] [IsLocalRing S]

/-- A local `R`-algebra `S` is isomorphic, as an `R`-algebra, to its localization at its maximal
ideal: that localization inverts only units. -/
noncomputable def algEquivLocalizationAtMaximalIdeal :
    S ≃ₐ[R] Localization.AtPrime (maximalIdeal S) :=
  (IsLocalization.atUnits S (maximalIdeal S).primeCompl
    fun _ hx ↦ notMem_maximalIdeal.mp hx).restrictScalars R

/-- The local-ring equivalence maps an element to its image in the localization. -/
@[simp]
theorem algEquivLocalizationAtMaximalIdeal_apply (s : S) :
    algEquivLocalizationAtMaximalIdeal R S s =
      algebraMap S (Localization.AtPrime (maximalIdeal S)) s :=
    by
      simpa only [algEquivLocalizationAtMaximalIdeal, AlgEquiv.restrictScalars_apply,
        Algebra.algebraMap_self_apply] using
        (IsLocalization.atUnits S (maximalIdeal S).primeCompl
          fun _ hx ↦ notMem_maximalIdeal.mp hx).commutes s

end IsLocalRing

namespace TauCeti

open _root_.IsLocalRing Ideal

variable {A R : Type*} [CommSemiring A] [CommSemiring R] [IsLocalRing R]

/-- Let `f : A →+* R` be a ring homomorphism to a local ring. An element of `A` whose image under
`f` is not in `𝔪_Rⁿ` does not lie in the `n`-th power of the maximal ideal of the localization of
`A` at `f⁻¹(𝔪_R)`: `f` extends to that localization, mapping its maximal ideal into `𝔪_R`. -/
theorem algebraMap_notMem_maximalIdeal_pow {f : A →+* R} {n : ℕ} {a : A}
    (ha : f a ∉ maximalIdeal R ^ n) :
    algebraMap A (Localization.AtPrime ((maximalIdeal R).comap f)) a ∉
      maximalIdeal (Localization.AtPrime ((maximalIdeal R).comap f)) ^ n := by
  let φ : Localization.AtPrime ((maximalIdeal R).comap f) →+* R :=
    IsLocalization.lift (M := ((maximalIdeal R).comap f).primeCompl) (g := f) fun s ↦
      notMem_maximalIdeal.mp s.2
  have hφ : φ.comp (algebraMap _ _) = f := IsLocalization.lift_comp _
  have hmap : (maximalIdeal (Localization.AtPrime ((maximalIdeal R).comap f))).map φ ≤
      maximalIdeal R := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, hφ]
    exact map_comap_le
  intro h
  apply ha
  rw [← hφ, RingHom.comp_apply]
  exact pow_right_mono hmap n (Ideal.map_pow φ _ n ▸ mem_map_of_mem φ h)

end TauCeti

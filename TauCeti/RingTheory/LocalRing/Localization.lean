/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang, The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Localization at the maximal ideal of a local ring and at its preimages, and local lifts

Every element of a local ring `S` outside its maximal ideal is a unit, so the localization of `S`
at its maximal ideal inverts only units and is `S` itself (Mathlib `IsLocalization.atUnits`).
This file names that equivalence, as an isomorphism of `R`-algebras for any `R`-algebra
structure on `S`, so that statements about `Localization.AtPrime (maximalIdeal S)` transfer to
`S` along a single map.

More generally, if a prime ideal `q` of an `R`-algebra `S` lies over the maximal ideal of a local
ring `R`, then the algebra map from `R` to any localization of `S` at `q` is local. Likewise, a ring
homomorphism `f : A →+* R` to a local ring extends to the localization of `A` at the preimage
`f⁻¹(𝔪_R)`, and this extension maps the maximal ideal into `𝔪_R`. Hence an element whose image under
`f` lies outside `𝔪_Rⁿ` stays outside the `n`-th power of the maximal ideal of that localization.
For `f` the constant coefficient map of a polynomial ring over `R`, this says that a polynomial
whose constant coefficient lies outside `𝔪_R²` does not lie in the square of the maximal ideal of
the polynomial ring localized at `(𝔪_R, X_i)`.

A homomorphism `ψ : R →+* T` to a local ring which inverts the complement of a prime
`p` and maps `p` into the maximal ideal lifts to a local homomorphism from the localization of `R`
at `p`. For instance, a homomorphism to a field factors locally through the localization at its
kernel.

## Main results

* `IsLocalRing.algEquivLocalizationAtMaximalIdeal R S`: the `R`-algebra isomorphism from a local
  ring `S` to its localization at its maximal ideal.
* `IsLocalization.AtPrime.isLocalHom_lift`: the lift of a homomorphism to a local ring along the
  localization at a prime mapped into the maximal ideal is local.
* `IsLocalization.AtPrime.isLocalHom_algebraMap_of_liesOver` and
  `Localization.AtPrime.isLocalHom_algebraMap_of_liesOver`: if `q` lies over `maximalIdeal R`, the
  algebra map from `R` to a localization at `q` is local.
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

namespace IsLocalization.AtPrime

open IsLocalRing

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T] [Algebra R S]
  [IsLocalRing T] (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime S p]

/-- Let `ψ : R →+* T` be a homomorphism to a local ring which inverts the complement of a prime `p`
and maps `p` into the maximal ideal. Its lift to the localization `S` of `R` at `p` is a local
homomorphism. For `T` a field, `p` can be the kernel of `ψ`. -/
theorem isLocalHom_lift {ψ : R →+* T} (hψ : ∀ y : p.primeCompl, IsUnit (ψ y))
    (hp : p ≤ (maximalIdeal T).comap ψ) : IsLocalHom (IsLocalization.lift hψ : S →+* T) := by
  refine ⟨fun z hz ↦ ?_⟩
  obtain ⟨⟨r, y⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
  rw [IsLocalization.AtPrime.isUnit_mk'_iff S p]
  intro hr
  have hr' : ψ r = ψ y * IsLocalization.lift hψ (IsLocalization.mk' S r y) :=
    (IsLocalization.lift_mk'_spec _ _ _ _).mp rfl
  exact hp hr (hr' ▸ (hψ y).mul hz)

/-- If `q` is a prime ideal of an `R`-algebra `S` lying over the maximal ideal of the local ring
`R`, then the algebra map from `R` to any localization `T` of `S` at `q` is local. -/
theorem isLocalHom_algebraMap_of_liesOver {R S T : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalRing R] (q : Ideal S) [q.IsPrime] [IsLocalization.AtPrime T q]
    [q.LiesOver (maximalIdeal R)] :
    IsLocalHom (algebraMap R T) :=
  ⟨fun r hr ↦ by
    by_contra hr'
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff T q (algebraMap R S r)).mpr
      ((Ideal.mem_of_liesOver q (maximalIdeal R) r).mp ((mem_maximalIdeal r).mpr hr'))
      (by rwa [IsScalarTower.algebraMap_apply R S T] at hr)⟩

end IsLocalization.AtPrime

namespace Localization.AtPrime

/-- If `q` is a prime ideal of an `R`-algebra `S` lying over the maximal ideal of the local ring
`R`, then `algebraMap R (Localization.AtPrime q)` is a local homomorphism. -/
theorem isLocalHom_algebraMap_of_liesOver {R S : Type*} [CommSemiring R] [CommSemiring S]
    [Algebra R S] [IsLocalRing R] (q : Ideal S) [q.IsPrime]
    [q.LiesOver (IsLocalRing.maximalIdeal R)] :
    IsLocalHom (algebraMap R (Localization.AtPrime q)) :=
  IsLocalization.AtPrime.isLocalHom_algebraMap_of_liesOver q

end Localization.AtPrime

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
      notMem_maximalIdeal.mp s.property
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

/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Localization at the maximal ideal of a local ring, and local lifts

Every element of a local ring `S` outside its maximal ideal is a unit, so the localization of `S`
at its maximal ideal inverts only units and is `S` itself (Mathlib `IsLocalization.atUnits`).
This file names that equivalence, as an isomorphism of `R`-algebras for any `R`-algebra
structure on `S`, so that statements about `Localization.AtPrime (maximalIdeal S)` transfer to
`S` along a single map.

A homomorphism `ψ : R →+* T` to a local ring which inverts the complement of a prime
`p` and maps `p` into the maximal ideal lifts to a local homomorphism from the localization of `R`
at `p`. For instance, a homomorphism to a field factors locally through the localization at its
kernel.

## Main results

* `IsLocalRing.algEquivLocalizationAtMaximalIdeal R S`: the `R`-algebra isomorphism from a local
  ring `S` to its localization at its maximal ideal.
* `IsLocalization.AtPrime.isLocalHom_lift`: the lift of a homomorphism to a local ring along the
  localization at a prime mapped into the maximal ideal is local.
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

end IsLocalization.AtPrime

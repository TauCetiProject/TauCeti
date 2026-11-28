/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
public import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.RingTheory.Ideal.UFD
import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension
import TauCeti.RingTheory.LocalProperties.StablyFree
import Mathlib.Algebra.Module.StablyFree.FreeOfInvertible
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Regular local rings are factorial

A regular local ring is a unique factorization domain. We induct on its dimension and invert
a prime parameter. The localizations of the resulting ring at maximal ideals come from
nonmaximal prime ideals of the original ring, so they are factorial by induction.
A height-one prime of the resulting ring is therefore invertible. As the localization of a
finite module over the original regular local ring, it has a finite free resolution; being
projective, it is stably free. An invertible stably free module is free, so every height-one
prime is principal. Mathlib's localization criterion then proves factoriality of the
original ring.

## References

* [The Stacks Project, Tag 0AG0](https://stacks.math.columbia.edu/tag/0AG0).
* H. Matsumura, *Commutative Ring Theory*, Theorem 20.3 (Auslander–Buchsbaum): regular local
  rings are unique factorization domains.
-/

public section

open IsLocalRing

namespace TauCeti.IsRegularLocalRing

universe u

private theorem uniqueFactorizationMonoid_localizationAway {R : Type u} [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ≠ 0) (hxm : x ∈ maximalIdeal R)
    (hloc : ∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R →
      UniqueFactorizationMonoid (Localization.AtPrime p)) :
    UniqueFactorizationMonoid (Localization.Away x) := by
  let S := Localization.Away x
  have : IsDomain S := IsLocalization.Away.isDomain S hx
  refine UniqueFactorizationMonoid.of_forall_isPrincipal_of_height_eq_one fun P _ hP ↦ ?_
  have : Module.Finite S P := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian P)
  have : Module.Invertible S P := P.moduleInvertible_of_height_eq_one hP fun m _ _ ↦ by
    have hm : m.comap (algebraMap R S) ≠ maximalIdeal R := by
      intro heq
      have hxm' : algebraMap R S x ∈ m := by
        rw [← Ideal.mem_comap, heq]
        exact hxm
      exact (Ideal.IsPrime.ne_top inferInstance) (Ideal.eq_top_of_isUnit_mem _ hxm'
        (IsLocalization.Away.algebraMap_isUnit x))
    have := hloc _ hm
    exact MulEquiv.uniqueFactorizationMonoid
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization (.powers x) m).toMulEquiv
      inferInstance
  let Q := P.comap (algebraMap R S)
  have hQ : Q.localized' S (.powers x) (Algebra.linearMap R S) = P := by
    rw [Ideal.localized'_eq_map]
    exact IsLocalization.map_under (.powers x) S P
  have : Module.Invertible S (Q.localized' S (.powers x) (Algebra.linearMap R S)) :=
    Module.Invertible.congr (LinearEquiv.ofEq _ _ hQ.symm)
  have hd := hasProjectiveDimensionLE_spanFinrank_maximalIdeal (ModuleCat.of R Q)
  have := Module.isStablyFree_of_isLocalizedModule_of_hasProjectiveDimensionLE (.powers x)
    _ Q hd _ (Q.toLocalized' S (.powers x) (Algebra.linearMap R S))
  have := Module.free_of_isStablyFree_of_invertible S
    (Q.localized' S (.powers x) (Algebra.linearMap R S))
  obtain ⟨e⟩ := Module.Invertible.free_iff_linearEquiv.mp this
  rw [← hQ]
  exact ⟨_, Submodule.eq_span_singleton_of_surjective e.symm.surjective⟩

private theorem uniqueFactorizationMonoid_of_spanFinrank_eq (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
      (maximalIdeal R).spanFinrank = n → UniqueFactorizationMonoid R := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro R _ _ hn
    have hloc (p : Ideal R) [p.IsPrime] (hp : p ≠ maximalIdeal R) :
        UniqueFactorizationMonoid (Localization.AtPrime p) := by
      refine ih (maximalIdeal (Localization.AtPrime p)).spanFinrank ?_
        (Localization.AtPrime p) rfl
      simpa only [hn] using spanFinrank_maximalIdeal_localization_lt p hp
    by_cases hfield : IsField R
    · let := hfield.toField
      infer_instance
    obtain ⟨x, hxm, hx2⟩ :=
      IsConcreteLE.exists_of_lt ((maximalIdeal_sq_lt_maximalIdeal R).mpr hfield)
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx2 (zero_mem _)
    have := quotient_span_singleton hxm hx2
    have hxprime : Prime x := (Ideal.span_singleton_prime hx0).mp
      ((Ideal.Quotient.isDomain_iff_prime _).mp inferInstance)
    have := uniqueFactorizationMonoid_localizationAway hx0 hxm hloc
    exact (UniqueFactorizationMonoid.iff_localizationAway_of_prime hxprime).mpr inferInstance

/-- Every regular local ring is a unique factorization domain. -/
@[stacks 0AG0]
instance uniqueFactorizationMonoid {R : Type u} [CommRing R] [IsRegularLocalRing R] :
    UniqueFactorizationMonoid R :=
  uniqueFactorizationMonoid_of_spanFinrank_eq _ R rfl

end TauCeti.IsRegularLocalRing

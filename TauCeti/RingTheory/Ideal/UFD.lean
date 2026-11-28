/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.Ideal.IsPrincipal
public import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.LocalProperties.Invertible
import Mathlib.RingTheory.Localization.Submodule

/-!
# Height-one ideals on locally factorial rings

A finitely generated height-one prime ideal in a domain is invertible if its localizations at
maximal ideals containing it are factorial. Its localizations are nonzero principal ideals,
hence free of rank one. Invertibility is local at maximal ideals, so the original ideal is
invertible.
-/

public section

namespace Ideal

variable {R : Type*} [CommRing R] [IsDomain R]

/-- A finitely generated height-one prime in a domain is invertible if the localizations at maximal
ideals containing it are factorial. -/
theorem moduleInvertible_of_height_eq_one (P : Ideal R) [P.IsPrime]
    [Module.Finite R P] (hP : P.height = 1)
    (hloc : ∀ (m : Ideal R) [m.IsMaximal], P ≤ m →
      UniqueFactorizationMonoid (Localization.AtPrime m)) : Module.Invertible R P := by
  have hP0 : P ≠ ⊥ := P.ne_bot_of_height_eq_one hP
  refine Module.Invertible.of_isLocalized_maximal
    (fun m _ ↦ Localization.AtPrime m)
    (fun m _ ↦ P.localized' (Localization.AtPrime m) m.primeCompl
      (Algebra.linearMap R (Localization.AtPrime m)))
    (fun m _ ↦ P.toLocalized' (Localization.AtPrime m) m.primeCompl
      (Algebra.linearMap R (Localization.AtPrime m))) ?_
  intro m _
  let S := Localization.AtPrime m
  have hinj : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S m.primeCompl_le_nonZeroDivisors
  have hmap0 : P.map (algebraMap R S) ≠ ⊥ := by
    exact fun h ↦ hP0 ((Ideal.map_eq_bot_iff_of_injective hinj).mp h)
  have : (P.map (algebraMap R S)).IsPrincipal := by
    by_cases hPm : P ≤ m
    · have : UniqueFactorizationMonoid S := hloc m hPm
      have hd : Disjoint (m.primeCompl : Set R) P :=
        Set.disjoint_left.mpr fun a ha hPa ↦ ha (hPm hPa)
      have := IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl S P inferInstance hd
      apply UniqueFactorizationMonoid.isPrincipal_of_height_eq_one
      rw [← IsLocalization.height_under m.primeCompl,
        IsLocalization.under_map_of_isPrime_disjoint m.primeCompl S inferInstance hd, hP]
    · have htop : P.map (algebraMap R S) = ⊤ := by
        obtain ⟨a, haP, ham⟩ := IsConcreteLE.not_le_iff_exists.mp hPm
        exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ haP)
          (IsLocalization.map_units S (⟨a, ham⟩ : m.primeCompl))
      rw [htop]
      infer_instance
  have : Module.Invertible S (P.map (algebraMap R S)) :=
    Module.Invertible.congr (Ideal.isoBaseOfIsPrincipal hmap0)
  exact Module.Invertible.congr (LinearEquiv.ofEq _ _
    (Ideal.localized'_eq_map S m.primeCompl P).symm)

end Ideal

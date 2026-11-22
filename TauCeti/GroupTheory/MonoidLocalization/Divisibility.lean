/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Divisibility

/-!
# Relative primality and squarefreeness in localizations of monoids

In a decomposition monoid, relatively prime elements stay relatively prime in every
localization (`Submonoid.LocalizationMap.map_isRelPrime`), and with cancellation squarefree
elements stay squarefree (`Submonoid.LocalizationMap.map_squarefree`). Both lift divisibility
in the localization with Mathlib's `Submonoid.LocalizationMap.map_dvd_map` and detect units with
`Submonoid.LocalizationMap.map_isUnit_iff`.
-/

public section

namespace Submonoid.LocalizationMap

section CommMonoid

variable {M N : Type*} [CommMonoid M] {S : Submonoid M} [CommMonoid N]
  (f : LocalizationMap S N)

/-- In a decomposition monoid, relatively prime elements stay relatively prime in every
localization. -/
theorem map_isRelPrime [DecompositionMonoid M] {x y : M} (h : IsRelPrime x y) :
    IsRelPrime (f x) (f y) := by
  intro d hx hy
  obtain ⟨⟨a, s⟩, hd⟩ := f.surj d
  have hs := f.map_units s
  refine isUnit_of_mul_isUnit_left (hd ▸ f.map_isUnit_iff.2 ?_)
  obtain ⟨m₁, hm₁, ha₁⟩ := f.map_dvd_map.1 (hd ▸ hs.mul_right_dvd.2 hx)
  obtain ⟨m₂, hm₂, ha₂⟩ := f.map_dvd_map.1 (hd ▸ hs.mul_right_dvd.2 hy)
  obtain ⟨a₁, a₂, h₁, h₂, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul ha₁
  exact ⟨m₁ * m₂, mul_mem hm₁ hm₂, mul_dvd_mul h₁
    ((h.of_dvd_left h₂).dvd_of_dvd_mul_right ((dvd_mul_left a₂ a₁).trans ha₂))⟩

end CommMonoid

section CommMonoidWithZero

variable {M N : Type*} [CommMonoidWithZero M] {S : Submonoid M} [CommMonoid N]
  (f : LocalizationMap S N)

/-- In a cancellative decomposition monoid, squarefree elements stay squarefree in every
localization. -/
theorem map_squarefree [IsCancelMulZero M] [DecompositionMonoid M] {x : M} (hx : Squarefree x) :
    Squarefree (f x) := by
  intro d hd
  obtain ⟨⟨a, s⟩, hda⟩ := f.surj d
  have hs := f.map_units s
  refine isUnit_of_mul_isUnit_left (hda ▸ f.map_isUnit_iff.2 ?_)
  obtain ⟨m, hm, ham⟩ := f.map_dvd_map.1 (show f (a * a) ∣ f x by
    rwa [map_mul, ← hda, mul_mul_mul_comm, (hs.mul hs).mul_right_dvd])
  exact ⟨m, hm, hx.dvd_of_squarefree_of_mul_dvd_mul_left ham⟩

end CommMonoidWithZero

end Submonoid.LocalizationMap

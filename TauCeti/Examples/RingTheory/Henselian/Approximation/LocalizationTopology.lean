/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselian.Approximation.LocalizationTopology

/-!
# Checks for localized approximation topologies

The coefficient ring `ℤ[1/3]` contains an open copy of `ℤ` but is not discrete.
Its first basic subgroup does not contain `1`, even though `3` is a unit in the
localized ring. This distinguishes additive images from extended ideals.
We also test discreteness for `I = ⊥` and indiscreteness for `t = 1`, `I = ⊤`.
-/

public section

open Topology
open TauCeti.HenselianApproximation

namespace TauCeti.HenselianApproximation.LocalizationChecks

/-- *localized_zero_ideal*: the zero ideal gives the discrete topology. -/
example : localizedTopology (3 : ℤ) ⊥ (Localization.Away (3 : ℤ)) = ⊥ := by simp

/-- *localized_unit_total_ideal*: parameter `1` and total ideal give the indiscrete topology. -/
example :
    letI := IsLocalization.away_of_isUnit_of_bijective ℤ (isUnit_one : IsUnit (1 : ℤ))
      Function.bijective_id
    localizedTopology (1 : ℤ) ⊤ ℤ = ⊤ := by
  let := IsLocalization.away_of_isUnit_of_bijective ℤ (isUnit_one : IsUnit (1 : ℤ))
    Function.bijective_id
  exact localizedTopology_one_top ℤ

/-- *localized_integer_three*: the image of `ℤ` is open in `ℤ[1/3]`. -/
example :
    IsOpen[localizedTopology (3 : ℤ) ⊤ (Localization.Away (3 : ℤ))]
      (Set.range (algebraMap ℤ (Localization.Away (3 : ℤ)))) := by
  let := ringTopology (3 : ℤ) ⊤
  let := localizedTopology (3 : ℤ) ⊤ (Localization.Away (3 : ℤ))
  exact (isOpenMap_algebraMap_localizedTopology (3 : ℤ) ⊤ _).isOpen_range

/-- *localized_integer_three_not_discrete*: zero is not open in `ℤ[1/3]`. -/
example :
    ¬ IsOpen[localizedTopology (3 : ℤ) ⊤ (Localization.Away (3 : ℤ))]
      ({0} : Set (Localization.Away (3 : ℤ))) := by
  let S := Localization.Away (3 : ℤ)
  let := localizedTopology (3 : ℤ) ⊤ S
  have hinj : Function.Injective (algebraMap ℤ S) :=
    IsLocalization.injective S
      (powers_le_nonZeroDivisors_of_noZeroDivisors (by norm_num : (3 : ℤ) ≠ 0))
  intro h
  obtain ⟨n, _, hn⟩ := (hasBasis_nhds_zero_localizedTopology (3 : ℤ) ⊤ S).mem_iff.mp
    (h.mem_nhds (by simp))
  have hx : algebraMap ℤ S (3 ^ n) ∈ localizedSubgroup (3 : ℤ) ⊤ S n :=
    (mem_localizedSubgroup_iff (3 : ℤ) ⊤ S n _).mpr ⟨1, by simp, by simp⟩
  have hz : (3 : ℤ) ^ n = 0 := hinj (by simpa using hn hx)
  exact pow_ne_zero n (by norm_num) hz

/-- *localized_images_not_extended_ideals*: `3` is a unit after localization, but the
additive image of `3ℤ` does not contain `1`. -/
example :
    IsUnit (algebraMap ℤ (Localization.Away (3 : ℤ)) 3) ∧
      (1 : Localization.Away (3 : ℤ)) ∉
        localizedSubgroup (3 : ℤ) ⊤ (Localization.Away (3 : ℤ)) 1 := by
  refine ⟨IsLocalization.Away.algebraMap_isUnit 3, ?_⟩
  intro h
  obtain ⟨a, _, ha⟩ := (mem_localizedSubgroup_iff (3 : ℤ) ⊤ _ 1 1).mp h
  have hinj := IsLocalization.injective (Localization.Away (3 : ℤ))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (by norm_num : (3 : ℤ) ≠ 0))
  have heq : (3 : ℤ) * a = 1 := hinj (by simpa using ha)
  omega

end TauCeti.HenselianApproximation.LocalizationChecks

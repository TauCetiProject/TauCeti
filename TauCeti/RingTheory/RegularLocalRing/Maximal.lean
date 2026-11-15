/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension

/-!
# Testing regularity at maximal ideals

A noetherian ring is regular if and only if its localizations at maximal ideals are regular
local rings. Indeed, every prime is contained in a maximal ideal, and its localization is a
localization of that regular local ring. This criterion lets maximal-ideal computations establish
regularity without repeating those computations at nonmaximal primes.

## References

* Stacks Project, Section 10.110, especially Lemma 10.110.6 (Tag 0AFS): localizations of regular
  local rings are regular local rings.
-/

public section

namespace TauCeti

/-- A noetherian ring is regular exactly when its localizations at maximal ideals are regular
local rings. -/
theorem isRegularRing_iff_localization_maximal (R : Type*) [CommRing R] [IsNoetherianRing R] :
    IsRegularRing R ↔ ∀ (m : Ideal R) [m.IsMaximal],
      IsRegularLocalRing (Localization.AtPrime m) := by
  refine ⟨fun _ _ _ ↦ inferInstance, fun h ↦ isRegularRing_iff.mpr fun p _ ↦ ?_⟩
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p Ideal.IsPrime.ne_top'
  let := hm
  let := h m
  let S := Localization.AtPrime m
  let T := Localization.AtPrime p
  have hle : m.primeCompl ≤ p.primeCompl := fun _ hs hp ↦ hs (hpm hp)
  let : Algebra S T := IsLocalization.localizationAlgebraOfSubmonoidLe S T
    m.primeCompl p.primeCompl hle
  let : IsScalarTower R S T := IsLocalization.localization_isScalarTower_of_submonoid_le
    S T m.primeCompl p.primeCompl hle
  let : IsLocalization (p.primeCompl.map (algebraMap R S)) T :=
    IsLocalization.isLocalization_of_submonoid_le S T m.primeCompl p.primeCompl hle
  have : IsRegularRing S := inferInstance
  have : IsRegularRing T := IsRegularRing.of_isLocalization
    (p.primeCompl.map (algebraMap R S)) T
  exact _root_.IsRegularLocalRing.of_isRegularRing_of_isLocalRing T

end TauCeti

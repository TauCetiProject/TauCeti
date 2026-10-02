/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Flat.Localization

/-!
# Nonemptiness of the free locus over a reduced ring

Every module over a nonzero reduced ring is free at some minimal prime. For a finitely
presented module, Mathlib's openness of the free locus therefore gives a nonempty open
set where it is locally free. This is the generic-freeness input for finite morphisms.

## References

* The Stacks Project, Tag 051Z, for the more general generic-freeness theorem.
-/

public section

namespace Module

variable (R M : Type*) [CommRing R] [IsReduced R] [Nontrivial R]
  [AddCommGroup M] [Module R M]

/-- A module over a nonzero reduced ring has nonempty free locus. -/
theorem freeLocus_nonempty : (freeLocus R M).Nonempty := by
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes (R := R) (I := ⊥) bot_ne_top
  have := hp.1.1
  have : Ring.KrullDimLE 0 (Localization.AtPrime p) := .of_isLocalization p hp _
  let : Field (Localization.AtPrime p) := Ring.KrullDimLE.isField_of_isReduced.toField
  exact ⟨⟨p, inferInstance⟩, Module.Free.of_divisionRing _ _⟩

end Module

namespace PrimeSpectrum

open Module

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- If a base prime belongs to the free locus of an algebra, that algebra is flat
over the base after localizing at any prime above it. -/
theorem flat_localization_of_comap_mem_freeLocus (q : PrimeSpectrum S)
    (hq : q.comap (algebraMap R S) ∈ freeLocus R S) :
    Flat R (Localization.AtPrime q.asIdeal) := by
  let p := q.comap (algebraMap R S)
  let U := Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl
  let B := Localization U
  have hU : U ≤ q.asIdeal.primeCompl := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  let : Algebra B (Localization.AtPrime q.asIdeal) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ U q.asIdeal.primeCompl hU
  have : IsScalarTower S B (Localization.AtPrime q.asIdeal) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ U q.asIdeal.primeCompl hU
  have : IsScalarTower R B (Localization.AtPrime q.asIdeal) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [IsScalarTower.algebraMap_eq R S B, ← RingHom.comp_assoc,
        ← IsScalarTower.algebraMap_eq S B (Localization.AtPrime q.asIdeal),
        ← IsScalarTower.algebraMap_eq R S (Localization.AtPrime q.asIdeal)])
  have : Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl S) := hq
  have : Flat R (Localization.AtPrime p.asIdeal) :=
    IsLocalization.flat _ p.asIdeal.primeCompl
  have : Flat R (LocalizedModule p.asIdeal.primeCompl S) :=
    Flat.trans R (Localization.AtPrime p.asIdeal) _
  have : Flat R B := Flat.of_linearEquiv
    (IsLocalizedModule.iso p.asIdeal.primeCompl (IsScalarTower.toAlgHom R S B).toLinearMap).symm
  have : IsLocalization (q.asIdeal.primeCompl.map (algebraMap S B))
      (Localization.AtPrime q.asIdeal) :=
    IsLocalization.isLocalization_of_submonoid_le B _ U q.asIdeal.primeCompl hU
  have : Flat B (Localization.AtPrime q.asIdeal) :=
    IsLocalization.flat _ (q.asIdeal.primeCompl.map (algebraMap S B))
  exact Flat.trans R B _

end PrimeSpectrum

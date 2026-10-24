/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Etale.Torsor

/-!
# Tests for finite étale torsors

A finite Galois extension is a torsor under its Galois group, and a field with a faithful action
of a finite group is a torsor over its fixed field. Over the zero ring the zero algebra is a
torsor under every finite group, which then does not act faithfully. Over a field the zero
algebra has a bijective Galois map but is not a torsor, because it is not faithfully flat.
-/

namespace TauCeti.Algebra

/-- *test_isGalois*: a finite Galois extension is a torsor under its Galois group, which is then
a Galois group in Mathlib's sense. -/
example (K L : Type*) [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L] :
    IsFiniteEtaleTorsor Gal(L/K) K L ∧ IsGaloisGroup Gal(L/K) K L :=
  ⟨inferInstance, inferInstance⟩

/-- The rank of a finite Galois extension, computed as a torsor, is its degree. -/
example (K L : Type*) [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (p : PrimeSpectrum K) : Module.rankAtStalk (R := K) L p = Module.finrank K L := by
  rw [IsFiniteEtaleTorsor.rankAtStalk_eq_card (G := Gal(L/K)),
    IsGaloisGroup.card_eq_finrank Gal(L/K) K L]

/-- Artin's theorem as a torsor: a field with a faithful action of a finite group is a torsor over
its fixed field. -/
example (G L : Type*) [Group G] [Finite G] [Field L] [MulSemiringAction G L] [FaithfulSMul G L] :
    IsFiniteEtaleTorsor G (FixedPoints.subfield G L) L :=
  IsFiniteEtaleTorsor.iff_isGaloisGroup.mpr inferInstance

/-- *test_zero_ring*: over the zero ring the zero algebra is a torsor under every finite group,
and a nontrivial group does not act faithfully on it. -/
example (G A B : Type*) [Group G] [Finite G] [Nontrivial G] [CommRing A] [CommRing B]
    [Algebra A B] [MulSemiringAction G B] [SMulCommClass G A B] [Subsingleton A] :
    IsFiniteEtaleTorsor G A B ∧ ¬ FaithfulSMul G B := by
  have : Subsingleton B := Module.subsingleton A B
  refine ⟨inferInstance, fun h ↦ ?_⟩
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  exact hg (h.eq_of_smul_eq_smul fun _ ↦ Subsingleton.elim _ _)

/-- *test_field_zero_algebra*: over a field the zero algebra has a bijective Galois map but is
not a torsor. -/
example (G K B : Type*) [Group G] [Finite G] [Field K] [CommRing B] [Algebra K B]
    [MulSemiringAction G B] [SMulCommClass G K B] [Subsingleton B] :
    Function.Bijective (MulSemiringAction.tensorToPi K B G) ∧ ¬ IsFiniteEtaleTorsor G K B := by
  have : Subsingleton (TensorProduct K B B) := Module.subsingleton B _
  refine ⟨⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun f ↦ ⟨0, Subsingleton.elim _ _⟩⟩, fun h ↦ ?_⟩
  obtain ⟨hB, -⟩ := (IsFiniteEtaleTorsor.iff_field K).mp h
  exact not_nontrivial B hB

end TauCeti.Algebra

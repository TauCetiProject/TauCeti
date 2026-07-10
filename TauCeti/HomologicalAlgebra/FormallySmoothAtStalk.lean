/-
Copyright (c) 2026 daouid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Formally Smooth Morphisms at Stalks

This file proves that the stalk map of a smooth morphism of schemes is formally smooth.

This advances the roadmap at TauCetiRoadmap/JacobianChallenge/README.md.

## Important Note

The theorems originally requested (asserting that the stalk map of a smooth morphism
is locally standard smooth) are false, because the stalk map is generally not of
finite presentation. We prove instead that the stalk map is formally smooth.
-/

public section

open AlgebraicGeometry

namespace TauCeti.Theorems.FormallySmoothAtStalk

universe u

section Helper

lemma locally_of_isLocalRing {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing S]
    {P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hPi : RingHom.RespectsIso P) (f : R →+* S) (h : RingHom.Locally P f) : P f := by
  obtain ⟨s, hs, h⟩ := RingHom.locally_iff_isLocalization hPi f |>.mp h
  have ⟨t, hts, ht⟩ := Set.not_subset.mp (fun h_sub =>
    (IsLocalRing.maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (hs ▸ Ideal.span_le.mpr h_sub)))
  haveI : IsLocalization.Away (t : S) S :=
    IsLocalization.away_of_isUnit_of_bijective S
      (IsLocalRing.notMem_maximalIdeal.mp ht) Function.bijective_id
  exact h t hts S

lemma not_isStandardSmoothOfRelativeDimension_ratFunc (K : Type u) [Field K] :
    ¬ Algebra.IsStandardSmoothOfRelativeDimension 1 K (RatFunc K) := by
  intro h
  haveI : Algebra.IsStandardSmooth K (RatFunc K) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  haveI : Algebra.FiniteType K (RatFunc K) := inferInstance
  haveI : Module.Finite K (RatFunc K) :=
    finite_of_finite_type_of_isJacobsonRing K (RatFunc K)
  haveI : Algebra.IsAlgebraic K (RatFunc K) := Algebra.IsIntegral.isAlgebraic
  have ht : Algebra.Transcendental K (RatFunc K) := inferInstance
  rw [Algebra.transcendental_iff_not_isAlgebraic] at ht
  exact ht ‹_›

end Helper

section SmoothStalk

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]

/-- The stalk map of a smooth morphism is **formally** smooth. -/
theorem stalkMap_formallySmooth (x : X.carrier) :
    (f.stalkMap x).hom.FormallySmooth :=
  Scheme.Hom.mem_smoothLocus.mp (f.smoothLocus_eq_top ▸ trivial)

end SmoothStalk

section SmoothOfRelDimStalk

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)

/-- The stalk map of a morphism that is smooth of relative dimension `n` is
**formally** smooth. -/
theorem stalkMap_formallySmooth_of_relDim [SmoothOfRelativeDimension n f]
    (x : X.carrier) :
    (f.stalkMap x).hom.FormallySmooth :=
  haveI := SmoothOfRelativeDimension.smooth n f
  stalkMap_formallySmooth f x

/-- Corrected version of standardSmooth_relDim_at_stalk: stalk map is formally smooth. -/
theorem formallySmooth_stalkMap [SmoothOfRelativeDimension n f] (x : X.carrier) :
    (f.stalkMap x).hom.FormallySmooth :=
  stalkMap_formallySmooth_of_relDim f n x

end SmoothOfRelDimStalk

end TauCeti.Theorems.FormallySmoothAtStalk

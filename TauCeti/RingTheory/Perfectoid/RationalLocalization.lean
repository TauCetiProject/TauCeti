/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Perfect
public import TauCeti.RingTheory.Huber.StableUniform
public import TauCeti.RingTheory.Perfectoid.PerfectRing
import TauCeti.RingTheory.Huber.Perfect

/-!
# Rational localizations of characteristic-`p` perfectoid Tate rings

Completed rational localizations remain perfect and hence perfectoid, including when the
localization is zero. In particular the base is stably uniform, which is used for sheafiness of the
structure presheaf and for rational charts of characteristic-`p` perfectoid spaces. This uses the
characterization of characteristic-`p` perfectoid Tate rings by perfectness in Scholze,
*Étale cohomology of diamonds*, Proposition 3.5.
-/

public section

namespace TauCeti.Perfectoid

open TauCeti.Huber

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A] [UniformSpace A]
  [IsUniformAddGroup A] [IsTopologicalRing A] [T2Space A] [CompleteSpace A] [IsTateRing A]
  [IsPerfectoidTateRing p A]

/-- Frobenius is bijective on the completed rational localization of a characteristic-`p`
perfectoid Tate ring. No nontriviality is required of the base or of the localization. -/
theorem IsPerfectoidTateRing.perfectRing_ratLoc (hp : (p : A) = 0) (P : PairOfDefinition A)
    (T : Finset A) (s : A) (hden : P.HasDenominatorPower T s (Localization.Away s)) :
    PerfectRing (Huber.ratLoc P T s hden) p := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · have : Subsingleton (Huber.ratLoc P T s hden) :=
      (algebraMap A (Huber.ratLoc P T s hden)).codomain_trivial
    exact ⟨Function.bijective_of_subsingleton _⟩
  have : CharP A p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hp
  have := IsPerfectoidTateRing.perfectRing (p := p) (R := A)
  exact P.perfectRing_ratLoc T s hden p
    ((frobeniusEquiv A p).toEquiv.continuous_symm_iff.mpr (isOpenMap_frobenius p))

/-- Completed rational localizations of characteristic-`p` perfectoid Tate rings are perfectoid.
The characteristic assumption is expressed as `p = 0` so that it includes the zero ring. -/
theorem IsPerfectoidTateRing.ratLoc (hp : (p : A) = 0) (P : PairOfDefinition A)
    (T : Finset A) (s : A) (hden : P.HasDenominatorPower T s (Localization.Away s)) :
    IsPerfectoidTateRing p (Huber.ratLoc P T s hden) := by
  let B := Huber.ratLoc P T s hden
  rcases subsingleton_or_nontrivial B with hB | hB
  · exact isPerfectoidTateRing_of_subsingleton p B
  have : CharP B p := (CharP.charP_iff_prime_eq_zero Fact.out).2 (by
    rw [← map_natCast (algebraMap A B), hp, map_zero])
  have := IsPerfectoidTateRing.perfectRing_ratLoc hp P T s hden
  exact IsPerfectoidTateRing.of_perfectRing

/-- A characteristic-`p` perfectoid Tate ring is stably uniform. -/
theorem IsPerfectoidTateRing.isStablyUniform_of_natCast_eq_zero (hp : (p : A) = 0) :
    IsStablyUniform A := by
  constructor
  intro P T s hT
  let hden := P.hasDenominatorPower_of_isOpen_span T s (Localization.Away s) hT
  have := IsPerfectoidTateRing.ratLoc hp P T s hden
  exact IsPerfectoidTateRing.isUniform p (R := Huber.ratLoc P T s hden)

end TauCeti.Perfectoid

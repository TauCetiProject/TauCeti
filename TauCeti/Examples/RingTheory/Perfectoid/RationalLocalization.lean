/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Perfectoid.RationalLocalization
import TauCeti.RingTheory.Huber.LocalizationTopology.Pair
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational.StableUniform

/-!
# Checks for perfectoid rational localizations

On the disjoint union of two copies of a characteristic-`p` affinoid, localizing at the idempotent
`(1, 0)` gives a nonzero chart, as witnessed by the projection to the first copy. Localizing at
zero instead gives a zero ring. We also check that the usual plus ring inherits perfectness and
that stable uniformity gives the sheafiness of the original ring.
-/

namespace TauCeti.Examples

open TauCeti.Huber TauCeti.Perfectoid

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A] [T2Space A] [CompleteSpace A] [IsTateRing A] [IsPerfectoidTateRing p A]

example [Nontrivial A] (hp : (p : A) = 0) (P : PairOfDefinition (A × A))
    (hden : P.HasDenominatorPower ({1} : Finset (A × A)) (1, 0) (Localization.Away (1, 0))) :
    Nontrivial (ratLoc P {1} (1, 0) hden) ∧ PerfectRing (ratLoc P {1} (1, 0) hden) p := by
  let f : A × A →+* A := RingHom.fst A A
  have hu : IsUnit (f (1, 0)) := isUnit_one
  obtain ⟨g, -⟩ := P.existsUnique_continuous_ringHom_completion_locTopology {1} (1, 0)
    (Localization.Away (1, 0)) hden (φ := f) continuous_fst.continuousAt hu (by
      intro t ht
      rw [Finset.mem_singleton] at ht
      subst t
      simp [f])
  have hp' : (p : A × A) = 0 := Prod.ext hp hp
  exact ⟨g.domain_nontrivial, IsPerfectoidTateRing.perfectRing_ratLoc hp' P _ _ hden⟩

example (hp : (p : A) = 0) (P : PairOfDefinition A)
    (hden : P.HasDenominatorPower ({1} : Finset A) 0 (Localization.Away (0 : A))) :
    Subsingleton (ratLoc P {1} 0 hden) ∧ IsPerfectoidTateRing p (ratLoc P {1} 0 hden) := by
  have hu := isUnit_algebraMap_ratLoc P {1} 0 hden
  rw [map_zero, isUnit_zero_iff] at hu
  exact ⟨subsingleton_iff_zero_eq_one.mp hu, IsPerfectoidTateRing.ratLoc hp P _ _ hden⟩

example (hp : (p : A) = 0) (P : PairOfDefinition A) (U : Pair A)
    (hP : P.ringOfDefinition ≤ U.plus) (T : Finset A) (s : A)
    (hden : P.HasDenominatorPower T s (Localization.Away s)) :
    PerfectRing (P.rationalLocalizationPair U hP T s (Localization.Away s) hden).plus p := by
  have := IsPerfectoidTateRing.perfectRing_ratLoc hp P T s hden
  exact Pair.instPerfectRingPlus _ p

example (hp : (p : A) = 0) : IsSheafyRing A := by
  have := IsPerfectoidTateRing.isStablyUniform_of_natCast_eq_zero hp
  exact isSheafyRing_of_isStablyUniform

end TauCeti.Examples

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Character

/-!
# Examples of smooth characters

The trivial character is smooth and twisting by it changes nothing. Every character of a discrete
group is smooth, and so is its rank-one representation. Twisting the trivial representation of a
topological group by a smooth character gives a smooth representation. On a subgroup inside the
kernel of a character, twisting by it does not change the invariants.
-/

public section

open Representation

namespace TauCeti

variable {A G : Type*} [CommSemiring A] [Group G] [TopologicalSpace G]

example : IsSmoothCharacter (1 : G →* Aˣ) := isSmoothCharacter_one

example {V : Type*} [AddCommMonoid V] [Module A V] (ρ : Representation A G V) :
    charTwist (1 : G →* Aˣ) ρ = ρ :=
  charTwist_one ρ

example [DiscreteTopology G] (χ : G →* Aˣ) : IsSmoothCharacter χ :=
  isSmoothCharacter_of_discreteTopology χ

example [DiscreteTopology G] (χ : G →* Aˣ) : IsSmooth (ofLinearCharacter χ) := inferInstance

example [SeparatelyContinuousMul G] {χ : G →* Aˣ} (hχ : IsSmoothCharacter χ) :
    IsSmooth (charTwist χ (trivial A G A)) :=
  hχ.isSmooth_charTwist _

example {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V] (χ : G →* kˣ)
    (ρ : Representation k G V) {U : Subgroup G} (hU : U ≤ χ.ker) :
    invariants ((charTwist χ ρ).comp U.subtype) = invariants (ρ.comp U.subtype) := by
  rw [charTwist_comp_subtype_of_le_ker χ ρ hU]

end TauCeti

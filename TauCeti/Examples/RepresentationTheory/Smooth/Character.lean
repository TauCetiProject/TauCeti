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
topological group by a smooth character gives a smooth representation.
-/

public section

open Representation

namespace TauCeti

variable {A G : Type*} [CommRing A] [Group G] [TopologicalSpace G]

example : IsSmoothCharacter (1 : G →* Aˣ) := isSmoothCharacter_one

example {V : Type*} [AddCommGroup V] [Module A V] (ρ : Representation A G V) :
    charTwist (1 : G →* Aˣ) ρ = ρ :=
  charTwist_one ρ

example [DiscreteTopology G] (χ : G →* Aˣ) : IsSmoothCharacter χ :=
  isSmoothCharacter_of_discreteTopology χ

example [DiscreteTopology G] (χ : G →* Aˣ) : IsSmooth (ofLinearCharacter χ) := inferInstance

example [SeparatelyContinuousMul G] {χ : G →* Aˣ} (hχ : IsSmoothCharacter χ) :
    IsSmooth (charTwist χ (trivial A G A)) :=
  hχ.isSmooth_charTwist _

end TauCeti

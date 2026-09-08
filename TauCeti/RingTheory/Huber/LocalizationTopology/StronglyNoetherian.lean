/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Restriction
public import TauCeti.RingTheory.Huber.StronglyNoetherian

import TauCeti.RingTheory.Huber.LocalizationTopology.Presentation

/-!
# Strong noetherianness of a completed localisation is carrier-independent

A presentation `(T, s)` of a rational localisation is carried by *some* localisation `S` of `A`
at `s`, and the choice is immaterial: two carriers of the same presentation have isomorphic
completions. Strong noetherianness therefore depends on the presentation alone.

Nothing here is specific to Laurent presentations or to enlarging the numerator set; those live
in `TauCeti.RingTheory.Huber.LocalizationTopology.Laurent.StronglyNoetherian`, which consumes
this.

## Main results

* `TauCeti.Huber.PairOfDefinition.isStronglyNoetherian_completion_self`.
-/

public section

namespace TauCeti.Huber

open TauCeti.Localization

namespace PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **Strong noetherianness does not depend on which localisation carries a presentation.** Two
presentations with the same numerator set and denominator, carried by different localisations of
`A` at `s`, have isomorphic completions, so one is strongly noetherian exactly when the other is.
Nothing else is assumed: no nilpotence, no noetherianity.

This is the invariance a caller needs in order to change carriers. -/
theorem isStronglyNoetherian_completion_self (P : PairOfDefinition A) (T : Finset A)
    (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s S']
    (hden' : HasDenominatorPower P T s S')
    (hSN :
      letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsStronglyNoetherian (UniformSpace.Completion S)) :
    letI := locUniformSpace P T s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T s S' hden'
    letI := isTopologicalRing_locUniformSpace P T s S' hden'
    letI := isHuberRing_locUniformSpace P T s S' hden'
    IsStronglyNoetherian (UniformSpace.Completion S') := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T s S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T s S' hden'
  have _ := isTopologicalRing_locUniformSpace P T s S' hden'
  have _ := isHuberRing_locUniformSpace P T s S' hden'
  exact (isStronglyNoetherian_congr
    (presentationRingEquiv P T s S hden T s S' hden'
      (restrictionRingHomOfSubset P T s S hden T S' hden' fun _ hu ↦ hu)
      (restrictionRingHomOfSubset P T s S' hden' T S hden fun _ hu ↦ hu)
      (continuous_restrictionRingHomOfSubset P T s S hden T S' hden' fun _ hu ↦ hu)
      (continuous_restrictionRingHomOfSubset P T s S' hden' T S hden fun _ hu ↦ hu)
      (restrictionRingHomOfSubset_comp_toCompletionLoc P T s S hden T S' hden' fun _ hu ↦ hu)
      (restrictionRingHomOfSubset_comp_toCompletionLoc P T s S' hden' T S hden fun _ hu ↦ hu))
    (continuous_presentationRingEquiv P T s S hden T s S' hden' _ _ _ _ _ _)
    (continuous_presentationRingEquiv_symm P T s S hden T s S' hden' _ _ _ _ _ _)).mp hSN

end PairOfDefinition

end TauCeti.Huber

end

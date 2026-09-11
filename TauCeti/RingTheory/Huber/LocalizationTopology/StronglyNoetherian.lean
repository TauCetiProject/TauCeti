/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Restriction
public import TauCeti.RingTheory.Huber.StronglyNoetherian
public import TauCeti.RingTheory.Huber.LocalizationTopology.Evaluation

import TauCeti.RingTheory.Huber.LocalizationTopology.Presentation

/-!
# Strong noetherianness of a completed rational localisation

Two results, one about the carrier and one about the ring.

**Carrier-independence.** A presentation `(T, s)` of a rational localisation is carried by *some*
localisation `S` of `A` at `s`, and the choice is immaterial: two carriers of the same
presentation have isomorphic completions. Strong noetherianness therefore depends on the
presentation alone.

**Strong noetherianity itself.** When `A` is a strongly noetherian Tate ring and the numerators
generate the unit ideal together with `s`, the completion `A⟨T/s⟩` is again strongly noetherian.
The route is the presentation: `A⟨T/s⟩` is strictly topologically of finite type over `A`
(`TauCeti.Huber.PairOfDefinition.isStrictlyTopologicallyFiniteType_toCompletionLoc`), and strong
noetherianity travels along such a presentation. This is what a caller needs in order to iterate
the construction, and hence what the sheaf condition for a strongly noetherian Huber pair rests
on.

Nothing here is specific to Laurent presentations or to enlarging the numerator set; those live
in `TauCeti.RingTheory.Huber.LocalizationTopology.Laurent.StronglyNoetherian`, which consumes
this.

## Main results

* `TauCeti.Huber.PairOfDefinition.isStronglyNoetherian_completion_self`: the carrier does not
  matter.
* `TauCeti.Huber.PairOfDefinition.isStronglyNoetherian_completion`: a rational localisation of a
  strongly noetherian Tate ring is strongly noetherian.
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

/-- **A rational localisation of a strongly noetherian Tate ring is strongly noetherian**,
whenever the numerators together with the denominator `s` generate the unit ideal.

Strong noetherianity of `A` alone suffices: nothing is assumed of the localisation, and the
hypothesis on the numerators is the rational-subset condition, which holds by definition wherever
`A⟨T/s⟩` is the ring of a rational subset.

This is the form Wedhorn's §8.2 needs in order to iterate: it makes strong noetherianity stable
under passing to a rational localisation, so the argument may be repeated inside `A⟨T/s⟩`. -/
theorem isStronglyNoetherian_completion [IsTateRing A]
    [IsStronglyNoetherian A] [(nhds (0 : A)).IsCountablyGenerated]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (hspan : Ideal.span (insert s (T : Set A)) = ⊤) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI : UniformContinuousConstSMul A S :=
      uniformContinuousConstSMul_of_continuousConstSMul A S
    letI : NonarchimedeanRing S := by
      have h := nonarchimedeanRing_locTopology P T s S hden
      rwa [← locUniformSpace_toTopologicalSpace P T s S hden] at h
    IsStronglyNoetherian (UniformSpace.Completion S) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  let _ : UniformContinuousConstSMul A S :=
    uniformContinuousConstSMul_of_continuousConstSMul A S
  have _ : NonarchimedeanRing S := by
    have h := nonarchimedeanRing_locTopology P T s S hden
    rwa [← locUniformSpace_toTopologicalSpace P T s S hden] at h
  exact (isStrictlyTopologicallyFiniteType_toCompletionLoc P T s S hden
    hspan).isStronglyNoetherian

end PairOfDefinition

end TauCeti.Huber

end

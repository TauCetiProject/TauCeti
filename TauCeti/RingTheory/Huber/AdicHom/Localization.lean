/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.AdicHom.Basic
public import TauCeti.RingTheory.Huber.LocalizationTopology.Completion

/-!
# Adicness of the structure map of a completed localisation

The structure map `A → A⟨T/s⟩` of a completed localisation of a Huber ring is adic: it is
continuous, and the ideal it generates from an open ideal of `A` is open. This is what makes a
completed rational localisation an adic algebra over its base, as completed tensor products along
adic homomorphisms require.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 6.23 and Proposition 6.25.
-/

public section

namespace TauCeti.Huber.PairOfDefinition

/-- The structure map `A → A⟨T/s⟩` of a completed localisation is adic. -/
theorem isAdicHom_toCompletionLoc {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (P : PairOfDefinition A) (T : Set A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    IsAdicHom (toCompletionLoc P T s S hden) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  have _ : IsHuberRing A := ⟨⟨P⟩⟩
  exact IsAdicHom.of_continuous_isOpen_map (continuous_toCompletionLoc P T s S hden)
    fun _ hJ ↦ isOpen_map_toCompletionLoc P T s S hden hJ

end TauCeti.Huber.PairOfDefinition

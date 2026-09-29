/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.SheafCriterion
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Basic

import TauCeti.RingTheory.Huber.RingOfDefinition

/-!
# Sheafhood across compatible presentations

`IsSheafyForEveryPresentation Aplus` requires `Aplus` to be a ring of integral elements and the
presentation-indexed limit presheaf `presentationLimitPresheaf P Aplus` to be a sheaf of complete
separated topological rings for every pair of definition `P` contained in `Aplus`. Such a pair
exists because `Aplus` is open. This universal condition is a priori stronger than sheafhood for
one chosen compatible `P`.

On rational opens, `presentationLimitRationalIso` identifies the presheaf's values with the
completed rational localizations, and `presentationLimitRationalIso_inv_comp_map_comp_hom`
identifies its restrictions with the canonical comparison maps. These rational-open comparisons
do not themselves identify the presentation-indexed presheaf with Wedhorn's `𝒪_X` on all opens
or establish independence of the compatible pair of definition. The predicate concerns only the
presentation-indexed presheaves; it makes no claim about a canonical pair-level structure presheaf.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §8.1 and Theorem 8.28.
-/

open CategoryTheory _root_.TopologicalSpace TauCeti.TopologicalSpace.Opens
  TauCeti.ValuationSpectrum

namespace TauCeti.Huber

public section

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A]

/-- The plus ring `Aplus` is a ring of integral elements, and its presentation-indexed limit
presheaf is a sheaf for every compatible pair of definition. This condition concerns the
presentation-indexed presheaves, without identifying them with a canonical pair-level structure
presheaf. -/
structure IsSheafyForEveryPresentation (Aplus : Subring A) : Prop where
  /-- `Aplus` is a ring of integral elements of `A`. -/
  isRingOfIntegralElements : IsRingOfIntegralElements Aplus
  /-- The presentation-indexed limit presheaf is a sheaf for each compatible pair of definition. -/
  isSheaf (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ Aplus) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus)

/-- The universal condition supplies a compatible pair of definition whose presentation-indexed
limit presheaf is a sheaf. -/
theorem IsSheafyForEveryPresentation.exists_compatible_isSheaf {Aplus : Subring A}
    (h : IsSheafyForEveryPresentation Aplus) :
    ∃ P : PairOfDefinition A, P.ringOfDefinition ≤ Aplus ∧
      Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
        (presentationLimitPresheaf P Aplus) := by
  obtain ⟨P, hP⟩ := exists_pairOfDefinition_ringOfDefinition_le h.isRingOfIntegralElements.isOpen
  exact ⟨P, hP, h.isSheaf P hP⟩

end

end TauCeti.Huber

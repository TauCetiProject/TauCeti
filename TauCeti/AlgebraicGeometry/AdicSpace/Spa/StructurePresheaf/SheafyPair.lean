/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.SheafCriterion
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Basic

/-!
# Sheafiness of a Huber pair

`IsSheafyPair Aplus` requires `Aplus` to be a ring of integral elements and the
presentation-indexed limit presheaf `presentationLimitPresheaf P Aplus` to be a sheaf of complete
separated topological rings for every pair of definition `P`. Independence of the choice of `P`
is not yet available, so this condition is a priori stronger than sheafhood for one chosen `P`.

The presentation-indexed limit presheaf has not yet been identified as a presheaf with Wedhorn's
`𝒪_X`. Relating this predicate to Wedhorn's sheafiness requires that identification.

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

/-- A Huber pair `(A, A⁺)` whose plus ring is `Aplus` and whose presentation-indexed limit
presheaf is a sheaf for every pair of definition. This presheaf has not yet been identified with
Wedhorn's `𝒪_X`. -/
structure IsSheafyPair (Aplus : Subring A) : Prop where
  /-- `Aplus` is a ring of integral elements of `A`. -/
  isRingOfIntegralElements : IsRingOfIntegralElements Aplus
  /-- The presentation-indexed limit presheaf is a sheaf for each pair of definition. -/
  isSheaf (P : PairOfDefinition A) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus)

end

end TauCeti.Huber

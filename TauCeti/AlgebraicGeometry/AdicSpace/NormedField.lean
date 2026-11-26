/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Affinoid.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.StronglyNoetherian
public import TauCeti.RingTheory.Huber.Normed
public import TauCeti.RingTheory.Huber.Restricted.Noetherian

/-!
# The affinoid adic space of a complete ultrametric field

The closed unit ball of a complete nontrivially normed ultrametric field `K` is the
power-bounded subring. Strong noetherianness makes this pair sheafy, so
`AdicSpace.ofNormedField K` presents the affinoid adic space `Spa(K, K°)` without an explicit
pair of definition. Its morphisms can be computed using `AdicSpace.ofPairHomEquiv`.
-/

public section

namespace TauCeti.AdicSpace

open Huber

/-- The affinoid adic space `Spa(K, K°)` of a complete nontrivially normed ultrametric field, with
the closed unit ball as its ring of integral elements. -/
noncomputable abbrev ofNormedField (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] : AdicSpace :=
  ofPair (Pair.powerBounded K)
    (isSheafyForEveryPresentation_of_isStronglyNoetherian
      (Pair.powerBounded K).isRingOfIntegralElements)

end TauCeti.AdicSpace

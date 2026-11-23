/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.CWComplex
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Functoriality.Basic
public import TauCeti.Topology.CWComplex.Classical.CWType

/-!
# CW type of the classifying-space functor

Milnor's classifying space `TauCeti.classifyingSpace G` carries a CW structure
(`TauCeti.instCWComplexClassifyingSpace` in `TauCeti.AlgebraicTopology.ClassifyingSpace.CWComplex`)
and hence has CW type. The strict functor
`TauCeti.classifyingSpaceFunctor : GrpCat ⥤ BasedTopologicalSpace` (defined in
`TauCeti.AlgebraicTopology.ClassifyingSpace.Functoriality.Basic`) sends `G` to `classifyingSpace G`
equipped with its base point. This module bridges those two files by providing the `CWType`
instance on `(classifyingSpaceFunctor.obj G).carrier`.

## Main definitions

* `TauCeti.instCWTypeClassifyingSpaceFunctorObj`: the underlying space of
  `classifyingSpaceFunctor.obj G` has CW type.
-/

public section

noncomputable section

namespace TauCeti

universe u

/-- The underlying space of `classifyingSpaceFunctor.obj G` has CW type. -/
instance instCWTypeClassifyingSpaceFunctorObj (G : GrpCat.{u}) :
    CWType (classifyingSpaceFunctor.obj G).carrier :=
  inferInstanceAs (CWType (classifyingSpace G))

end TauCeti

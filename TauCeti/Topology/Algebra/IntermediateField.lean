/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.Topology.Algebra.Algebra

/-!
# Topological instances on intermediate fields

Every intermediate field `E : IntermediateField K L` carries the subspace topology inherited from
`L`. This file provides the `IsTopologicalSemiring` and `IsTopologicalRing` instances for `E`
derived from its underlying subalgebra.
-/

public section

namespace IntermediateField

/-- An intermediate field of a topological semiring field is a topological semiring for its
subspace topology. -/
instance instIsTopologicalSemiring {K L : Type*} [Field K] [Field L] [Algebra K L]
    [TopologicalSpace L] [IsTopologicalSemiring L] (E : IntermediateField K L) :
    IsTopologicalSemiring E :=
  inferInstanceAs (IsTopologicalSemiring E.toSubalgebra)

/-- An intermediate field of a topological ring field is a topological ring for its subspace
topology. -/
instance instIsTopologicalRing {K L : Type*} [Field K] [Field L] [Algebra K L]
    [TopologicalSpace L] [IsTopologicalRing L] (E : IntermediateField K L) :
    IsTopologicalRing E :=
  IsTopologicalSemiring.toIsTopologicalRing inferInstance

end IntermediateField

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Topological instances on intermediate fields

Every intermediate field `E : IntermediateField K L` carries the subspace topology inherited from
`L`. This file provides the `IsTopologicalRing` instance for `E` derived from its underlying
subring `E.toSubring` (`Subring.instIsTopologicalRing`), from which `IsTopologicalSemiring E`
follows automatically.
-/

public section

namespace IntermediateField

/-- An intermediate field of a topological ring field is a topological ring for its subspace
topology. -/
instance instIsTopologicalRing {K L : Type*} [Field K] [Field L] [Algebra K L]
    [TopologicalSpace L] [IsTopologicalRing L] (E : IntermediateField K L) :
    IsTopologicalRing E :=
  inferInstanceAs (IsTopologicalRing E.toSubring)

end IntermediateField

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.Compactness.Compact

/-!
# Compactness of clopen subtypes

A clopen subset of a compact space is compact. This instance allows continuous functions
on clopen subtypes to carry their supremum norm without repeating compactness arguments.
No separation hypothesis on the ambient space is needed.
-/

public section

namespace TauCeti

open TopologicalSpace

/-- A clopen subset of a compact space is compact, without a separation assumption. -/
instance compactSpace_clopens {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {s : Clopens X} : CompactSpace s :=
  isCompact_iff_compactSpace.mp s.isClosed.isCompact

end TauCeti

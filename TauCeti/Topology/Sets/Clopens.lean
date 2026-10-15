/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Sets.Closeds

/-!
# Compact clopen subsets

This file supplies the compact-space instance on a clopen subset of a compact space.
-/

public section

open TopologicalSpace

namespace TopologicalSpace.Clopens

/-- A clopen subset of a compact space is compact. -/
instance instCompactSpace [TopologicalSpace X] [CompactSpace X] (s : Clopens X) : CompactSpace s :=
  isCompact_iff_compactSpace.mp s.isClosed.isCompact

end TopologicalSpace.Clopens

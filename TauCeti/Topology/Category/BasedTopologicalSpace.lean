/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Basic

/-!
# Based topological spaces

A `TauCeti.BasedTopologicalSpace` is a topological space together with a basepoint. It is the
carrier for constructions that need a distinguished point of the space itself, such as loop spaces
and based mapping spaces.

## Main declarations

* `TauCeti.BasedTopologicalSpace`: a topological space with a basepoint.
-/

public section

universe u

namespace TauCeti

/-- A topological space with a basepoint. -/
structure BasedTopologicalSpace where
  /-- The underlying type. -/
  carrier : Type u
  [topologicalSpace : TopologicalSpace carrier]
  /-- The basepoint. -/
  basepoint : carrier

attribute [instance] BasedTopologicalSpace.topologicalSpace

end TauCeti

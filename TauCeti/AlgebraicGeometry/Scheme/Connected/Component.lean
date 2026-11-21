/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Connected.LocallyConnected

/-!
# Connected components as open subschemes

On a locally connected scheme, a connected component is open and closed. Equip it with the
open-subscheme structure, so that its inclusion is both an open and a closed immersion.
This keeps the scheme structure on each component, including nilpotents, rather than giving
the closed set its reduced induced structure.

## References

* The Stacks Project, Topology, Section 5.7, connected components.
-/

public section

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) [LocallyConnectedSpace X]

/-- The connected component of a point, with its open-subscheme structure. -/
def connectedComponentOpen (x : X) : X.Opens :=
  ⟨connectedComponent x, isOpen_connectedComponent⟩

/-- The points of the component open are precisely the topological connected component. -/
@[simp]
theorem coe_connectedComponentOpen (x : X) :
    (connectedComponentOpen X x : Set X) = connectedComponent x :=
  (rfl)

/-- A component open is connected and nonempty. -/
instance connectedSpace_connectedComponentOpen (x : X) :
    ConnectedSpace (connectedComponentOpen X x).toScheme :=
  isConnected_iff_connectedSpace.mp isConnected_connectedComponent

/-- The inclusion of a component open is also a closed immersion. -/
instance isClosedImmersion_connectedComponentOpen_ι (x : X) :
    IsClosedImmersion (connectedComponentOpen X x).ι :=
  IsClosedImmersion.of_isPreimmersion _ (by
    simpa only [Opens.range_ι, coe_connectedComponentOpen] using
      (isClosed_connectedComponent (x := x)))

end AlgebraicGeometry.Scheme

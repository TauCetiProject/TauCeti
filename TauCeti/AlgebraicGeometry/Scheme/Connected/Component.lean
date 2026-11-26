/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic
public import Mathlib.Topology.Connected.LocallyConnected
public import TauCeti.Topology.ConnectedComponents

/-!
# Connected components as open subschemes

On a locally connected scheme, a connected component is open and closed. Equip it with the
open-subscheme structure, so that its inclusion is both an open and a closed immersion.
This keeps the scheme structure on each component, including nilpotents, rather than giving
the closed set its reduced induced structure.

Components indexed by the quotient `ConnectedComponents X` carry the same open-subscheme
structure and connectedness and closed-immersion instances.

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
  (connectedComponentOpen X x).isClosedImmersion_ι_iff.mpr
    (by simpa only [coe_connectedComponentOpen] using isClosed_connectedComponent (x := x))

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

universe u

variable {X : Scheme.{u}} [LocallyConnectedSpace X]

/-- The quotient-indexed component of a point agrees with its connected-component open. -/
@[simp]
theorem opens_mk_eq_connectedComponentOpen (x : X) :
    (ConnectedComponents.mk x).opens = X.connectedComponentOpen x := by
  apply TopologicalSpace.Opens.ext
  exact ConnectedComponents.coe_opens_mk x

/-- A quotient-indexed connected component, with its open-subscheme structure, is connected. -/
instance connectedSpace_connectedComponentsOpens (C : ConnectedComponents X) :
    ConnectedSpace (Scheme.Opens.toScheme C.opens) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  rw [opens_mk_eq_connectedComponentOpen]
  infer_instance

/-- The inclusion of a quotient-indexed connected component is a closed immersion. -/
instance isClosedImmersion_connectedComponentsOpens_ι (C : ConnectedComponents X) :
    IsClosedImmersion (Scheme.Opens.ι C.opens) :=
  (Opens.isClosedImmersion_ι_iff C.opens).mpr C.isClopen_opens.isClosed

end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Spaces of CW type

A space has CW type if it is homotopy equivalent to a subspace of a Hausdorff space
carrying a classical CW structure. No finiteness condition is imposed on the cells.
The model lives in the same universe as the space.

This property permits cellular arguments about homotopy invariants to apply to spaces
without a chosen CW structure. In particular, Whitehead's theorem applies to weak
homotopy equivalences between spaces of CW type. The property is preserved by homotopy
equivalences and homeomorphisms.

## References

* A. Hatcher, *Algebraic Topology*, Chapter 0 and Section 4.1.
-/

public section

open Topology Set

universe u

namespace TauCeti

/-- A space has **CW type** if it is homotopy equivalent to a classical CW complex
in a Hausdorff ambient space in the same universe. -/
class CWType (X : Type u) [TopologicalSpace X] : Prop where
  /-- A CW complex homotopy equivalent to the space. -/
  exists_homotopyEquiv : ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : T2Space Y)
    (C : Set Y) (_ : CWComplex C), Nonempty (ContinuousMap.HomotopyEquiv X C)

/-- A classical CW complex has CW type. -/
instance CWType.of_cwComplex {Y : Type u} [TopologicalSpace Y] [T2Space Y]
    (C : Set Y) [CWComplex C] : CWType C :=
  ⟨⟨Y, _, ‹_›, C, ‹_›, ⟨.refl C⟩⟩⟩

end TauCeti

namespace ContinuousMap.HomotopyEquiv

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- A space homotopy equivalent to a space of CW type has CW type. -/
theorem cwType [h : TauCeti.CWType Y] (e : HomotopyEquiv X Y) : TauCeti.CWType X := by
  obtain ⟨Z, _, _, C, _, ⟨e'⟩⟩ := h.exists_homotopyEquiv
  exact ⟨⟨Z, _, ‹_›, C, ‹_›, ⟨e.trans e'⟩⟩⟩

/-- CW type is invariant under homotopy equivalence. -/
theorem cwType_iff (e : HomotopyEquiv X Y) : TauCeti.CWType X ↔ TauCeti.CWType Y :=
  ⟨fun _ ↦ e.symm.cwType, fun _ ↦ e.cwType⟩

end ContinuousMap.HomotopyEquiv

/-- A space homeomorphic to a space of CW type has CW type. -/
theorem Homeomorph.cwType {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [TauCeti.CWType Y] (e : X ≃ₜ Y) : TauCeti.CWType X :=
  e.toHomotopyEquiv.cwType

/-- Every discrete space has CW type, with its points as zero-cells. -/
instance TauCeti.CWType.of_discreteTopology (X : Type u) [TopologicalSpace X]
    [DiscreteTopology X] : TauCeti.CWType X :=
  (Homeomorph.Set.univ X).symm.cwType

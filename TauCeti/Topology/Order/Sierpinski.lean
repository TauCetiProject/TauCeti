/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Order

/-!
# Closed points and irreducibility of the Sierpiński space

Mathlib equips `Prop` with the Sierpiński topology (`sierpinskiSpace`), in which `{True}` is open
(`isOpen_singleton_true`). This file records the complementary closed-point and irreducibility
properties of `Prop`: `{False}` is closed, `{True}` is dense (hence not closed), and `Prop` is an
irreducible space (hence connected via `IrreducibleSpace.connectedSpace`).

## Main results

* `TauCeti.isClosed_singleton_false`: `{False}` is closed in `Prop`.
* `TauCeti.not_isClosed_singleton_true`: `{True}` is not closed in `Prop`.
* `TauCeti.irreducibleSpace_prop`: `Prop` with the Sierpiński topology is an irreducible space.
-/

public section

open Set Topology

namespace TauCeti

/-- In the Sierpiński space `Prop`, the singleton `{False}` is closed. -/
@[simp]
theorem isClosed_singleton_false : IsClosed ({False} : Set Prop) := by
  simpa using isOpen_singleton_true.isClosed_compl

/-- In the Sierpiński space `Prop`, the open singleton `{True}` is not closed. -/
@[simp]
theorem not_isClosed_singleton_true : ¬ IsClosed ({True} : Set Prop) := fun h ↦
  false_ne_true <| mem_singleton_iff.1 <| h.closure_eq ▸
    mem_closure_iff_nhds.2 fun _ hU ↦ ⟨True, by simp_all⟩

/-- The Sierpiński space `Prop` is irreducible (and hence connected via
`IrreducibleSpace.connectedSpace`), since `{True}` is dense. -/
instance irreducibleSpace_prop : IrreducibleSpace Prop where
  toNonempty := inferInstance
  isPreirreducible_univ := by
    have hd : Dense ({True} : Set Prop) := fun p ↦ by
      by_cases hp : p
      · exact subset_closure (by simp [hp])
      · exact mem_closure_iff_nhds.2 fun _ hU ↦ ⟨True, by simp_all⟩
    simpa [hd.closure_eq] using (isPreirreducible_singleton (x := True)).closure

end TauCeti

end

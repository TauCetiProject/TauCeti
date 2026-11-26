/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Order.UpperLowerSetTopology

/-!
# Open sets, closed points, separation, and irreducibility of the Sierpiński space

Mathlib equips `Prop` with the Sierpiński topology (`sierpinskiSpace`), in which `{True}` is open
(`isOpen_singleton_true`) and `𝓝 False = ⊤` (`nhds_false`). This file classifies all open subsets
of `Prop` and records its closed-point, non-Hausdorffness, and irreducibility properties:

* `TauCeti.isOpen_sierpinski_iff`: the open subsets of `Prop` are `∅`, `{True}`, and `Set.univ`.
* `TauCeti.isClosed_singleton_false`: `{False}` is closed in `Prop`.
* `TauCeti.not_isClosed_singleton_true`: `{True}` is not closed in `Prop`.
* `TauCeti.not_t2Space_sierpinski`: `Prop` with the Sierpiński topology is not Hausdorff.
* `TauCeti.irreducibleSpace_prop`: `Prop` with the Sierpiński topology is an irreducible space
  (hence connected via `IrreducibleSpace.connectedSpace`).
-/

public section

open Set Topology

namespace TauCeti

/-- **Exact open sets of the Sierpiński space `Prop`**: a subset of `Prop` is open in
`sierpinskiSpace` if and only if it is `∅`, `{True}`, or `Set.univ`. -/
theorem isOpen_sierpinski_iff {s : Set Prop} :
    IsOpen s ↔ s = ∅ ∨ s = {True} ∨ s = univ := by
  refine ⟨fun hs ↦ ?_, fun h ↦ ?_⟩
  · by_cases hF : False ∈ s
    · exact Or.inr (Or.inr (Filter.mem_top.1 (nhds_false ▸ hs.mem_nhds hF)))
    · by_cases hT : True ∈ s
      · refine Or.inr (Or.inl (Set.ext fun p ↦ ⟨fun hp ↦ ?_, fun hp ↦ hp.symm ▸ hT⟩))
        by_cases hp' : p
        · exact eq_true hp'
        · exact (hF (eq_false hp' ▸ hp)).elim
      · refine Or.inl (eq_empty_iff_forall_notMem.2 fun p hp ↦ ?_)
        by_cases hp' : p
        · exact hT (eq_true hp' ▸ hp)
        · exact hF (eq_false hp' ▸ hp)
  · rcases h with rfl | rfl | rfl
    exacts [isOpen_empty, isOpen_singleton_true, isOpen_univ]

/-- In the Sierpiński space `Prop`, the singleton `{False}` is closed. -/
@[simp]
theorem isClosed_singleton_false : IsClosed ({False} : Set Prop) := by
  simpa using isOpen_singleton_true.isClosed_compl

/-- In the Sierpiński space `Prop`, the open singleton `{True}` is not closed. -/
@[simp]
theorem not_isClosed_singleton_true : ¬ IsClosed ({True} : Set Prop) := fun h ↦
  false_ne_true <| mem_singleton_iff.1 <| h.closure_eq ▸
    (Topology.IsUpperSet.closure_singleton (a := True)).symm ▸ (bot_le : False ≤ True)

/-- The Sierpiński space `Prop` is not Hausdorff (`¬ T2Space Prop`), since `{True}` is not
closed. -/
theorem not_t2Space_sierpinski : ¬ T2Space Prop := fun h ↦
  have := h.t1Space
  not_isClosed_singleton_true isClosed_singleton

/-- The Sierpiński space `Prop` is irreducible (and hence connected via
`IrreducibleSpace.connectedSpace`), since `{True}` is dense. -/
instance irreducibleSpace_prop : IrreducibleSpace Prop where
  toNonempty := inferInstance
  isPreirreducible_univ := by simpa using (isPreirreducible_singleton (x := True)).closure

end TauCeti

end

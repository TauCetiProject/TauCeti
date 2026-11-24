/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Isomorphism.Basic
public import TauCeti.Combinatorics.Network.SetFlow

/-!
# Maximum flows under network isomorphisms

A bounded-network isomorphism identifies the feasible assignments of two networks and preserves
their values. This file deduces that it preserves and reflects minimum bounded `s`–`t`
assignments and maximum flows between terminal sets, the last through a transport equivalence of
terminal-set flows. Maximum bounded `s`–`t` assignments and maximum ordinary flows are handled in
`TauCeti.Combinatorics.Network.Isomorphism.Basic` by
`TauCeti.Network.Iso.isMaximum_mapBoundedFlow_iff` and `TauCeti.Network.Iso.isMaximum_mapFlow_iff`.

Minimum cuts are covered by the general relabelling results for terminal cuts:
`TauCeti.TerminalCut.isMinimum_map_iff`, `TauCeti.TerminalCut.minimumValue_map` and
`TauCeti.TerminalCut.minimizersOrderIso` apply to cut bounds and cut capacities through
`TauCeti.Network.Iso.cutBound_assignmentEquiv` and `TauCeti.Network.Iso.arrowSum_assignmentEquiv`.

## Main definitions

* `TauCeti.Network.Iso.setFlowEquiv`: transport of `A`–`B` flows, with transported capacities
  and terminal sets.

## Main results

* `TauCeti.Network.Iso.isMinimum_mapBoundedFlow_iff`: minimum bounded `s`–`t` assignments
  correspond.
* `TauCeti.Network.Iso.isMaximum_setFlowEquiv_iff`: maximum `A`–`B` flows correspond.
-/

public section

namespace TauCeti

universe u u' w

namespace Network

namespace Iso

variable {K : Type w} {V : Type u} {W : Type u'}
variable [AddCommGroup K] [Preorder K]
variable {N : Network K V} {N' : Network K W}
variable [Fintype V] [Fintype W]
variable [∀ x y, Fintype (N.Hom x y)] [∀ x y, Fintype (N'.Hom x y)]

/-- Transport preserves and reflects minimality of a bounded `s`–`t` assignment. -/
@[simp]
theorem isMinimum_mapBoundedFlow_iff (e : N ≃ₙ N') {lo hi : N.Assignment K} {s t : V}
    (f : TauCeti.BoundedFlow lo hi s t) :
    (e.mapBoundedFlow f).IsMinimum ↔ f.IsMinimum := by
  rw [BoundedFlow.isMinimum_iff, BoundedFlow.isMinimum_iff,
    ← (e.boundedFlowEquiv lo hi s t).forall_congr_right]
  simp

/-- Transport identifies the `A`–`B` flows for `cap` with the flows for the transported
capacities between the transported terminal sets. -/
def setFlowEquiv (e : N ≃ₙ N') (cap : N.Assignment K) (A B : Finset V) :
    SetFlow cap A B ≃
      SetFlow (e.assignmentEquiv K cap) (A.map e.vertexEquiv.toEmbedding)
        (B.map e.vertexEquiv.toEmbedding) where
  toFun f :=
    { toFun := e.assignmentEquiv K f.toFun
      mem_Icc := by
        rw [← assignmentEquiv_zero e, e.assignmentEquiv_mem_Icc_map_iff]
        exact f.mem_Icc
      conserve y hyA hyB := by
        obtain ⟨x, rfl⟩ := e.vertexEquiv.surjective y
        rw [Finset.mem_map_equiv, Equiv.symm_apply_apply] at hyA hyB
        rw [e.excessAt_assignmentEquiv]
        exact f.conserve x hyA hyB
      excessAt_nonpos y hy := by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
        rw [Equiv.coe_toEmbedding, e.excessAt_assignmentEquiv]
        exact f.excessAt_nonpos x hx
      excessAt_nonneg y hy := by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
        rw [Equiv.coe_toEmbedding, e.excessAt_assignmentEquiv]
        exact f.excessAt_nonneg x hx }
  invFun g :=
    { toFun := (e.assignmentEquiv K).symm g.toFun
      mem_Icc := by
        rw [← e.assignmentEquiv_mem_Icc_map_iff, Equiv.apply_symm_apply, assignmentEquiv_zero]
        exact g.mem_Icc
      conserve x hxA hxB := by
        rw [← e.excessAt_assignmentEquiv, Equiv.apply_symm_apply]
        exact g.conserve _ (by simpa [Finset.mem_map_equiv] using hxA)
          (by simpa [Finset.mem_map_equiv] using hxB)
      excessAt_nonpos x hx := by
        rw [← e.excessAt_assignmentEquiv, Equiv.apply_symm_apply]
        exact g.excessAt_nonpos _ (Finset.mem_map_of_mem _ hx)
      excessAt_nonneg x hx := by
        rw [← e.excessAt_assignmentEquiv, Equiv.apply_symm_apply]
        exact g.excessAt_nonneg _ (Finset.mem_map_of_mem _ hx) }
  left_inv f := by
    ext1
    exact (e.assignmentEquiv K).symm_apply_apply f.toFun
  right_inv g := by
    ext1
    exact (e.assignmentEquiv K).apply_symm_apply g.toFun

@[simp]
theorem setFlowEquiv_apply_toFun (e : N ≃ₙ N') {cap : N.Assignment K} {A B : Finset V}
    (f : SetFlow cap A B) : (e.setFlowEquiv cap A B f).toFun = e.assignmentEquiv K f.toFun :=
  (rfl)

@[simp]
theorem setFlowEquiv_symm_apply_toFun (e : N ≃ₙ N') {cap : N.Assignment K} {A B : Finset V}
    (g : SetFlow (e.assignmentEquiv K cap) (A.map e.vertexEquiv.toEmbedding)
      (B.map e.vertexEquiv.toEmbedding)) :
    ((e.setFlowEquiv cap A B).symm g).toFun = (e.assignmentEquiv K).symm g.toFun :=
  (rfl)

/-- Transport preserves the value of an `A`–`B` flow. -/
@[simp]
theorem val_setFlowEquiv (e : N ≃ₙ N') {cap : N.Assignment K} {A B : Finset V}
    (f : SetFlow cap A B) : (e.setFlowEquiv cap A B f).val = f.val := by
  simp [SetFlow.val_def]

/-- Transport preserves and reflects maximality of an `A`–`B` flow. -/
@[simp]
theorem isMaximum_setFlowEquiv_iff (e : N ≃ₙ N') {cap : N.Assignment K} {A B : Finset V}
    (f : SetFlow cap A B) : (e.setFlowEquiv cap A B f).IsMaximum ↔ f.IsMaximum := by
  rw [SetFlow.isMaximum_iff, SetFlow.isMaximum_iff, ← (e.setFlowEquiv cap A B).forall_congr_right]
  simp

end Iso

end Network

end TauCeti

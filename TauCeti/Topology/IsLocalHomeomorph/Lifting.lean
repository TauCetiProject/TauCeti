/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.IsLocalHomeomorph
public import TauCeti.Topology.Order.Interval.Basic

/-!
# Extending interval lifts through local homeomorphisms

A lift of an ordered curve on `[a, T]`, with `a ≤ T < b`, extends to a strictly longer closed
interval when the curve is continuous on `[T, b]`. When the map is locally homeomorphic at the
lifted endpoint and the old lift lies in an open set `U`, the extended lift also stays in `U`.
The pasting step records agreement with the inverse branch on the added interval and uses an
ambient map agreeing with the chart on its source.

These are the right-continuation steps in compact confinement arguments for partial lifts.

## References

* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Set Filter Function
open scoped Topology

/-- A lift of an ambient map `f` on `[a, b]` extends across `[b, d]` using a partial
homeomorphism agreeing with `f` on its source. Assume `a ≤ b`, that the old endpoint is in the
chart source, and that the curve is continuous on `[b, d]` and stays in the chart target there.
The extended lift stays in `U` when both the old lift and the added inverse branch lie in `U`.
It agrees with both branches on their respective closed intervals, including their common
endpoint. -/
theorem PartialHomeomorph.exists_extend_lift_Icc
    {α X Y : Type*} [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α]
    [TopologicalSpace X] [TopologicalSpace Y] (e : PartialHomeomorph X Y)
    {f : X → Y} (he : EqOn f e e.source)
    {c : α → Y} {a b d : α} (hab : a ≤ b) {l : α → X}
    (hl : ContinuousOn l (Icc a b)) (hc : ContinuousOn c (Icc b d))
    (hproj : EqOn (f ∘ l) c (Icc a b)) (hsrc : l b ∈ e.source)
    (hmaps : MapsTo c (Icc b d) e.target) {U : Set X}
    (hlU : MapsTo l (Icc a b) U) (heU : MapsTo (e.symm ∘ c) (Icc b d) U) :
    ∃ l' : α → X, ContinuousOn l' (Icc a d) ∧ EqOn l' l (Icc a b) ∧
      EqOn l' (e.symm ∘ c) (Icc b d) ∧ EqOn (f ∘ l') c (Icc a d) ∧
      MapsTo l' (Icc a d) U := by
  classical
  have hjoin : l b = e.symm (c b) := by
    rw [← hproj ⟨hab, le_rfl⟩, comp_apply, he hsrc, e.left_inv hsrc]
  refine ⟨(Iic b).piecewise l (e.symm ∘ c),
    hl.piecewise_Iic_Icc (e.continuousOn_symm.comp hc hmaps) (fun _ ↦ hjoin),
    (piecewise_eqOn _ _ _).mono fun _ ht ↦ ht.2, ?_, ?_, ?_⟩
  · intro t ht
    by_cases htb : t ∈ Iic b
    · have : t = b := le_antisymm htb ht.1
      subst t
      simpa only [piecewise_eq_of_mem _ _ _ (mem_Iic.mpr le_rfl), comp_apply] using hjoin
    · exact piecewise_eq_of_notMem _ _ _ htb
  · intro t ht
    by_cases htb : t ∈ Iic b
    · simpa only [comp_apply, piecewise_eq_of_mem _ _ _ htb] using hproj ⟨ht.1, htb⟩
    · have hct := hmaps ⟨(lt_of_not_ge htb).le, ht.2⟩
      simpa only [comp_apply, piecewise_eq_of_notMem _ _ _ htb] using
        (he (e.map_target hct)).trans (e.right_inv hct)
  · intro t ht
    by_cases htb : t ∈ Iic b
    · simpa only [piecewise_eq_of_mem _ _ _ htb] using hlU ⟨ht.1, htb⟩
    · simpa only [piecewise_eq_of_notMem _ _ _ htb, comp_apply] using
        heU ⟨(lt_of_not_ge htb).le, ht.2⟩

/-- Restrict a local inverse chart at a point of an open set so its entire source lies in that
set. The ambient map agrees with the restricted chart on its source. -/
theorem IsLocalHomeomorphOn.exists_openPartialHomeomorph_source_subset
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {S U : Set X}
    (hf : IsLocalHomeomorphOn f S) (hU : IsOpen U) {x : X} (hxS : x ∈ S) (hxU : x ∈ U) :
    ∃ e : OpenPartialHomeomorph X Y, x ∈ e.source ∧ e.source ⊆ U ∧
      EqOn f e e.source := by
  obtain ⟨e, hs, he⟩ := hf x hxS
  refine ⟨e.restrOpen U hU, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hs, hxU⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact inter_subset_right
  · rw [OpenPartialHomeomorph.coe_restrOpen, he]
    exact eqOn_refl _ _

/-- A lift in an open set `U` on `[a, T]`, with `a ≤ T < b`, extends to `[a, u]` for some
`T < u ≤ b` when the curve is continuous on `[T, b]` and the ambient map is locally homeomorphic
at its endpoint. The extension agrees with the old lift and stays in `U`. -/
theorem IsLocalHomeomorphOn.exists_extend_lift_Icc
    {α X Y : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {S U : Set X}
    (hf : IsLocalHomeomorphOn f S) (hU : IsOpen U) {c : α → Y} {a T b : α}
    (hT : a ≤ T) (hTb : T < b) (hc : ContinuousOn c (Icc T b)) {l : α → X}
    (hl : ContinuousOn l (Icc a T)) (hproj : EqOn (f ∘ l) c (Icc a T))
    (hlU : MapsTo l (Icc a T) U) (hlS : l T ∈ S) :
    ∃ u ∈ Ioc T b, ∃ l' : α → X,
      ContinuousOn l' (Icc a u) ∧ EqOn l' l (Icc a T) ∧
      EqOn (f ∘ l') c (Icc a u) ∧ MapsTo l' (Icc a u) U := by
  obtain ⟨e, hsrc, heU, he⟩ :=
    hf.exists_openPartialHomeomorph_source_subset hU hlS (hlU ⟨hT, le_rfl⟩)
  have ht : c T ∈ e.target := by
    rw [← hproj ⟨hT, le_rfl⟩, comp_apply, he hsrc]
    exact e.map_source hsrc
  have hcont : ContinuousWithinAt c (Ici T) T :=
    (hc T ⟨le_rfl, hTb.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hTb)
  obtain ⟨v, hv, hsub⟩ := (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset hTb).mp
    (hcont.preimage_mem_nhdsWithin (e.open_target.mem_nhds ht))
  obtain ⟨u, hTu, huv⟩ := exists_between hv.1
  have hsub' : Icc T u ⊆ Ico T v := fun _ ht ↦ ⟨ht.1, ht.2.trans_lt huv⟩
  have hePartial : EqOn f (e.toPartialHomeomorph : X → Y) e.source := by
    rw [e.coe_toPartialHomeomorph]
    exact he
  have heUPartial : MapsTo (e.toPartialHomeomorph.symm ∘ c) (Icc T u) U := by
    rw [e.coe_toPartialHomeomorph_symm]
    exact fun _ ht ↦ heU (e.map_target (hsub (hsub' ht)))
  obtain ⟨l', hl', heq, _, hp, hm⟩ := e.toPartialHomeomorph.exists_extend_lift_Icc hePartial hT hl
    (hc.mono (Icc_subset_Icc le_rfl (huv.le.trans hv.2))) hproj hsrc
    (fun _ ht ↦ hsub (hsub' ht)) hlU
    heUPartial
  exact ⟨u, ⟨hTu, huv.le.trans hv.2⟩, l', hl', heq, hp, hm⟩

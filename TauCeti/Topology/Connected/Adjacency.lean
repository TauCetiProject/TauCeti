/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import TauCeti.Topology.Connected.Basic
public import TauCeti.Topology.ConnectedComponents
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
# Adjacency of actual connected components

The vertices are Mathlib's connected components of a subset. Two distinct
components are adjacent when their ambient closures share a point of a
specified regular set. A continuous curve leaving the subset only at finitely
many parameters, with regular values at those parameters, gives a finite graph walk.

This criterion turns curves with finitely many crossings into connectivity
results for component adjacency graphs, such as chamber graphs of wall complements.
No local connectedness or separation assumption on the ambient space is needed.

## Attribution

Adapted in full from `Mei/Topology/Connected/Basic.lean` and
`Mei/Topology/Connected/Adjacency.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), at
`9cf969cdee9748087aae45dbf4888a130890655c` (Apache 2.0).
Original copyright (c) 2026 Mei contributors; original author: Codex.
-/

public section

open Set Filter

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

/-- The graph of actual components, with adjacency witnessed by a common
ambient closure point in the prescribed regular set. -/
def componentAdjacencyGraph (s R : Set X) : SimpleGraph (ConnectedComponents s) where
  Adj c d := c ≠ d ∧ ∃ x ∈ R, x ∈ closure c.carrierIn ∧ x ∈ closure d.carrierIn
  symm := ⟨fun _ _ ⟨hne, x, hx, hc, hd⟩ => ⟨hne.symm, x, hx, hd, hc⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

/-- Adjacency is exactly a regular common closure point between distinct components. -/
@[simp]
theorem componentAdjacencyGraph_adj {s R : Set X} {c d : ConnectedComponents s} :
    (componentAdjacencyGraph s R).Adj c d ↔
      c ≠ d ∧ ∃ x ∈ R, x ∈ closure c.carrierIn ∧ x ∈ closure d.carrierIn := Iff.rfl

/-- Enlarging the regular set enlarges the component adjacency graph. -/
@[gcongr, mono]
theorem componentAdjacencyGraph_mono {s R₁ R₂ : Set X} (hR : R₁ ⊆ R₂) :
    componentAdjacencyGraph s R₁ ≤ componentAdjacencyGraph s R₂ := by
  rintro c d ⟨hcd, x, hx, hc, hd⟩
  exact ⟨hcd, x, hR hx, hc, hd⟩

/-- Two components are reachable if their closures share a regular point. -/
theorem reachable_componentAdjacencyGraph_of_mem_closure {s R : Set X}
    {c d : ConnectedComponents s} {x : X} (hx : x ∈ R)
    (hc : x ∈ closure c.carrierIn) (hd : x ∈ closure d.carrierIn) :
    (componentAdjacencyGraph s R).Reachable c d := by
  by_cases hcd : c = d
  · rw [hcd]
  · exact SimpleGraph.Adj.reachable (componentAdjacencyGraph_adj.mpr ⟨hcd, x, hx, hc, hd⟩)

/-- Two points lie in the same component if they are joined by a preconnected set in the
ambient set. -/
theorem reachable_componentAdjacencyGraph_of_isPreconnected {s R : Set X} {A : Set X}
    (hA : IsPreconnected A) (hAs : A ⊆ s) {x y : X} (hx : x ∈ A) (hy : y ∈ A)
    (hxs : x ∈ s) (hys : y ∈ s) :
    (componentAdjacencyGraph s R).Reachable
      (ConnectedComponents.mk ⟨x, hxs⟩) (ConnectedComponents.mk ⟨y, hys⟩) := by
  have hxy : ConnectedComponents.mk (⟨x, hxs⟩ : s) =
      ConnectedComponents.mk ⟨y, hys⟩ :=
    ((ConnectedComponents.mk_eq_mk_iff_mem_connectedComponentIn
      (x := (⟨y, hys⟩ : s)) (y := ⟨x, hxs⟩)).mpr
      (hA.subset_connectedComponentIn hx hAs hy)).symm
  rw [hxy]

/-- A regular point joins the components on its two sides of an isolated exceptional parameter. -/
theorem reachable_componentAdjacencyGraph_of_isolated_exception {s R : Set X} {f : ℝ → X}
    {a b t : ℝ} (hf : ContinuousOn f (Icc a b)) (hat : a < t) (htb : t < b)
    {ha : f a ∈ s} {hb : f b ∈ s}
    (hsa : ∀ u ∈ Ico a t, f u ∈ s) (hsb : ∀ u ∈ Ioc t b, f u ∈ s) (ht : f t ∈ R) :
    (componentAdjacencyGraph s R).Reachable
      (ConnectedComponents.mk ⟨f a, ha⟩) (ConnectedComponents.mk ⟨f b, hb⟩) := by
  have hft : ContinuousAt f t := hf.continuousAt (Icc_mem_nhds hat htb)
  have hca : f t ∈ closure (connectedComponentIn s (f a)) :=
    isPreconnected_Ico.mem_closure_connectedComponentIn
      (hf.mono (fun u hu => ⟨hu.1, hu.2.le.trans htb.le⟩)) ⟨le_rfl, hat⟩
      (by rw [closure_Ico hat.ne]; exact ⟨hat.le, le_rfl⟩)
      hft.continuousWithinAt hsa
  have hcb : f t ∈ closure (connectedComponentIn s (f b)) :=
    isPreconnected_Ioc.mem_closure_connectedComponentIn
      (hf.mono (fun u hu => ⟨hat.le.trans hu.1.le, hu.2⟩)) ⟨htb, le_rfl⟩
      (by rw [closure_Ioc htb.ne]; exact ⟨le_rfl, htb.le⟩)
      hft.continuousWithinAt hsb
  exact reachable_componentAdjacencyGraph_of_mem_closure ht
    (by rwa [ConnectedComponents.carrierIn_mk])
    (by rwa [ConnectedComponents.carrierIn_mk])

end TauCeti

namespace TauCeti
variable {X : Type*} [TopologicalSpace X]

/-- A continuous curve with only finitely many exceptional parameters gives
a finite adjacency walk between its endpoint components. Only values at
exceptional parameters need to lie in the regular set.
The curve may be constant and the endpoints may belong to the same component. -/
theorem reachable_componentAdjacencyGraph_of_continuousOn
    {s R : Set X} {f : ℝ → X} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    (hab : a ≤ b) (ha : f a ∈ s) (hb : f b ∈ s)
    (hfin : {t ∈ Icc a b | f t ∉ s}.Finite)
    (hR : ∀ t ∈ Icc a b, f t ∉ s → f t ∈ R) :
    (componentAdjacencyGraph s R).Reachable
      (ConnectedComponents.mk ⟨f a, ha⟩) (ConnectedComponents.mk ⟨f b, hb⟩) := by
  classical
  obtain ⟨T, hT'⟩ := hfin.exists_finset
  have hT : ∀ t ∈ Icc a b, f t ∉ s → t ∈ T :=
    fun t ht hbad => (hT' t).mpr ⟨ht, hbad⟩
  clear hT' hfin
  induction T using Finset.strongInductionOn generalizing a b with
  | _ T ih =>
    by_cases hall : ∀ t ∈ Icc a b, f t ∈ s
    -- If the curve stays in the set, its image lies in a single component.
    · refine reachable_componentAdjacencyGraph_of_isPreconnected
        (isPreconnected_Icc.image f hf) ?_ ⟨a, ⟨le_rfl, hab⟩, rfl⟩
          ⟨b, ⟨hab, le_rfl⟩, rfl⟩ ha hb
      exact image_subset_iff.mpr hall
    · push Not at hall
      obtain ⟨t, ht, hbad⟩ := hall
      have htT : t ∈ T := hT t ht hbad
      have hat : a < t := lt_of_le_of_ne ht.1 (by rintro rfl; exact hbad ha)
      have htb : t < b := lt_of_le_of_ne ht.2 (by rintro rfl; exact hbad hb)
      -- Choose an interval inside `Icc a b` which meets the remaining exceptions nowhere.
      obtain ⟨δ, hδ, hδsub⟩ := (nhds_basis_Icc_pos t).mem_iff.mp
        (Filter.inter_mem (Icc_mem_nhds hat htb)
          ((T.erase t).isClosed.isOpen_compl.mem_nhds (by simp)))
      have hleft : a ≤ t - δ := (hδsub (Set.left_mem_Icc.mpr (by linarith))).1.1
      have hright : t + δ ≤ b := (hδsub (Set.right_mem_Icc.mpr (by linarith))).1.2
      have hlocal (u : ℝ) (hu : u ∈ Icc (t - δ) (t + δ)) (hut : u ≠ t) : f u ∈ s := by
        by_contra hus
        exact (hδsub hu).2 (Finset.mem_coe.mpr
          (Finset.mem_erase.mpr ⟨hut, hT u (hδsub hu).1 hus⟩))
      have hs : f (t - δ) ∈ s :=
        hlocal _ (Set.left_mem_Icc.mpr (by linarith)) (sub_lt_self t hδ).ne
      have hu : f (t + δ) ∈ s :=
        hlocal _ (Set.right_mem_Icc.mpr (by linarith)) (lt_add_of_pos_right t hδ).ne'
      have hleft_sub : Icc a (t - δ) ⊆ Icc a b :=
        Icc_subset_Icc le_rfl ((sub_le_self t hδ.le).trans htb.le)
      have hright_sub : Icc (t + δ) b ⊆ Icc a b :=
        Icc_subset_Icc (hat.le.trans (le_add_of_nonneg_right hδ.le)) le_rfl
      -- Each side has strictly fewer exceptional parameters, so induction joins its endpoints.
      have hbefore := ih (T.erase t) (Finset.erase_ssubset htT)
        (hf.mono hleft_sub) hleft ha hs
        (fun u hu' => hR u (hleft_sub hu'))
        (fun u hu' hus => Finset.mem_erase.mpr
          ⟨ne_of_lt (hu'.2.trans_lt (sub_lt_self t hδ)), hT u (hleft_sub hu') hus⟩)
      have hafter := ih (T.erase t) (Finset.erase_ssubset htT)
        (hf.mono hright_sub) hright hu hb
        (fun u hu' => hR u (hright_sub hu'))
        (fun u hu' hus => Finset.mem_erase.mpr
          ⟨ne_of_gt ((lt_add_of_pos_right t hδ).trans_le hu'.1), hT u (hright_sub hu') hus⟩)
      -- At the remaining exceptional point, the two adjacent regular values are adjacent
      -- or already represent the same component.
      have hmiddle : (componentAdjacencyGraph s R).Reachable
          (ConnectedComponents.mk ⟨f (t - δ), hs⟩) (ConnectedComponents.mk ⟨f (t + δ), hu⟩) :=
        reachable_componentAdjacencyGraph_of_isolated_exception
          (hf.mono (Icc_subset_Icc hleft hright))
          (sub_lt_self t hδ) (lt_add_of_pos_right t hδ)
          (fun u hu' => hlocal u ⟨hu'.1, hu'.2.le.trans (le_add_of_nonneg_right hδ.le)⟩ hu'.2.ne)
          (fun u hu' => hlocal u ⟨(sub_le_self t hδ.le).trans hu'.1.le, hu'.2⟩ hu'.1.ne')
          (hR t ht hbad)
      exact hbefore.trans (hmiddle.trans hafter)

end TauCeti

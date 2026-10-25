/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Irreducible
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.Topology.PathComponent
public import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue

/-!
# Connected components

This file records general topological properties of connected components, and of the quotient of a
space by them.

## Main declarations

* `ConnectedComponents.instMulActionOfContinuousConstSMul`: an action by continuous maps descends
  to connected components.
* `ConnectedComponents.coe_eq_coe_iff_connectedComponentIn_eq`: points of a set lie in the same
  connected component of the subspace exactly when they have the same component in the set.
* `Homeomorph.image_connectedComponent`: a homeomorphism maps a connected component onto
  the connected component of the image point.
* `TauCeti.frontier_connectedComponentIn_subset_compl`: in a locally connected space, a connected
  component of an open set has its frontier in the complement of that set.
* `IsPreconnected.subset_connectedComponentIn_of_inter_closure_subset`: a preconnected set through
  a point of an open set `U` lies in the component of that point in `U`, as soon as it meets the
  closure of that component only inside `U`.
* `IsClosed.connectedComponentIn`: a connected component of a closed set is closed.
* `IsClosed.exists_isOpen_isCompact_closure_disjoint_frontier`: in a locally compact Hausdorff
  space, a compact connected component of a closed set `F` has an open neighbourhood with compact
  closure whose frontier misses `F`.
* `TauCeti.connectedComponentIn_eq_of_lt`: a preconnected set on which a function stays on one
  side of a value it never takes is a connected component.
* `TauCeti.isPreconnected_compl_of_isPreconnected_frontier`: in a preconnected, locally connected
  space, an open set with preconnected frontier has preconnected complement.
* `TauCeti.isPreconnected_compl_of_isDiscrete`: removing from a preconnected space a closed
  discrete set, each point of which has small connected punctured neighbourhoods, leaves it
  preconnected.
* `TauCeti.instT1SpaceConnectedComponents`: the connected-components quotient of any topological
  space is a T1 space.
* `TauCeti.connectedComponentsSigmaHomeomorph`: a locally connected space is homeomorphic
  to the disjoint union of its connected components.
* `TauCeti.finite_connectedComponents_of_finite_irreducibleComponents`: finiteness of the
  irreducible components implies finiteness of the connected components.
* `TauCeti.isClopen_of_finite_pairwiseDisjoint_closed_cover`: each member of a finite pairwise
  disjoint closed cover is clopen.
* `TauCeti.natCard_connectedComponents_eq_of_iUnion_eq_univ`: a space covered by finitely many
  pairwise disjoint closed connected sets has exactly as many connected components as sets.
-/

public section

open Function Set Topology

universe u

variable {X : Type u} [TopologicalSpace X]

namespace ConnectedComponents

variable {G X : Type*} [Monoid G] [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X]

/-- An action by continuous maps induces an action on connected components. -/
noncomputable instance instMulActionOfContinuousConstSMul :
    MulAction G (ConnectedComponents X) where
  smul g := (continuous_const_smul g : Continuous (fun x : X ↦ g • x)).connectedComponentsMap
  one_smul x := by
    obtain ⟨x, rfl⟩ := surjective_coe x
    exact congrArg ConnectedComponents.mk (one_smul G x)
  mul_smul g h x := by
    obtain ⟨x, rfl⟩ := surjective_coe x
    exact congrArg ConnectedComponents.mk (mul_smul g h x)

/-- The action on components sends the component of a point to that of its translate. -/
@[simp]
theorem smul_mk (g : G) (x : X) :
    g • ConnectedComponents.mk x = ConnectedComponents.mk (g • x) := (rfl)

/-- Each fixed element still acts continuously on the quotient space of components. -/
instance : ContinuousConstSMul G (ConnectedComponents X) where
  continuous_const_smul g :=
    (continuous_const_smul g : Continuous (fun x : X ↦ g • x)).connectedComponentsMap_continuous

end ConnectedComponents

namespace ConnectedComponents

/-- Two points of a set `F` define the same connected component of the subspace `F` exactly when
they have the same connected component in `F`. -/
theorem coe_eq_coe_iff_connectedComponentIn_eq {F : Set X} {a b : X} (ha : a ∈ F) (hb : b ∈ F) :
    ((⟨a, ha⟩ : F) : ConnectedComponents F) = (⟨b, hb⟩ : F) ↔
      connectedComponentIn F a = connectedComponentIn F b := by
  rw [connectedComponentIn_eq_image ha, connectedComponentIn_eq_image hb,
    Subtype.val_injective.image_injective.eq_iff, coe_eq_coe]

end ConnectedComponents

namespace Homeomorph

/-- A homeomorphism maps a connected component onto the connected component of the image point. -/
@[simp]
theorem image_connectedComponent {Y : Type*} [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    e '' connectedComponent x = connectedComponent (e x) := by
  simpa only [connectedComponentIn_univ, _root_.Set.image_univ_of_surjective e.surjective] using
    e.image_connectedComponentIn (s := _root_.Set.univ) (x := x) (_root_.Set.mem_univ x)

end Homeomorph

namespace TauCeti

/-- **The frontier of a connected component of an open set misses the set.** Equivalently,
`frontier (connectedComponentIn F x) ∩ F = ∅`: the component is clopen in `F`. -/
theorem frontier_connectedComponentIn_subset_compl [LocallyConnectedSpace X] {F : Set X}
    (hF : IsOpen F) (x : X) : frontier (connectedComponentIn F x) ⊆ Fᶜ := by
  intro y hy hyF
  have hC : IsOpen (connectedComponentIn F x) := hF.connectedComponentIn
  obtain ⟨z, hzy, hzx⟩ :=
    mem_closure_iff.mp hy.1 _ hF.connectedComponentIn (mem_connectedComponentIn hyF)
  have hyC : y ∈ connectedComponentIn F x := by
    rw [connectedComponentIn_eq hzx, ← connectedComponentIn_eq hzy]
    exact mem_connectedComponentIn hyF
  exact hy.2 (by rwa [hC.interior_eq])

/-- **Trapping a preconnected set in a component of an open set.** Let `U` be open in a locally
connected space and let `C` be the connected component of `x ∈ U` in `U`. A preconnected set `A`
through `x` lies in `C` as soon as it meets the closure of `C` only inside `U`. This weakens the
hypothesis `A ⊆ U` of `IsPreconnected.subset_connectedComponentIn`. -/
theorem _root_.IsPreconnected.subset_connectedComponentIn_of_inter_closure_subset
    [LocallyConnectedSpace X] {A U : Set X} {x : X} (hA : IsPreconnected A)
    (hU : IsOpen U) (hxA : x ∈ A) (hxU : x ∈ U)
    (h : A ∩ closure (_root_.connectedComponentIn U x) ⊆ U) :
    A ⊆ _root_.connectedComponentIn U x := by
  refine hA.subset_of_closure_inter_subset hU.connectedComponentIn
    ⟨x, hxA, mem_connectedComponentIn hxU⟩ fun y hy => ?_
  by_contra hyC
  have hfr : y ∈ frontier (_root_.connectedComponentIn U x) :=
    ⟨hy.1, by rwa [hU.connectedComponentIn.interior_eq]⟩
  exact frontier_connectedComponentIn_subset_compl hU x hfr (h ⟨hy.2, hy.1⟩)

/-- A connected component of a closed set is closed. -/
protected theorem _root_.IsClosed.connectedComponentIn {F : Set X} {x : X} (hF : IsClosed F) :
    IsClosed (connectedComponentIn F x) := by
  refine closure_subset_iff_isClosed.mp fun y hy => ?_
  by_cases hx : x ∈ F
  · exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hx))
      (closure_minimal (connectedComponentIn_subset F x) hF) hy
  · rw [connectedComponentIn_eq_empty hx, closure_empty] at hy
    exact hy.elim

/-- **A compact component of a closed set is cut out by an open set.** In a locally compact
Hausdorff space, if the connected component of `x` in a closed set `F` is compact, then it has an
open neighbourhood `V` with compact closure whose frontier misses `F`. -/
theorem _root_.IsClosed.exists_isOpen_isCompact_closure_disjoint_frontier [T2Space X]
    [LocallyCompactSpace X] {F : Set X} (hF : IsClosed F) {x : X}
    (hx : IsCompact (connectedComponentIn F x)) :
    ∃ V, IsOpen V ∧ connectedComponentIn F x ⊆ V ∧ IsCompact (closure V) ∧
      Disjoint (frontier V) F := by
  by_cases hxF : x ∈ F
  swap
  · exact ⟨∅, isOpen_empty, by simp [connectedComponentIn_eq_empty hxF], by simp, by simp⟩
  -- a compact neighbourhood `Y` of the component inside `F`, in which the component is the same
  obtain ⟨W, hWo, hQW, -, hWc⟩ :=
    exists_open_between_and_isCompact_closure hx isOpen_univ (subset_univ _)
  set Y := F ∩ closure W
  have hxY : x ∈ Y := ⟨hxF, subset_closure (hQW (mem_connectedComponentIn hxF))⟩
  have hQY : connectedComponentIn Y x = connectedComponentIn F x :=
    (connectedComponentIn_mono x inter_subset_left).antisymm
      (isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hxF)
        fun y hy => ⟨connectedComponentIn_subset _ _ hy, subset_closure (hQW hy)⟩)
  have : CompactSpace Y := isCompact_iff_compactSpace.mp (hWc.inter_left hF)
  set y : Y := ⟨x, hxY⟩
  have himage : ((↑) : Y → X) '' connectedComponent y = connectedComponentIn F x := by
    rw [← connectedComponentIn_eq_image hxY, hQY]
  -- finitely many clopen subsets of `Y` around `y` already cut the component down into `W`
  obtain ⟨u, hu⟩ := (hWo.preimage continuous_subtype_val).isClosed_compl.isCompact
    |>.elim_finite_subfamily_closed (fun s : {s : Set Y // IsClopen s ∧ y ∈ s} => s.1)
      (fun s => s.2.1.1) (by
        rw [← connectedComponent_eq_iInter_isClopen, disjoint_compl_left_iff_subset]
        exact fun z hz => hQW (himage ▸ mem_image_of_mem _ hz))
  set s : Set Y := ⋂ i ∈ u, i.1
  have hs : IsClopen s := isClopen_biInter_finset fun i _ => i.2.1
  have hsW : s ⊆ (↑) ⁻¹' W := disjoint_compl_left_iff_subset.mp hu
  obtain ⟨O, hOo, hOs⟩ := isOpen_induced_iff.mp hs.isOpen
  -- a neighbourhood `V` of the image of `s` whose closure stays in `W ∩ O`
  obtain ⟨V, hVo, hsV, hVWO, hVc⟩ := exists_open_between_and_isCompact_closure
    (hs.isClosed.isCompact.image continuous_subtype_val) (hWo.inter hOo)
    (image_subset_iff.mpr fun z hz => ⟨hsW hz, by rw [← hOs] at hz; exact hz⟩)
  refine ⟨V, hVo, ?_, hVc, disjoint_left.mpr fun z hz hzF => ?_⟩
  · rw [← himage]
    exact (image_mono (hs.connectedComponent_subset
      (mem_iInter₂.mpr fun i _ => i.2.2))).trans hsV
  · -- a frontier point of `V` in `F` lies in `Y ∩ O`, hence in the image of `s ⊆ V`
    have hzWO := hVWO hz.1
    have hzs : (⟨z, hzF, subset_closure hzWO.1⟩ : Y) ∈ s := by
      rw [← hOs]
      exact hzWO.2
    exact hz.2 (by rw [hVo.interior_eq]; exact hsV ⟨_, hzs, rfl⟩)

/-- **A strict superlevel set cuts out a connected component.** Let `φ` be continuous on `D` and
never equal to `c` there. A preconnected subset `H ⊆ D` containing every point of `D` where `φ`
exceeds `c` is the connected component in `D` of any of its points `z` with `c < φ z`: by the
intermediate value theorem, that component cannot reach a point where `φ` is below `c`. -/
theorem connectedComponentIn_eq_of_lt {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderClosedTopology α] {D H : Set X} {z : X} {φ : X → α} {c : α} (hH : IsPreconnected H)
    (hHD : H ⊆ D) (hz : z ∈ H) (hzc : c < φ z) (hφ : ContinuousOn φ D)
    (hDne : ∀ q ∈ D, φ q ≠ c) (hmem : ∀ q ∈ D, c < φ q → q ∈ H) :
    connectedComponentIn D z = H := by
  apply Subset.antisymm
  · intro q hq
    have hqD : q ∈ D := connectedComponentIn_subset D z hq
    apply hmem q hqD
    rcases lt_or_gt_of_ne (hDne q hqD) with hqlt | hqgt
    · have hzC : z ∈ connectedComponentIn D z := mem_connectedComponentIn (hHD hz)
      obtain ⟨p, hpC, hpc⟩ := isPreconnected_connectedComponentIn.intermediate_value hq hzC
        (hφ.mono (connectedComponentIn_subset D z)) ⟨hqlt.le, hzc.le⟩
      exact (hDne p (connectedComponentIn_subset D z hpC) hpc).elim
    · exact hqgt
  · exact hH.subset_connectedComponentIn hz hHD

/-- **An open set with preconnected frontier has preconnected complement**, in a preconnected,
locally connected space.

Openness is needed: in `ℝ` the frontier of `{0}` is `{0}`, while `{0}ᶜ` is disconnected. -/
theorem isPreconnected_compl_of_isPreconnected_frontier [LocallyConnectedSpace X]
    [PreconnectedSpace X] {U : Set X} (hU : IsOpen U) (hf : IsPreconnected (frontier U)) :
    IsPreconnected Uᶜ := by
  -- If `frontier U` is nonempty, each nonempty component `D` of the exterior `(closure U)ᶜ`
  -- reaches `frontier U` through its own frontier: a frontier point of `D` lies in `closure U`
  -- but, being a limit of exterior points, not in the open set `U`. So `frontier U ∪ D` is
  -- preconnected, and `Uᶜ` is the union of these sets, all of which contain `frontier U`.
  rcases (frontier U).eq_empty_or_nonempty with h | ⟨p, hp⟩
  · rcases frontier_eq_empty_iff.mp h with rfl | rfl
    · simpa using isPreconnected_univ
    · simpa using isPreconnected_empty
  have hpiece : ∀ y, IsPreconnected (frontier U ∪ connectedComponentIn (closure U)ᶜ y) := by
    intro y
    set D := connectedComponentIn (closure U)ᶜ y
    rcases D.eq_empty_or_nonempty with hD | hD
    · simpa [hD] using hf
    have hDu : D ≠ univ := fun h =>
      connectedComponentIn_subset _ _ (h ▸ mem_univ p : p ∈ D) hp.1
    obtain ⟨q, hq⟩ := nonempty_frontier_iff.mpr ⟨hD, hDu⟩
    have hqU : q ∈ frontier U := by
      refine ⟨?_, ?_⟩
      · simpa using frontier_connectedComponentIn_subset_compl isClosed_closure.isOpen_compl y hq
      · rw [hU.interior_eq]
        intro hqU
        obtain ⟨z, hzU, hzD⟩ := mem_closure_iff.mp hq.1 U hU hqU
        exact connectedComponentIn_subset _ _ hzD (subset_closure hzU)
    have hins : IsPreconnected (insert q D) :=
      isPreconnected_connectedComponentIn.subset_closure (subset_insert q D)
        (insert_subset hq.1 subset_closure)
    have := hf.union' ⟨q, hqU, mem_insert q D⟩ hins
    rwa [union_insert, insert_eq_of_mem (mem_union_left D hqU)] at this
  have hcover : Uᶜ = ⋃ y, frontier U ∪ connectedComponentIn (closure U)ᶜ y := by
    refine Subset.antisymm (fun x hx => mem_iUnion.mpr ⟨x, ?_⟩) (iUnion_subset fun y => ?_)
    · by_cases hxc : x ∈ closure U
      · exact Or.inl (hU.frontier_eq ▸ ⟨hxc, hx⟩)
      · exact Or.inr (mem_connectedComponentIn hxc)
    · refine union_subset (hU.frontier_eq ▸ fun x hx => hx.2) fun x hx hxU => ?_
      exact connectedComponentIn_subset _ _ hx (subset_closure hxU)
  rw [hcover]
  exact isPreconnected_iUnion ⟨p, mem_iInter.mpr fun _ => Or.inl hp⟩ hpiece

/-- **Removing a closed discrete set keeps a space preconnected**, provided each removed point
has arbitrarily small neighbourhoods whose punctured versions are connected.

The hypothesis on the punctured neighbourhoods is what fails in `ℝ`, where removing `0`
disconnects the line. -/
theorem isPreconnected_compl_of_isDiscrete [PreconnectedSpace X] {s : Set X} (hs : IsClosed s)
    (hd : IsDiscrete s) (h : ∀ x ∈ s, ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsConnected (V \ {x})) :
    IsPreconnected sᶜ := by
  have hV : ∀ x ∈ s, ∃ V ∈ 𝓝 x, V \ {x} ⊆ sᶜ ∧ IsConnected (V \ {x}) := by
    intro x hx
    obtain ⟨u, hu, hus⟩ := isDiscrete_iff_forall_mem_exists_isOpen.1 hd x hx
    have hxu : x ∈ u := (hus.symm ▸ mem_singleton x : x ∈ u ∩ s).1
    obtain ⟨V, hV, hVu, hc⟩ := h x hx u (hu.mem_nhds hxu)
    refine ⟨V, hV, fun y hy hys ↦ hy.2 ?_, hc⟩
    simpa [← hus] using And.intro (hVu hy.1) hys
  choose! V hVn hVs hVc using hV
  -- The punctured neighbourhood of a removed point lies on one side of a separation of `sᶜ`;
  -- putting the point on that side separates the whole space, so one side is empty.
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hcov hdisj
  have hside (x : X) (hx : x ∈ s) : V x \ {x} ⊆ u ∨ V x \ {x} ⊆ v :=
    isPreconnected_iff_subset_of_disjoint.1 (hVc x hx).isPreconnected u v hu hv
      ((hVs x hx).trans hcov) (subset_empty_iff.1 <| hdisj ▸ inter_subset_inter_left _ (hVs x hx))
  -- Extending each side by the removed points whose punctured neighbourhood it contains
  -- separates the whole space.
  have hext (w : Set X) (hw : IsOpen w) : IsOpen (w \ s ∪ {x | x ∈ s ∧ V x \ {x} ⊆ w}) := by
    refine isOpen_iff_mem_nhds.2 fun y hy ↦ ?_
    rcases hy with hy | ⟨hys, hyw⟩
    · exact Filter.mem_of_superset ((hw.inter hs.isOpen_compl).mem_nhds hy) subset_union_left
    · refine Filter.mem_of_superset (hVn y hys) fun z hz ↦ ?_
      rcases eq_or_ne z y with rfl | hzy
      · exact Or.inr ⟨hys, hyw⟩
      · exact Or.inl ⟨hyw ⟨hz, hzy⟩, hVs y hys ⟨hz, hzy⟩⟩
  have hnot (x : X) (hx : x ∈ s) (hxu : V x \ {x} ⊆ u) (hxv : V x \ {x} ⊆ v) : False := by
    obtain ⟨z, hz⟩ := (hVc x hx).nonempty
    exact (eq_empty_iff_forall_notMem.1 hdisj) z ⟨hVs x hx hz, hxu hz, hxv hz⟩
  rcases isPreconnected_iff_subset_of_disjoint.1 isPreconnected_univ _ _ (hext u hu) (hext v hv)
    (fun y _ ↦ by
      by_cases hys : y ∈ s
      · exact (hside y hys).imp (fun h ↦ Or.inr ⟨hys, h⟩) fun h ↦ Or.inr ⟨hys, h⟩
      · exact (hcov hys).imp (fun h ↦ Or.inl ⟨h, hys⟩) fun h ↦ Or.inl ⟨h, hys⟩)
    (by
      refine eq_empty_iff_forall_notMem.2 fun y ⟨_, hyu, hyv⟩ ↦ ?_
      rcases hyu with hyu | hyu <;> rcases hyv with hyv | hyv
      · exact (eq_empty_iff_forall_notMem.1 hdisj) y ⟨hyu.2, hyu.1, hyv.1⟩
      · exact (hyu.2 hyv.1).elim
      · exact (hyv.2 hyu.1).elim
      · exact hnot y hyu.1 hyu.2 hyv.2) with h | h
  · exact Or.inl fun y hy ↦ ((h (mem_univ y)).resolve_right fun h' ↦ hy h'.1).1
  · exact Or.inr fun y hy ↦ ((h (mem_univ y)).resolve_right fun h' ↦ hy h'.1).1

/-- The quotient of a topological space by its connected components is a T1 space. -/
instance instT1SpaceConnectedComponents : T1Space (ConnectedComponents X) :=
  ⟨fun c => by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [← ConnectedComponents.isQuotientMap_coe.isClosed_preimage,
      connectedComponents_preimage_singleton]
    exact isClosed_connectedComponent⟩

/-- A fibre of the quotient to connected components is path-connected when the ambient space is
locally path-connected. -/
instance instPathConnectedSpaceConnectedComponentsFiber [LocallyPathConnectedSpace X]
    (C : ConnectedComponents X) :
    PathConnectedSpace (ConnectedComponents.mk ⁻¹' {C} : Set X) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  rw [connectedComponents_preimage_singleton, ← pathComponent_eq_connectedComponent]
  infer_instance

/-- A fibre of the quotient to connected components is locally path-connected when the ambient
space is locally path-connected. -/
instance instLocallyPathConnectedSpaceConnectedComponentsFiber [LocallyPathConnectedSpace X]
    (C : ConnectedComponents X) :
    LocallyPathConnectedSpace (ConnectedComponents.mk ⁻¹' {C} : Set X) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  rw [connectedComponents_preimage_singleton, ← pathComponent_eq_connectedComponent]
  infer_instance

/-- **A locally connected space is the disjoint union of its connected components.**

The summand indexed by `C : ConnectedComponents X` is the fibre of the canonical quotient map
over `C`, so this decomposition does not require choosing representatives. -/
noncomputable def connectedComponentsSigmaHomeomorph [LocallyConnectedSpace X] :
    (Σ C : ConnectedComponents X, (ConnectedComponents.mk ⁻¹' {C} : Set X)) ≃ₜ X := by
  let e : (Σ C : ConnectedComponents X, (ConnectedComponents.mk ⁻¹' {C} : Set X)) ≃ X :=
    Equiv.sigmaPreimageEquiv ConnectedComponents.mk
  exact e.toHomeomorphOfContinuousOpen
    (continuous_sigma fun _ ↦ continuous_subtype_val)
    (isOpenMap_sigma.mpr fun C ↦
      ((isOpen_discrete {C}).preimage ConnectedComponents.continuous_coe).isOpenMap_subtype_val)

@[simp]
theorem connectedComponentsSigmaHomeomorph_apply [LocallyConnectedSpace X]
    (z : Σ C : ConnectedComponents X, (ConnectedComponents.mk ⁻¹' {C} : Set X)) :
    connectedComponentsSigmaHomeomorph z = z.2 :=
  (rfl)

@[simp]
theorem connectedComponentsSigmaHomeomorph_symm_apply [LocallyConnectedSpace X] (x : X) :
    connectedComponentsSigmaHomeomorph.symm x =
      ⟨ConnectedComponents.mk x, ⟨x, Set.mem_singleton _⟩⟩ :=
  (rfl)

/-- A space with finitely many irreducible components has finitely many connected components. -/
theorem finite_connectedComponents_of_finite_irreducibleComponents
    (h : (irreducibleComponents X).Finite) : Finite (ConnectedComponents X) := by
  let C : Set (ConnectedComponents X) :=
    ⋃ Z ∈ irreducibleComponents X, ConnectedComponents.mk '' Z
  have hC : C.Finite := h.biUnion fun Z hZ =>
    Set.Subsingleton.finite <| by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [ConnectedComponents.coe_eq_coe']
      exact hZ.1.isConnected.isPreconnected.subset_connectedComponent hy hx
  apply Finite.of_finite_univ
  rw [← Set.eq_univ_of_forall]
  · exact hC
  · intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    exact Set.mem_biUnion (irreducibleComponent_mem_irreducibleComponents x)
      ⟨x, mem_irreducibleComponent, rfl⟩

/-- Every member of a finite pairwise disjoint closed cover is clopen. -/
theorem isClopen_of_finite_pairwiseDisjoint_closed_cover {ι : Type*} [Finite ι] {U : ι → Set X}
    (hclosed : ∀ i, IsClosed (U i)) (hdisj : Pairwise (Disjoint on U))
    (hunion : ⋃ i, U i = univ) (i : ι) : IsClopen (U i) := by
  refine ⟨hclosed i, ?_⟩
  rw [← isClosed_compl_iff, compl_eq_univ_sdiff, ← hunion, iUnion_sdiff]
  refine isClosed_iUnion_of_finite fun j ↦ ?_
  rcases eq_or_ne j i with rfl | hne
  · simp
  · simpa only [(hdisj hne).sdiff_eq_left] using hclosed j

/-- A space covered by finitely many pairwise disjoint closed connected sets has exactly as many
connected components as sets: the sets are its connected components. -/
theorem natCard_connectedComponents_eq_of_iUnion_eq_univ {ι : Type*} [Finite ι] {U : ι → Set X}
    (hclosed : ∀ i, IsClosed (U i)) (hdisj : Pairwise (Disjoint on U))
    (hunion : ⋃ i, U i = univ) (hconn : ∀ i, IsConnected (U i)) :
    Nat.card (ConnectedComponents X) = Nat.card ι := by
  have hclopen : ∀ i, IsClopen (U i) :=
    isClopen_of_finite_pairwiseDisjoint_closed_cover hclosed hdisj hunion
  have (i : ι) : Unique (ConnectedComponents (U i)) :=
    have := isPreconnected_iff_preconnectedSpace.1 (hconn i).isPreconnected
    have := (hconn i).nonempty.to_subtype
    uniqueOfSubsingleton (ConnectedComponents.mk (Classical.arbitrary _))
  exact Nat.card_congr ((ConnectedComponents.equivOfIsClopen hclopen hdisj hunion).trans
    (Equiv.sigmaUnique ι _))

end TauCeti

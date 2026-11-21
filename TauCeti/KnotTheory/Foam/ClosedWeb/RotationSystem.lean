/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Foam.ClosedWeb.Basic
public import TauCeti.Combinatorics.RibbonGraph.Basic
public import TauCeti.GroupTheory.Perm.OrbitCount.Basic
import TauCeti.GroupTheory.Perm.Fin
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.GroupTheory.Perm.SumCongr
import TauCeti.Combinatorics.Enumerative.PerfectMatching

/-!
# The compatible rotation system of a closed web

The surface rotation of an oriented trivalent web is its stored cyclic successor at a
split, and its inverse at a merge. This distinction matters: using the stored successor
at both ends of the theta web gives a different surface.

`ClosedWeb.ribbonGraph` subdivides each interval edge at a white bivalent vertex. Original
vertices are black. Each vertex-free circle is represented by one auxiliary black vertex,
one white vertex and two edges. Thus circles remain separate connected components, rather
than disappearing from the rotation system. The two sorts of edges of this bipartite graph
are the ends of intervals and the two halves of each auxiliary circle.

This is the rotation-system conversion used by Goertz–Marino–Wedrich, *Monoidal 2-categories
from foam evaluation*, arXiv:2602.11120v1, Construction 4.6. The bipartite subdivision uses the
usual ribbon-graph convention of Lando–Zvonkin, *Graphs on Surfaces and Their Applications*,
Chapter 1. No planarity condition is imposed here.
-/

public section

namespace TauCeti.ClosedWeb

open Equiv

universe u v

variable (W : ClosedWeb.{u})

/-- Surface rotation: cyclic successor at splits and cyclic predecessor at merges. -/
def rotation : Perm W.End :=
  W.ends.symm.trans ((Equiv.prodCongrRight fun v : W.Vertex =>
    if W.IsMerge v then (finRotate 3).symm else finRotate 3).trans W.ends)

/-- The rotation in local slots, with the merge inversion explicit. -/
@[simp] theorem rotation_ends (v : W.Vertex) (i : Fin 3) :
    W.rotation (W.ends (v, i)) =
      W.ends (v, if W.IsMerge v then (finRotate 3).symm i else finRotate 3 i) := by
  by_cases h : W.IsMerge v <;> simp [rotation, Equiv.prodCongrRight, h]

/-- The inverse rotation in local slots: successor at merges, predecessor at splits. -/
@[simp] theorem rotation_symm_ends (v : W.Vertex) (i : Fin 3) :
    W.rotation.symm (W.ends (v, i)) =
      W.ends (v, if W.IsMerge v then finRotate 3 i else (finRotate 3).symm i) := by
  apply W.rotation.injective
  by_cases h : W.IsMerge v <;> simp [h]

/-- Surface rotation preserves the incident vertex. -/
@[simp] theorem incident_rotation (d : W.End) :
    W.incident (W.rotation d) = W.incident d := by
  obtain ⟨⟨v, i⟩, rfl⟩ := W.ends.surjective d
  simp

/-- Inverse surface rotation also preserves the incident vertex. -/
@[simp] theorem incident_rotation_symm (d : W.End) :
    W.incident (W.rotation.symm d) = W.incident d := by
  simpa using (W.incident_rotation (W.rotation.symm d)).symm

/-- At a split, the surface rotation is the stored cyclic successor. -/
theorem rotation_eq_cyclicSucc_of_isSplit (d : W.End) (h : W.IsSplit (W.incident d)) :
    W.rotation d = W.cyclicSucc d := by
  obtain ⟨⟨v, i⟩, rfl⟩ := W.ends.surjective d
  rw [incident_ends] at h
  simp [(W.not_isMerge_iff v).mpr h]

/-- At a merge, the surface rotation is the stored cyclic predecessor. -/
theorem rotation_eq_cyclicSucc_symm_of_isMerge (d : W.End) (h : W.IsMerge (W.incident d)) :
    W.rotation d = W.cyclicSucc.symm d := by
  obtain ⟨⟨v, i⟩, rfl⟩ := W.ends.surjective d
  rw [incident_ends] at h
  simp [h]

/-- Disjoint union preserves the effective rotation on the left component. -/
@[simp] theorem rotation_sum_apply_inl (V : ClosedWeb.{v}) (e : W.Edge) (b : Bool) :
    (W.sum V).rotation ((Sum.inl e, b) : (W.Edge ⊕ V.Edge) × Bool) =
      (Sum.inl (W.rotation (e, b)).1, (W.rotation (e, b)).2) := by
  obtain ⟨⟨v, i⟩, h⟩ := W.ends.surjective (e, b)
  have hr := (W.sum V).rotation_ends (Sum.inl v) i
  simp only [isMerge_sum_inl] at hr
  rwa [sum_ends_apply_inl, sum_ends_apply_inl, ← W.rotation_ends, h] at hr

/-- Disjoint union preserves the effective rotation on the right component. -/
@[simp] theorem rotation_sum_apply_inr (V : ClosedWeb.{v}) (e : V.Edge) (b : Bool) :
    (W.sum V).rotation ((Sum.inr e, b) : (W.Edge ⊕ V.Edge) × Bool) =
      (Sum.inr (V.rotation (e, b)).1, (V.rotation (e, b)).2) := by
  obtain ⟨⟨v, i⟩, h⟩ := V.ends.surjective (e, b)
  have hr := (W.sum V).rotation_ends (Sum.inr v) i
  simp only [isMerge_sum_inr] at hr
  rwa [sum_ends_apply_inr, sum_ends_apply_inr, ← V.rotation_ends, h] at hr

/-- Mirroring replaces effective rotation by its inverse. -/
@[simp] theorem rotation_mirror : W.mirror.rotation = W.rotation.symm := by
  apply Equiv.ext
  intro d
  obtain ⟨⟨v, i⟩, rfl⟩ := W.mirror.ends.surjective d
  rw [W.mirror.rotation_ends, mirror_ends_apply, mirror_ends_apply, W.rotation_symm_ends]
  by_cases h : W.IsMerge v <;> simp only [isMerge_mirror, h, ite_true, ite_false] <;>
    apply congrArg (fun j => W.ends (v, j)) <;> fin_cases i <;> decide

/-- Reversal exchanges the two ends of each edge and inverts effective rotation. -/
@[simp] theorem rotation_reverse_apply (d : W.End) :
    W.reverse.rotation d =
      ((W.rotation.symm (d.1, !d.2)).1, !(W.rotation.symm (d.1, !d.2)).2) := by
  obtain ⟨⟨v, i⟩, rfl⟩ := W.reverse.ends.surjective d
  rw [W.reverse.rotation_ends, reverse_ends_apply, reverse_ends_apply]
  have hs : W.IsSplit v ↔ ¬W.IsMerge v := (W.not_isMerge_iff v).symm
  by_cases h : W.IsMerge v <;> simp [hs, h]

/-- In the theta web the new slot is the new edge, and the vertex determines the orientation
of its end: on edge zero the end label is the vertex itself, and otherwise it is flipped. -/
@[simp] theorem rotation_theta_apply (d : theta.End) :
    theta.rotation d =
      let v := theta.incident d
      let i := if v then finRotate 3 d.1 else (finRotate 3).symm d.1
      (i, if i = 0 then v else !v) := by
  obtain ⟨⟨v, i⟩, rfl⟩ := theta.ends.surjective d
  rw [theta.rotation_ends, incident_ends, theta_ends_apply, theta_ends_apply]
  cases v <;> simp

/-- All three ends at a vertex lie in one cycle of the surface rotation. -/
theorem sameCycle_rotation_ends (v : W.Vertex) (i j : Fin 3) :
    W.rotation.SameCycle (W.ends (v, i)) (W.ends (v, j)) := by
  by_cases h : W.IsMerge v
  · exact ((isCycleOn_finRotate.inv).2 (Set.mem_univ i) (Set.mem_univ j)).map
      (τ := W.rotation) (g := fun k => W.ends (v, k)) (fun k => by simp [h])
  · exact (isCycleOn_finRotate.2 (Set.mem_univ i) (Set.mem_univ j)).map
      (τ := W.rotation) (g := fun k => W.ends (v, k)) (fun k => by simp [h])

/-- The vertex fibres are exactly the cycles of the effective surface rotation. -/
theorem sameCycle_rotation_iff (d e : W.End) :
    W.rotation.SameCycle d e ↔ W.incident d = W.incident e := by
  constructor
  · intro h
    exact h.apply_eq_of_apply_eq W.incident_rotation
  · obtain ⟨⟨v, i⟩, rfl⟩ := W.ends.surjective d
    obtain ⟨⟨w, j⟩, rfl⟩ := W.ends.surjective e
    simp only [incident_ends]
    rintro rfl
    exact W.sameCycle_rotation_ends v i j

/-- Each vertex fibre carries exactly one cycle. -/
theorem isCycleOn_rotation (v : W.Vertex) :
    W.rotation.IsCycleOn (W.incident ⁻¹' {v}) :=
  W.rotation.isCycleOn_preimage_of_sameCycle_iff W.sameCycle_rotation_iff v

/-- Edges of the bipartite subdivision: one per end of an interval edge, and two halves
per vertex-free circle. -/
abbrev RibbonEdge := W.End ⊕ (W.Circle × Bool)

/-- Black vertices are original vertices or auxiliary circle vertices. -/
def ribbonBlackEnd : W.RibbonEdge → W.Vertex ⊕ W.Circle
  | .inl d => .inl (W.incident d)
  | .inr d => .inr d.1

/-- White vertices are interval-edge midpoints or auxiliary circle midpoints. -/
def ribbonWhiteEnd : W.RibbonEdge → W.Edge ⊕ W.Circle
  | .inl d => .inl d.1
  | .inr d => .inr d.1

@[simp] theorem ribbonBlackEnd_inl (d : W.End) :
    W.ribbonBlackEnd (.inl d) = .inl (W.incident d) := (rfl)

@[simp] theorem ribbonBlackEnd_inr (c : W.Circle) (b : Bool) :
    W.ribbonBlackEnd (.inr (c, b)) = .inr c := (rfl)

@[simp] theorem ribbonWhiteEnd_inl (e : W.Edge) (b : Bool) :
    W.ribbonWhiteEnd (.inl (e, b)) = .inl e := (rfl)

@[simp] theorem ribbonWhiteEnd_inr (c : W.Circle) (b : Bool) :
    W.ribbonWhiteEnd (.inr (c, b)) = .inr c := (rfl)

/-- Rotation about black vertices in the subdivision. -/
def ribbonRotB : Perm W.RibbonEdge :=
  Equiv.sumCongr W.rotation (Equiv.prodCongr (Equiv.refl _) Equiv.boolNot)

/-- Rotation about white bivalent vertices exchanges the two edge ends. -/
def ribbonRotW : Perm W.RibbonEdge :=
  Equiv.sumCongr (Equiv.prodCongr (Equiv.refl _) Equiv.boolNot)
    (Equiv.prodCongr (Equiv.refl _) Equiv.boolNot)

@[simp] theorem ribbonRotB_inl (d : W.End) :
    W.ribbonRotB (.inl d) = .inl (W.rotation d) := (rfl)

@[simp] theorem ribbonRotB_inr (c : W.Circle) (b : Bool) :
    W.ribbonRotB (.inr (c, b)) = .inr (c, !b) := (rfl)

@[simp] theorem ribbonRotW_inl (e : W.Edge) (b : Bool) :
    W.ribbonRotW (.inl (e, b)) = .inl (e, !b) := (rfl)

@[simp] theorem ribbonRotW_inr (c : W.Circle) (b : Bool) :
    W.ribbonRotW (.inr (c, b)) = .inr (c, !b) := (rfl)

@[simp] theorem ribbonBlackEnd_rotB (d : W.RibbonEdge) :
    W.ribbonBlackEnd (W.ribbonRotB d) = W.ribbonBlackEnd d := by
  rcases d with d | ⟨c, b⟩ <;> simp [ribbonBlackEnd]

@[simp] theorem ribbonWhiteEnd_rotW (d : W.RibbonEdge) :
    W.ribbonWhiteEnd (W.ribbonRotW d) = W.ribbonWhiteEnd d := by
  rcases d with ⟨e, b⟩ | ⟨c, b⟩ <;> simp [ribbonWhiteEnd]

private theorem sameCycle_prodCongr_boolNot_iff {α : Type*} (a a' : α) (b b' : Bool) :
    Perm.SameCycle (Equiv.prodCongr (Equiv.refl α) Equiv.boolNot) (a, b) (a', b') ↔ a = a' := by
  have h : Function.Involutive (Equiv.prodCongr (Equiv.refl α) Equiv.boolNot : Perm _) := by
    rintro ⟨x, p⟩
    simp
  rw [h.sameCycle_iff]
  cases b <;> cases b' <;> simp

/-- Two subdivision edges lie in the same black rotation cycle exactly when they have
the same black vertex. -/
theorem sameCycle_ribbonRotB_iff (d e : W.RibbonEdge) :
    W.ribbonRotB.SameCycle d e ↔ W.ribbonBlackEnd d = W.ribbonBlackEnd e := by
  rcases d with d | ⟨c, b⟩ <;> rcases e with e | ⟨c', b'⟩
  · simp [ribbonRotB, W.sameCycle_rotation_iff]
  · simp [ribbonRotB]
  · simp [ribbonRotB, Perm.sameCycle_comm (x := Sum.inr (c, b))]
  · simp [ribbonRotB, sameCycle_prodCongr_boolNot_iff]

/-- Two subdivision edges lie in the same white rotation cycle exactly when they have
the same white vertex. -/
theorem sameCycle_ribbonRotW_iff (d e : W.RibbonEdge) :
    W.ribbonRotW.SameCycle d e ↔ W.ribbonWhiteEnd d = W.ribbonWhiteEnd e := by
  rcases d with ⟨e₁, b₁⟩ | ⟨c₁, b₁⟩ <;> rcases e with ⟨e₂, b₂⟩ | ⟨c₂, b₂⟩
  · simp [ribbonRotW, sameCycle_prodCongr_boolNot_iff]
  · simp [ribbonRotW]
  · simp [ribbonRotW, Perm.sameCycle_comm (x := Sum.inr (c₁, b₁))]
  · simp [ribbonRotW, sameCycle_prodCongr_boolNot_iff]

/-- Every black incidence fibre of the subdivision is a single cycle. -/
theorem isCycleOn_ribbonRotB (v : W.Vertex ⊕ W.Circle) :
    W.ribbonRotB.IsCycleOn (W.ribbonBlackEnd ⁻¹' {v}) :=
  W.ribbonRotB.isCycleOn_preimage_of_sameCycle_iff W.sameCycle_ribbonRotB_iff v

/-- Every white incidence fibre of the subdivision is a single cycle. -/
theorem isCycleOn_ribbonRotW (v : W.Edge ⊕ W.Circle) :
    W.ribbonRotW.IsCycleOn (W.ribbonWhiteEnd ⁻¹' {v}) :=
  W.ribbonRotW.isCycleOn_preimage_of_sameCycle_iff W.sameCycle_ribbonRotW_iff v

/-- The bipartite ribbon graph of the compatible rotation system, with every interval
subdivided once and every vertex-free circle retained as a two-edge component. -/
-- Reducible so the finite incidence carriers compute, just as for ClosedWeb.sum.
noncomputable abbrev ribbonGraph : BipartiteRibbonGraph where
  E := W.RibbonEdge
  B := W.Vertex ⊕ W.Circle
  W := W.Edge ⊕ W.Circle
  fintypeE := Fintype.ofFinite _
  fintypeB := Fintype.ofFinite _
  fintypeW := Fintype.ofFinite _
  decidableEqE := Classical.decEq _
  decidableEqB := Classical.decEq _
  decidableEqW := Classical.decEq _
  blackEnd := W.ribbonBlackEnd
  whiteEnd := W.ribbonWhiteEnd
  rotB := W.ribbonRotB
  rotW := W.ribbonRotW
  blackEnd_surjective := by
    rintro (v | c)
    · exact ⟨.inl (W.ends (v, 0)), by simp [ribbonBlackEnd]⟩
    · exact ⟨.inr (c, false), rfl⟩
  whiteEnd_surjective := by
    rintro (e | c)
    · exact ⟨.inl (e, false), rfl⟩
    · exact ⟨.inr (c, false), rfl⟩
  isCycleOn_rotB := W.isCycleOn_ribbonRotB
  isCycleOn_rotW := W.isCycleOn_ribbonRotW

@[simp] theorem blackEnd_ribbonGraph (d : W.RibbonEdge) :
    W.ribbonGraph.blackEnd d = W.ribbonBlackEnd d := (rfl)

@[simp] theorem whiteEnd_ribbonGraph (d : W.RibbonEdge) :
    W.ribbonGraph.whiteEnd d = W.ribbonWhiteEnd d := (rfl)

@[simp] theorem rotB_ribbonGraph : W.ribbonGraph.rotB = W.ribbonRotB := (rfl)

@[simp] theorem rotW_ribbonGraph : W.ribbonGraph.rotW = W.ribbonRotW := (rfl)

/-- On interval ends the face permutation is the inverse of rotation followed by edge exchange.
On each auxiliary circle it fixes both edges. -/
@[simp] theorem facePerm_ribbonGraph :
    W.ribbonGraph.facePerm =
      Equiv.sumCongr ((Equiv.prodCongr (Equiv.refl _) Equiv.boolNot) * W.rotation)⁻¹ 1 := by
  let τ : Perm (W.Circle × Bool) := Equiv.prodCongr (Equiv.refl _) Equiv.boolNot
  have h : τ * τ = 1 := by
    apply Equiv.ext
    rintro ⟨c, b⟩
    simp [τ, Perm.mul_apply]
  rw [BipartiteRibbonGraph.facePerm_def, rotW_ribbonGraph, rotB_ribbonGraph,
    ribbonRotW, ribbonRotB, Perm.sumCongr_mul]
  change (Perm.sumCongr _ (τ * τ))⁻¹ = _
  rw [h, Perm.sumCongr_inv, inv_one]

/-- The number of faces of the subdivided web. The first term counts the orbits of
edge exchange followed by effective rotation; each vertex-free circle adds two faces. -/
theorem faceCount_ribbonGraph :
    W.ribbonGraph.faceCount =
      orbitCount (W.rotation * Equiv.prodCongr (Equiv.refl _) Equiv.boolNot) +
        2 * Nat.card W.Circle := by
  classical
  let : Fintype W.ribbonGraph.Face := BipartiteRibbonGraph.instFintypeFace _
  calc
    W.ribbonGraph.faceCount = orbitCount W.ribbonGraph.facePerm := by
      rw [BipartiteRibbonGraph.faceCount_def, ← Nat.card_eq_fintype_card, orbitCount_def]
    _ = _ := by
      simp only [facePerm_ribbonGraph, Perm.orbitCount_sumCongr, Perm.orbitCount_inv,
        orbitCount_one, Nat.card_prod]
      rw [orbitCount_mul_comm (Equiv.prodCongr (Equiv.refl _) Equiv.boolNot)]
      simp [Nat.mul_comm]

/-- Subdivision does not change the Euler count `V - E + F`; the two faces of each
vertex-free circle are included in the native ribbon-graph face count. -/
theorem eulerChar_ribbonGraph :
    W.ribbonGraph.eulerChar =
      (Nat.card W.Vertex : ℤ) - Nat.card W.Edge + W.ribbonGraph.faceCount := by
  have hb : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  rw [BipartiteRibbonGraph.eulerChar_def]
  simp only [← Nat.card_eq_fintype_card, Nat.card_sum, Nat.card_prod, hb]
  push_cast
  ring

/-- The surface Euler count directly in terms of the original web and its effective
rotation, including the contribution of vertex-free circles. -/
theorem eulerChar_ribbonGraph_eq_orbitCount :
    W.ribbonGraph.eulerChar = (Nat.card W.Vertex : ℤ) - Nat.card W.Edge +
      orbitCount (W.rotation * Equiv.prodCongr (Equiv.refl _) Equiv.boolNot) +
        2 * Nat.card W.Circle := by
  rw [eulerChar_ribbonGraph, faceCount_ribbonGraph]
  push_cast
  ring

/-- A union of vertex-free circles has two faces per circle in the auxiliary subdivision. -/
@[simp] theorem faceCount_ribbonGraph_circles (C : Type u) [Finite C] :
    (circles C).ribbonGraph.faceCount = 2 * Nat.card C := by
  rw [faceCount_ribbonGraph, orbitCount_def, Nat.card_of_isEmpty]
  simp

/-- Every vertex-free circle contributes the Euler characteristic of a sphere. -/
@[simp] theorem eulerChar_ribbonGraph_circles (C : Type u) [Finite C] :
    (circles C).ribbonGraph.eulerChar = 2 * Nat.card C := by
  rw [eulerChar_ribbonGraph, faceCount_ribbonGraph_circles]
  simp

/-- The compatible theta rotation has three faces, not one. -/
@[simp] theorem faceCount_ribbonGraph_theta : theta.ribbonGraph.faceCount = 3 := by
  rw [faceCount_ribbonGraph]
  simp only [Nat.card_eq_fintype_card, Fintype.card_pempty, mul_zero, add_zero]
  have hm : IsPerfectMatching
      (theta.rotation * Equiv.prodCongr (Equiv.refl _) Equiv.boolNot) := by
    rw [isPerfectMatching_iff]
    simp only [rotation, isMerge_def]
    decide +kernel
  have hcard : Nat.card theta.End = 6 := by
    change Nat.card (Fin 3 × Bool) = 6
    norm_num [Nat.card_eq_fintype_card]
  have hc := hm.two_mul_orbitCount
  rw [hcard] at hc
  change orbitCount (theta.rotation * Equiv.prodCongr (Equiv.refl theta.Edge) Equiv.boolNot) = 3
  omega

/-- The theta web with its compatible rotation has Euler characteristic two. -/
@[simp] theorem eulerChar_ribbonGraph_theta : theta.ribbonGraph.eulerChar = 2 := by
  rw [eulerChar_ribbonGraph, faceCount_ribbonGraph_theta]
  norm_num

namespace Iso

variable {W : ClosedWeb.{u}} {V : ClosedWeb.{v}}

/-- Web isomorphisms intertwine the effective rotations as well as the stored ones. -/
@[simp] theorem map_rotation (f : W.Iso V) (e : W.Edge) (b : Bool) :
    V.rotation (f.edge e, b) =
      (f.edge (W.rotation (e, b)).1, (W.rotation (e, b)).2) := by
  obtain ⟨⟨v, i⟩, h⟩ := W.ends.surjective (e, b)
  have hv := V.rotation_ends (f.vertex v) i
  rw [f.map_ends (v, i), h] at hv
  simp only [f.isMerge_vertex] at hv
  rw [hv, ← h, W.rotation_ends]
  split_ifs
  · exact f.map_ends (v, (finRotate 3).symm i)
  · exact f.map_ends (v, finRotate 3 i)

/-- Web isomorphisms intertwine the inverse effective rotations. -/
@[simp] theorem map_rotation_symm (f : W.Iso V) (e : W.Edge) (b : Bool) :
    V.rotation.symm (f.edge e, b) =
      (f.edge (W.rotation.symm (e, b)).1, (W.rotation.symm (e, b)).2) := by
  apply V.rotation.injective
  simpa only [Equiv.apply_symm_apply, Prod.mk.eta] using
    (f.map_rotation (W.rotation.symm (e, b)).1 (W.rotation.symm (e, b)).2).symm

/-- A web isomorphism induces an isomorphism of the bipartite subdivisions,
including the auxiliary circle components. -/
noncomputable def ribbonGraph (f : W.Iso V) : W.ribbonGraph.Iso V.ribbonGraph where
  edge := Equiv.sumCongr (Equiv.prodCongr f.edge (Equiv.refl _))
    (Equiv.prodCongr f.circle (Equiv.refl _))
  black := Equiv.sumCongr f.vertex f.circle
  white := Equiv.sumCongr f.edge f.circle
  map_blackEnd d := by
    rcases d with ⟨e, b⟩ | ⟨c, b⟩ <;> simp [ribbonBlackEnd]
  map_whiteEnd d := by
    rcases d with ⟨e, b⟩ | ⟨c, b⟩ <;> simp [Equiv.sumCongr_apply, Equiv.prodCongr_apply]
  map_rotB d := by
    rcases d with ⟨e, b⟩ | ⟨c, b⟩ <;>
      simp [Equiv.sumCongr_apply, Equiv.prodCongr_apply, Prod.map, map_rotation]
  map_rotW d := by
    rcases d with ⟨e, b⟩ | ⟨c, b⟩ <;> simp [Equiv.sumCongr_apply, Equiv.prodCongr_apply]

@[simp] theorem ribbonGraph_edge (f : W.Iso V) :
    f.ribbonGraph.edge = Equiv.sumCongr (Equiv.prodCongr f.edge (Equiv.refl _))
      (Equiv.prodCongr f.circle (Equiv.refl _)) := (rfl)

@[simp] theorem ribbonGraph_black (f : W.Iso V) :
    f.ribbonGraph.black = Equiv.sumCongr f.vertex f.circle := (rfl)

@[simp] theorem ribbonGraph_white (f : W.Iso V) :
    f.ribbonGraph.white = Equiv.sumCongr f.edge f.circle := (rfl)

end Iso

/-- Relabelling transports the effective rotation along the equivalence of edge ends. -/
@[simp] theorem rotation_relabel_apply {V E C : Type v}
    (v : W.Vertex ≃ V) (e : W.Edge ≃ E) (c : W.Circle ≃ C) (d : E × Bool) :
    (W.relabel v e c).rotation d =
      (e (W.rotation (e.symm d.1, d.2)).1, (W.rotation (e.symm d.1, d.2)).2) := by
  simpa using (W.relabelIso v e c).map_rotation (e.symm d.1) d.2

end TauCeti.ClosedWeb

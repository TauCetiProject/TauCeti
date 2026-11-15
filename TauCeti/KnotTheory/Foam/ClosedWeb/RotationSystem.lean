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
theorem rotation_eq_cyclicSucc_of_isSplit {v : W.Vertex} (h : W.IsSplit v) (i : Fin 3) :
    W.rotation (W.ends (v, i)) = W.cyclicSucc (W.ends (v, i)) := by
  have hn := (W.not_isMerge_iff v).mpr h
  simp [hn]

/-- At a merge, the surface rotation is the stored cyclic predecessor. -/
theorem rotation_eq_cyclicSucc_symm_of_isMerge {v : W.Vertex} (h : W.IsMerge v)
    (i : Fin 3) :
    W.rotation (W.ends (v, i)) = W.cyclicSucc.symm (W.ends (v, i)) := by
  simp [h]

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
    W.rotation.IsCycleOn (W.incident ⁻¹' {v}) := by
  refine ⟨⟨?_, W.rotation.injective.injOn, ?_⟩, ?_⟩
  · intro d hd
    simpa using hd
  · intro d hd
    exact ⟨W.rotation.symm d, by simpa using hd, W.rotation.apply_symm_apply d⟩
  · intro d hd e he
    exact (W.sameCycle_rotation_iff d e).mpr (hd.trans he.symm)

/-- The ends of the bipartite subdivision, including two halves for each vertex-free circle. -/
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

private theorem sameCycle_ribbonRotB_circle (c : W.Circle) (b b' : Bool) :
    W.ribbonRotB.SameCycle (.inr (c, b)) (.inr (c, b')) := by
  have h := (Perm.SameCycle.refl W.ribbonRotB (.inr (c, b))).apply_right
  cases b <;> cases b' <;> first | exact Perm.SameCycle.refl _ _ | simpa using h

private theorem sameCycle_ribbonRotW_interval (e : W.Edge) (b b' : Bool) :
    W.ribbonRotW.SameCycle (.inl (e, b)) (.inl (e, b')) := by
  have h := (Perm.SameCycle.refl W.ribbonRotW (.inl (e, b))).apply_right
  cases b <;> cases b' <;> first | exact Perm.SameCycle.refl _ _ | simpa using h

private theorem sameCycle_ribbonRotW_circle (c : W.Circle) (b b' : Bool) :
    W.ribbonRotW.SameCycle (.inr (c, b)) (.inr (c, b')) := by
  have h := (Perm.SameCycle.refl W.ribbonRotW (.inr (c, b))).apply_right
  cases b <;> cases b' <;> first | exact Perm.SameCycle.refl _ _ | simpa using h

/-- Every black incidence fibre of the subdivision is a single cycle. -/
theorem isCycleOn_ribbonRotB (v : W.Vertex ⊕ W.Circle) :
    W.ribbonRotB.IsCycleOn (W.ribbonBlackEnd ⁻¹' {v}) := by
  refine ⟨⟨?_, W.ribbonRotB.injective.injOn, ?_⟩, ?_⟩
  · intro d hd
    simpa using hd
  · intro d hd
    refine ⟨W.ribbonRotB.symm d, ?_, W.ribbonRotB.apply_symm_apply d⟩
    have h := W.ribbonBlackEnd_rotB (W.ribbonRotB.symm d)
    rw [W.ribbonRotB.apply_symm_apply] at h
    exact h.symm.trans hd
  · intro d hd e he
    have h : W.ribbonBlackEnd d = W.ribbonBlackEnd e := hd.trans he.symm
    cases d with
    | inl d =>
      cases e with
      | inl e =>
        exact ((W.sameCycle_rotation_iff d e).mpr (Sum.inl.inj h)).map
          (fun _ => rfl)
      | inr e => simp [ribbonBlackEnd] at h
    | inr d =>
      cases e with
      | inl e => simp [ribbonBlackEnd] at h
      | inr e =>
        obtain ⟨c, b⟩ := d
        obtain ⟨c', b'⟩ := e
        have hc : c = c' := Sum.inr.inj h
        subst c'
        exact W.sameCycle_ribbonRotB_circle c b b'

/-- Every white incidence fibre of the subdivision is a single cycle. -/
theorem isCycleOn_ribbonRotW (v : W.Edge ⊕ W.Circle) :
    W.ribbonRotW.IsCycleOn (W.ribbonWhiteEnd ⁻¹' {v}) := by
  refine ⟨⟨?_, W.ribbonRotW.injective.injOn, ?_⟩, ?_⟩
  · intro d hd
    simpa using hd
  · intro d hd
    refine ⟨W.ribbonRotW.symm d, ?_, W.ribbonRotW.apply_symm_apply d⟩
    have h := W.ribbonWhiteEnd_rotW (W.ribbonRotW.symm d)
    rw [W.ribbonRotW.apply_symm_apply] at h
    exact h.symm.trans hd
  · intro d hd e he
    have h : W.ribbonWhiteEnd d = W.ribbonWhiteEnd e := hd.trans he.symm
    cases d with
    | inl d =>
      cases e with
      | inl e =>
        obtain ⟨a, b⟩ := d
        obtain ⟨a', b'⟩ := e
        have ha : a = a' := Sum.inl.inj h
        subst a'
        exact W.sameCycle_ribbonRotW_interval a b b'
      | inr e => simp [ribbonWhiteEnd] at h
    | inr d =>
      cases e with
      | inl e => simp [ribbonWhiteEnd] at h
      | inr e =>
        obtain ⟨c, b⟩ := d
        obtain ⟨c', b'⟩ := e
        have hc : c = c' := Sum.inr.inj h
        subst c'
        exact W.sameCycle_ribbonRotW_circle c b b'

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

@[simp] theorem ribbonGraph_blackEnd (d : W.RibbonEdge) :
    W.ribbonGraph.blackEnd d = W.ribbonBlackEnd d := (rfl)

@[simp] theorem ribbonGraph_whiteEnd (d : W.RibbonEdge) :
    W.ribbonGraph.whiteEnd d = W.ribbonWhiteEnd d := (rfl)

@[simp] theorem ribbonGraph_rotB : W.ribbonGraph.rotB = W.ribbonRotB := (rfl)

@[simp] theorem ribbonGraph_rotW : W.ribbonGraph.rotW = W.ribbonRotW := (rfl)

/-- The number of faces of the subdivided web. The first term counts the orbits of
edge exchange followed by effective rotation; each vertex-free circle adds two faces. -/
theorem faceCount_ribbonGraph :
    W.ribbonGraph.faceCount =
      orbitCount (W.rotation * Equiv.prodCongr (Equiv.refl _) Equiv.boolNot) +
        2 * Nat.card W.Circle := by
  classical
  let : Fintype W.ribbonGraph.Face := BipartiteRibbonGraph.instFintypeFace _
  have h : W.ribbonRotW * W.ribbonRotB =
      Equiv.sumCongr ((Equiv.prodCongr (Equiv.refl _) Equiv.boolNot) * W.rotation)
        (1 : Perm (W.Circle × Bool)) := by
    ext d
    rcases d with d | ⟨c, b⟩
    · obtain ⟨_, _⟩ := W.rotation d
      rfl
    · simp [Perm.mul_apply]
  rw [BipartiteRibbonGraph.faceCount_def, ← Nat.card_eq_fintype_card, ← orbitCount_def,
    BipartiteRibbonGraph.facePerm_def, ribbonGraph_rotW, ribbonGraph_rotB,
    Perm.orbitCount_inv, h, Perm.orbitCount_sumCongr, orbitCount_one, Nat.card_prod,
    Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, orbitCount_mul_comm]
  omega

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
    exact (by norm_num [Nat.card_eq_fintype_card] : Nat.card (Fin 3 × Bool) = 6)
  have hc := hm.two_mul_orbitCount
  rw [hcard] at hc
  have hr : orbitCount
      (theta.rotation * Equiv.prodCongr (Equiv.refl theta.Edge) Equiv.boolNot) = 3 := by omega
  exact hr

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

/-- A boundary-incidence isomorphism of webs induces an isomorphism of the bipartite
subdivisions, including the auxiliary circle components. -/
noncomputable def ribbonGraph (f : W.Iso V) : W.ribbonGraph.Iso V.ribbonGraph where
  edge := Equiv.sumCongr (Equiv.prodCongr f.edge (Equiv.refl _))
    (Equiv.prodCongr f.circle (Equiv.refl _))
  black := Equiv.sumCongr f.vertex f.circle
  white := Equiv.sumCongr f.edge f.circle
  map_blackEnd d := by
    rcases d with ⟨e, b⟩ | ⟨c, b⟩ <;> simp [ribbonBlackEnd]
  map_whiteEnd d := by
    rcases d with ⟨e, b⟩ | ⟨c, b⟩ <;> rfl
  map_rotB d := by
    rcases d with ⟨e, b⟩ | ⟨c, b⟩
    · simp [Equiv.sumCongr_apply, Equiv.prodCongr_apply, Prod.map, map_rotation]
    · rfl
  map_rotW d := by
    rcases d with ⟨e, b⟩ | ⟨c, b⟩ <;> rfl

@[simp] theorem ribbonGraph_edge (f : W.Iso V) :
    f.ribbonGraph.edge = Equiv.sumCongr (Equiv.prodCongr f.edge (Equiv.refl _))
      (Equiv.prodCongr f.circle (Equiv.refl _)) := (rfl)

@[simp] theorem ribbonGraph_black (f : W.Iso V) :
    f.ribbonGraph.black = Equiv.sumCongr f.vertex f.circle := (rfl)

@[simp] theorem ribbonGraph_white (f : W.Iso V) :
    f.ribbonGraph.white = Equiv.sumCongr f.edge f.circle := (rfl)

end Iso

end TauCeti.ClosedWeb

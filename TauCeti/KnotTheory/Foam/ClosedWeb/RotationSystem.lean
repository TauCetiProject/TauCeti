/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Foam.ClosedWeb.Planar
import TauCeti.GroupTheory.Perm.ProdCongr
import TauCeti.GroupTheory.Perm.SumCongr

/-!
# The compatible ribbon graph of a closed web, including circles

`ClosedWeb.toRibbonGraph` handles the interval part of a web using the effective rotation:
cyclic successor at splits and cyclic predecessor at merges. `ClosedWeb.ribbonGraph`
adds one black vertex, one white vertex and two edges for each vertex-free circle.
The same transposition rotates the two halves at either vertex, so their product is the
identity. Each circle thus adds two faces and increases the Euler characteristic by two.
A web isomorphism induces an isomorphism of these full subdivisions.

The effective rotation follows Goertz–Marino–Wedrich, *Monoidal 2-categories from foam
evaluation*, arXiv:2602.11120v1, Construction 4.6. The bipartite subdivision uses the
usual ribbon-graph convention of Lando–Zvonkin, *Graphs on Surfaces and Their Applications*,
Chapter 1. No planarity condition is imposed here.
-/

public section

namespace TauCeti.ClosedWeb

open Equiv Equiv.Perm

universe u v

variable (W : ClosedWeb.{u})

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

/-- The vertex fibres are exactly the cycles of the effective surface rotation. -/
theorem sameCycle_rotation_iff (d e : W.End) :
    W.rotation.SameCycle d e ↔ W.incident d = W.incident e := by
  constructor
  · intro h
    exact h.apply_eq_of_apply_eq W.incident_rotation
  · intro h
    exact (W.isCycleOn_rotation (W.incident e)).2 h rfl

/-! ### Subdivision including vertex-free circles -/

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

@[simp] theorem ribbonWhiteEnd_inl (d : W.End) :
    W.ribbonWhiteEnd (.inl d) = .inl d.1 := (rfl)

@[simp] theorem ribbonWhiteEnd_inr (c : W.Circle) (b : Bool) :
    W.ribbonWhiteEnd (.inr (c, b)) = .inr c := (rfl)

/-- Exchange the two halves of each vertex-free circle. -/
def circleSwap : Perm (W.Circle × Bool) := prodCongrRight fun _ => boolNot

@[simp] theorem circleSwap_apply (c : W.Circle) (b : Bool) :
    W.circleSwap (c, b) = (c, !b) := (rfl)

private theorem isCycleOn_circleSwap (c : W.Circle) :
    (circleSwap W).IsCycleOn (Prod.fst ⁻¹' {c}) := by
  have h : boolNot.IsCycleOn Set.univ := by
    refine ⟨boolNot.bijOn (by simp), fun b _ b' _ => ?_⟩
    cases b <;> cases b' <;> first | exact Perm.SameCycle.refl _ _ | exact ⟨1, by decide⟩
  change IsCycleOn (prodCongrRight fun (_ : W.Circle) => boolNot) _
  convert IsCycleOn.prodCongrRight (τ := fun (_ : W.Circle) => boolNot) (a := c) h using 1
  ext ⟨c', b⟩
  simp

/-- The bipartite ribbon graph of the compatible rotation system, with every interval
subdivided once and every vertex-free circle retained as a two-edge component. -/
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
  rotB := Equiv.sumCongr W.rotation (circleSwap W)
  rotW := Equiv.sumCongr W.endSwap (circleSwap W)
  blackEnd_surjective := by
    rintro (v | c)
    · exact ⟨.inl (W.ends (v, 0)), by simp⟩
    · exact ⟨.inr (c, false), rfl⟩
  whiteEnd_surjective := by
    rintro (e | c)
    · exact ⟨.inl (e, false), rfl⟩
    · exact ⟨.inr (c, false), rfl⟩
  isCycleOn_rotB := by
    rintro (v | c)
    · convert (W.isCycleOn_rotation v).sumCongr_inl (circleSwap W) using 2
      ext d : 1
      rcases d with d | ⟨d, b⟩ <;> simp
    · convert (isCycleOn_circleSwap W c).sumCongr_inr W.rotation using 2
      ext d : 1
      rcases d with d | ⟨d, b⟩ <;> simp
  isCycleOn_rotW := by
    rintro (e | c)
    · convert (W.isCycleOn_endSwap e).sumCongr_inl (circleSwap W) using 2
      ext d : 1
      rcases d with d | ⟨d, b⟩ <;> simp
    · convert (isCycleOn_circleSwap W c).sumCongr_inr W.endSwap using 2
      ext d : 1
      rcases d with d | ⟨d, b⟩ <;> simp

/-- Face traversal on the interval summand is its native ribbon-graph traversal; on the
circle summand both edges are fixed. -/
@[simp] theorem facePerm_ribbonGraph :
    W.ribbonGraph.facePerm = Equiv.sumCongr (W.endSwap * W.rotation)⁻¹ 1 := by
  have h : circleSwap W * circleSwap W = 1 := by
    apply Equiv.ext
    rintro ⟨c, b⟩
    simp [Perm.mul_apply]
  change (Perm.sumCongr W.endSwap (circleSwap W) * Perm.sumCongr W.rotation (circleSwap W))⁻¹ = _
  rw [Perm.sumCongr_mul, h, Perm.sumCongr_inv, inv_one]

/-- The full subdivision has the interval faces and two more faces per circle. -/
theorem faceCount_ribbonGraph :
    W.ribbonGraph.faceCount = W.faceCount + 2 * Nat.card W.Circle := by
  let : Fintype W.ribbonGraph.Face := BipartiteRibbonGraph.instFintypeFace _
  change Fintype.card W.ribbonGraph.Face = _
  rw [← Nat.card_eq_fintype_card]
  rw [← orbitCount_def, facePerm_ribbonGraph, Perm.orbitCount_sumCongr, orbitCount_inv,
    orbitCount_mul_comm, ← facePerm_def, ← faceCount_def, orbitCount_one, Nat.card_prod]
  simp [Nat.card_eq_fintype_card, Nat.mul_comm]

/-- The full subdivision adds two to the interval Euler characteristic per circle. -/
theorem eulerChar_ribbonGraph :
    W.ribbonGraph.eulerChar = W.eulerChar + 2 * Nat.card W.Circle := by
  have hb : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  rw [BipartiteRibbonGraph.eulerChar_def, faceCount_ribbonGraph, eulerChar_def]
  simp only [← Nat.card_eq_fintype_card, Nat.card_sum, Nat.card_prod, hb]
  push_cast
  ring

/-- A union of vertex-free circles has two faces per circle in the auxiliary subdivision. -/
@[simp] theorem faceCount_ribbonGraph_circles (C : Type u) [Finite C] :
    (circles C).ribbonGraph.faceCount = 2 * Nat.card C := by
  rw [faceCount_ribbonGraph, faceCount_def, orbitCount_def, Nat.card_of_isEmpty]
  simp

/-- Every vertex-free circle contributes the Euler characteristic of a sphere. -/
@[simp] theorem eulerChar_ribbonGraph_circles (C : Type u) [Finite C] :
    (circles C).ribbonGraph.eulerChar = 2 * Nat.card C := by
  rw [eulerChar_ribbonGraph, eulerChar_def, faceCount_def, orbitCount_def, Nat.card_of_isEmpty]
  simp

/-- The compatible theta rotation has three faces. -/
@[simp] theorem faceCount_ribbonGraph_theta : theta.ribbonGraph.faceCount = 3 := by
  rw [faceCount_ribbonGraph, faceCount_theta]
  simp

/-- The theta web with its compatible rotation has Euler characteristic two. -/
@[simp] theorem eulerChar_ribbonGraph_theta : theta.ribbonGraph.eulerChar = 2 := by
  rw [eulerChar_ribbonGraph, eulerChar_def, faceCount_theta]
  norm_num

namespace Iso

variable {W : ClosedWeb.{u}} {V : ClosedWeb.{v}}

/-- Web isomorphisms intertwine the inverse effective rotations. -/
@[simp] theorem map_rotation_symm (f : W.Iso V) (e : W.Edge) (b : Bool) :
    V.rotation.symm (f.edge e, b) =
      (f.edge (W.rotation.symm (e, b)).1, (W.rotation.symm (e, b)).2) := by
  apply V.rotation.injective
  simpa only [Equiv.apply_symm_apply, Prod.mk.eta] using
    (f.map_rotation (W.rotation.symm (e, b)).1 (W.rotation.symm (e, b)).2).symm

/-- A web isomorphism induces an isomorphism of the full bipartite subdivisions,
including the auxiliary circle components. -/
noncomputable def ribbonGraph (f : W.Iso V) : W.ribbonGraph.Iso V.ribbonGraph where
  edge := Equiv.sumCongr f.endEquiv (Equiv.prodCongr f.circle (Equiv.refl _))
  black := Equiv.sumCongr f.vertex f.circle
  white := Equiv.sumCongr f.edge f.circle
  map_blackEnd := by
    rintro (⟨e, b⟩ | ⟨c, b⟩)
    · change Sum.inl (V.incident (f.endEquiv (e, b))) =
        (Sum.inl (f.vertex (W.incident (e, b))) : V.Vertex ⊕ V.Circle)
      simp
    · rfl
  map_whiteEnd := by
    rintro (⟨e, b⟩ | ⟨c, b⟩)
    · change (Sum.inl (f.endEquiv (e, b)).1 : V.Edge ⊕ V.Circle) = Sum.inl (f.edge e)
      simp
    · rfl
  map_rotB := by
    rintro (⟨e, b⟩ | ⟨c, b⟩)
    · change Sum.inl (f.endEquiv (W.rotation (e, b))) =
        (Sum.inl (V.rotation (f.endEquiv (e, b))) : V.RibbonEdge)
      simp
    · change Sum.inr ((f.circle.prodCongr (Equiv.refl Bool)) (W.circleSwap (c, b))) =
        (Sum.inr (V.circleSwap (f.circle c, b)) : V.RibbonEdge)
      simp
  map_rotW := by
    rintro (⟨e, b⟩ | ⟨c, b⟩)
    · change Sum.inl (f.endEquiv (W.endSwap (e, b))) =
        (Sum.inl (V.endSwap (f.endEquiv (e, b))) : V.RibbonEdge)
      simp
    · change Sum.inr ((f.circle.prodCongr (Equiv.refl Bool)) (W.circleSwap (c, b))) =
        (Sum.inr (V.circleSwap (f.circle c, b)) : V.RibbonEdge)
      simp

@[simp] theorem ribbonGraph_edge (f : W.Iso V) :
    f.ribbonGraph.edge =
      Equiv.sumCongr f.endEquiv (Equiv.prodCongr f.circle (Equiv.refl _)) := (rfl)

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

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.ConnectedComponent
public import TauCeti.Combinatorics.Network.Isomorphism.Basic

/-!
# Walks and reachability under network isomorphisms

A network isomorphism transports directed walks bijectively, preserving the ordered lists of
vertices and arrow identities. Consequently it preserves simple paths, directed cycles, and
both vertex and arrow disjointness. The reachability statements include positive-capacity
reachability and reachability after deleting vertices or arrows, so relabelling a network does
not change its path witnesses or its separating sets.

All statements are independent of vertex and arrow finiteness. The coefficient type of an
assignment need not be the coefficient type of the network's bounds.
-/

public section

namespace TauCeti.Network.Iso

universe u u' v v' w w'

variable {K : Type w} [LE K] {V : Type u} {W : Type u'}
  {N : Network K V} {N' : Network K W}

/-- Transporting a walk commutes with changing its endpoints along equalities. -/
@[simp]
theorem mapPath_cast (e : N ≃ₙ N') {x y x' y' : V} (p : ArrowWalk N.Hom x y)
    (hx : x = x') (hy : y = y') :
    e.mapPath (@Quiver.Path.cast V ⟨N.Hom⟩ _ _ _ _ hx hy p) =
      @Quiver.Path.cast W ⟨N'.Hom⟩ _ _ _ _ (congrArg e.vertexEquiv hx)
        (congrArg e.vertexEquiv hy) (e.mapPath p) := by
  subst x' y'
  rfl

/-- Walk transport is an equivalence for each pair of endpoints. -/
def pathEquiv (e : N ≃ₙ N') (x y : V) :
    ArrowWalk N.Hom x y ≃ ArrowWalk N'.Hom (e.vertexEquiv x) (e.vertexEquiv y) where
  toFun := e.mapPath
  invFun p := @Quiver.Path.cast V ⟨N.Hom⟩ _ _ _ _
    (e.symm_vertexEquiv_apply_vertexEquiv x) (e.symm_vertexEquiv_apply_vertexEquiv y)
    (e.symm.mapPath p)
  left_inv p := e.mapPath_symm_mapPath p
  right_inv p := by
    rw [mapPath_cast]
    exact e.mapPath_mapPath_symm p

@[simp]
theorem pathEquiv_apply (e : N ≃ₙ N') {x y : V} (p : ArrowWalk N.Hom x y) :
    e.pathEquiv x y p = e.mapPath p := (rfl)

@[simp]
theorem pathEquiv_symm_apply (e : N ≃ₙ N') {x y : V}
    (p : ArrowWalk N'.Hom (e.vertexEquiv x) (e.vertexEquiv y)) :
    (e.pathEquiv x y).symm p = @Quiver.Path.cast V ⟨N.Hom⟩ _ _ _ _
      (e.symm_vertexEquiv_apply_vertexEquiv x) (e.symm_vertexEquiv_apply_vertexEquiv y)
      (e.symm.mapPath p) := (rfl)

/-- Walk transport maps the arrow sequence in order, retaining parallel arrows and repetitions. -/
@[simp]
theorem arrows_mapPath (e : N ≃ₙ N') {x y : V} (p : ArrowWalk N.Hom x y) :
    (e.mapPath p).arrows = p.arrows.map e.totalHomEquiv := by
  induction p with
  | nil => simp
  | cons p a ih => simp [ih, totalHomEquiv_apply]

/-- Transport preserves and reflects simple paths. -/
@[simp]
theorem isPath_mapPath (e : N ≃ₙ N') {x y : V} (p : ArrowWalk N.Hom x y) :
    (e.mapPath p).IsPath ↔ p.IsPath := by
  simp only [ArrowWalk.isPath_def, vertices_mapPath, List.nodup_map_iff e.vertexEquiv.injective]

/-- Transport preserves and reflects directed cycles, including loops. -/
@[simp]
theorem isCycle_mapPath (e : N ≃ₙ N') {x : V} (p : ArrowWalk N.Hom x x) :
    (e.mapPath p).IsCycle ↔ p.IsCycle := by
  simp only [ArrowWalk.isCycle_def, length_mapPath, vertices_mapPath, ← List.map_tail,
    List.nodup_map_iff e.vertexEquiv.injective]

/-- Two transported walks have disjoint arrow identities exactly when the original walks do.
Use explicitly: simplification first normalizes the arrow lists by `arrows_mapPath`. -/
theorem disjoint_arrows_mapPath (e : N ≃ₙ N') {x y z t : V}
    (p : ArrowWalk N.Hom x y) (q : ArrowWalk N.Hom z t) :
    (e.mapPath p).arrows.Disjoint (e.mapPath q).arrows ↔ p.arrows.Disjoint q.arrows := by
  simp only [arrows_mapPath, List.Disjoint.map_iff e.totalHomEquiv.injective]

/-- Two transported walks have disjoint vertex sets exactly when the original walks do.
Use explicitly: simplification first normalizes the vertex lists by `vertices_mapPath`. -/
theorem disjoint_vertices_mapPath (e : N ≃ₙ N') {x y z t : V}
    (p : ArrowWalk N.Hom x y) (q : ArrowWalk N.Hom z t) :
    (e.mapPath p).vertices.Disjoint (e.mapPath q).vertices ↔ p.vertices.Disjoint q.vertices := by
  simp only [vertices_mapPath, List.Disjoint.map_iff e.vertexEquiv.injective]

/-- Transport preserves and reflects internal vertex disjointness between fixed terminals. -/
@[simp]
theorem internallyDisjoint_mapPath (e : N ≃ₙ N') {x y : V}
    (p q : ArrowWalk N.Hom x y) :
    (e.mapPath p).InternallyDisjoint (e.mapPath q) ↔ p.InternallyDisjoint q := by
  simp only [ArrowWalk.internallyDisjoint_def, vertices_mapPath, List.mem_map]
  constructor
  · intro h v hvp hvq
    simpa using h (e.vertexEquiv v) ⟨v, hvp, rfl⟩ ⟨v, hvq, rfl⟩
  · rintro h _ ⟨v, hvp, rfl⟩ ⟨w, hwq, hwv⟩
    have hw : w = v := e.vertexEquiv.injective hwv
    subst w
    exact (h v hvp hwq).imp (congrArg e.vertexEquiv) (congrArg e.vertexEquiv)

/-- Reachability is unchanged by network isomorphism. -/
@[simp]
theorem nonempty_arrowWalk_iff (e : N ≃ₙ N') {x y : V} :
    Nonempty (ArrowWalk N'.Hom (e.vertexEquiv x) (e.vertexEquiv y)) ↔
      Nonempty (ArrowWalk N.Hom x y) :=
  (e.pathEquiv x y).nonempty_congr.symm

/-- Strong connectivity is unchanged by network isomorphism, including on an empty carrier. -/
theorem isStronglyConnected_iff (e : N ≃ₙ N') :
    @Quiver.IsStronglyConnected W ⟨N'.Hom⟩ ↔ @Quiver.IsStronglyConnected V ⟨N.Hom⟩ := by
  simp only [Quiver.isStronglyConnected_iff]
  constructor
  · intro h x y
    exact e.nonempty_arrowWalk_iff.1 (h (e.vertexEquiv x) (e.vertexEquiv y))
  · intro h x y
    obtain ⟨x, rfl⟩ := e.vertexEquiv.surjective x
    obtain ⟨y, rfl⟩ := e.vertexEquiv.surjective y
    exact e.nonempty_arrowWalk_iff.2 (h x y)

/-- Positive reachability is unchanged when both the network and its assignment are transported. -/
@[simp]
theorem positiveReachable_assignmentEquiv_iff {R : Type w'} [Zero R] [LT R]
    (e : N ≃ₙ N') (c : N.Assignment R) {x y : V} :
    PositiveReachable (e.assignmentEquiv R c) (e.vertexEquiv x) (e.vertexEquiv y) ↔
      PositiveReachable c x y := by
  simp only [positiveReachable_def]
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨p, rfl⟩ := (e.pathEquiv x y).surjective p
    refine ⟨p, fun a ha ↦ ?_⟩
    have h := hp (e.totalHomEquiv a) (by
      rw [pathEquiv_apply, arrows_mapPath]
      exact List.mem_map_of_mem ha)
    simpa only [assignmentEquiv_apply_totalHomEquiv] using h
  · rintro ⟨p, hp⟩
    refine ⟨e.mapPath p, ?_⟩
    rw [arrows_mapPath, List.forall_mem_map]
    simpa only [assignmentEquiv_apply_totalHomEquiv] using hp

/-- Deleting corresponding arrow identities preserves and reflects reachability.
Use explicitly: simplification expands the total-arrow equivalence inside the image. -/
theorem reachableWithout_image_iff (e : N ≃ₙ N') (F : Set (Σ x y, N.Hom x y)) {x y : V} :
    ReachableWithout (e.totalHomEquiv '' F) (e.vertexEquiv x) (e.vertexEquiv y) ↔
      ReachableWithout F x y := by
  simp only [reachableWithout_def]
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨p, rfl⟩ := (e.pathEquiv x y).surjective p
    refine ⟨p, fun a ha hF ↦ hp (e.totalHomEquiv a) ?_ ⟨a, hF, rfl⟩⟩
    rw [pathEquiv_apply, arrows_mapPath]
    exact List.mem_map_of_mem ha
  · rintro ⟨p, hp⟩
    refine ⟨e.mapPath p, ?_⟩
    simpa only [arrows_mapPath, List.forall_mem_map,
      e.totalHomEquiv.injective.mem_set_image] using hp

/-- Deleting corresponding vertices preserves and reflects reachability, including endpoints. -/
@[simp]
theorem reachableAvoiding_image_iff (e : N ≃ₙ N') (S : Set V) {x y : V} :
    ReachableAvoiding N'.Hom (e.vertexEquiv '' S) (e.vertexEquiv x) (e.vertexEquiv y) ↔
      ReachableAvoiding N.Hom S x y := by
  simp only [reachableAvoiding_def]
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨p, rfl⟩ := (e.pathEquiv x y).surjective p
    refine ⟨p, fun v hv hS ↦ hp (e.vertexEquiv v) ?_ ⟨v, hS, rfl⟩⟩
    simp [hv]
  · rintro ⟨p, hp⟩
    refine ⟨e.mapPath p, ?_⟩
    simpa only [vertices_mapPath, List.forall_mem_map,
      e.vertexEquiv.injective.mem_set_image] using hp

end TauCeti.Network.Iso

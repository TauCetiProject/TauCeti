/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Ear.Basic
public import TauCeti.Combinatorics.Network.Isomorphism.Subnetwork
public import TauCeti.Combinatorics.Network.Isomorphism.Walk

/-!
# Directed ear decompositions under network isomorphisms

A bounded-network isomorphism transports directed open and closed ears by relabelling their
vertices and individual arrow identities.  It therefore transports every prefix of a directed
ear decomposition, without changing the number or kind of its ears.

The characteristic formulas identify the transported prefix subnetworks, initial vertex, and
underlying walks.  In particular, loops remain one-arrow closed ears and parallel arrows remain
distinct throughout the transport.

## References

* J. Bang-Jensen and G. Gutin, *Digraphs: Theory, Algorithms and Applications*, Section 5.3.
-/

public section

namespace TauCeti.Network.Iso

universe u u' w

variable {K : Type w} [LE K] {V : Type u} {W : Type u'}
  {N : Network K V} {N' : Network K W}

/-- The subnetwork traced by a transported walk is the transport of the original traced
subnetwork. -/
@[simp]
theorem subnetworkOrderIso_toSubnetwork (e : N ≃ₙ N') {x y : V}
    (p : ArrowWalk N.Hom x y) :
    e.subnetworkOrderIso p.toSubnetwork = (e.mapPath p).toSubnetwork := by
  apply Network.Subnetwork.ext
  · rw [subnetworkOrderIso_vertexSet, ArrowWalk.toSubnetwork_vertexSet,
      ArrowWalk.toSubnetwork_vertexSet, vertices_mapPath]
    ext z
    simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_map]
  · rw [subnetworkOrderIso_arrowSet, ArrowWalk.toSubnetwork_arrowSet,
      ArrowWalk.toSubnetwork_arrowSet, arrows_mapPath]
    ext a
    simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_map]

/-- Transport an open directed ear along a bounded-network isomorphism. -/
@[expose]
def mapOpenEar (e : N ≃ₙ N') {S : N.Subnetwork} (P : N.OpenEar S) :
    N'.OpenEar (e.subnetworkOrderIso S) where
  source := e.vertexEquiv P.source
  target := e.vertexEquiv P.target
  walk := e.mapPath P.walk
  isPath := (e.isPath_mapPath P.walk).2 P.isPath
  source_mem := by
    rw [subnetworkOrderIso_vertexSet, e.vertexEquiv.injective.mem_set_image]
    exact P.source_mem
  target_mem := by
    rw [subnetworkOrderIso_vertexSet, e.vertexEquiv.injective.mem_set_image]
    exact P.target_mem
  source_ne_target := e.vertexEquiv.injective.ne P.source_ne_target
  internal_notMem := by
    intro x hx hxs hxt hxS
    rw [vertices_mapPath] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact P.internal_notMem y hy
      (fun h ↦ hxs (congrArg e.vertexEquiv h))
      (fun h ↦ hxt (congrArg e.vertexEquiv h))
      (by simpa using hxS)
  arrows_notMem := by
    rw [arrows_mapPath, List.forall_mem_map]
    intro b hb
    rw [subnetworkOrderIso_arrowSet, e.totalHomEquiv.injective.mem_set_image]
    exact P.arrows_notMem b hb

/-- The source of a transported open ear is the image of its source. -/
@[simp]
theorem mapOpenEar_source (e : N ≃ₙ N') {S : N.Subnetwork} (P : N.OpenEar S) :
    (e.mapOpenEar P).source = e.vertexEquiv P.source :=
  (rfl)

/-- The target of a transported open ear is the image of its target. -/
@[simp]
theorem mapOpenEar_target (e : N ≃ₙ N') {S : N.Subnetwork} (P : N.OpenEar S) :
    (e.mapOpenEar P).target = e.vertexEquiv P.target :=
  (rfl)

/-- The walk of a transported open ear is the transported walk. -/
@[simp]
theorem mapOpenEar_walk (e : N ≃ₙ N') {S : N.Subnetwork} (P : N.OpenEar S) :
    (e.mapOpenEar P).walk = e.mapPath P.walk :=
  (rfl)

/-- Transport a closed directed ear along a bounded-network isomorphism. -/
@[expose]
def mapClosedEar (e : N ≃ₙ N') {S : N.Subnetwork} (P : N.ClosedEar S) :
    N'.ClosedEar (e.subnetworkOrderIso S) where
  base := e.vertexEquiv P.base
  walk := e.mapPath P.walk
  isCycle := (e.isCycle_mapPath P.walk).2 P.isCycle
  base_mem := by
    rw [subnetworkOrderIso_vertexSet, e.vertexEquiv.injective.mem_set_image]
    exact P.base_mem
  eq_base_of_mem := by
    intro x hx hxS
    rw [vertices_mapPath] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact congrArg e.vertexEquiv (P.eq_base_of_mem y hy (by simpa using hxS))
  arrows_notMem := by
    rw [arrows_mapPath, List.forall_mem_map]
    intro b hb
    rw [subnetworkOrderIso_arrowSet, e.totalHomEquiv.injective.mem_set_image]
    exact P.arrows_notMem b hb

/-- The base of a transported closed ear is the image of its base. -/
@[simp]
theorem mapClosedEar_base (e : N ≃ₙ N') {S : N.Subnetwork} (P : N.ClosedEar S) :
    (e.mapClosedEar P).base = e.vertexEquiv P.base :=
  (rfl)

/-- The walk of a transported closed ear is the transported walk. -/
@[simp]
theorem mapClosedEar_walk (e : N ≃ₙ N') {S : N.Subnetwork} (P : N.ClosedEar S) :
    (e.mapClosedEar P).walk = e.mapPath P.walk :=
  (rfl)

/-- Transport an open or closed directed ear along a bounded-network isomorphism. -/
@[expose]
def mapEar (e : N ≃ₙ N') {S : N.Subnetwork} :
    N.Ear S → N'.Ear (e.subnetworkOrderIso S)
  | .open P => .open (e.mapOpenEar P)
  | .closed P => .closed (e.mapClosedEar P)

/-- Transport preserves whether an ear is open or closed. -/
@[simp]
theorem mapEar_kind (e : N ≃ₙ N') {S : N.Subnetwork} (P : N.Ear S) :
    (e.mapEar P).kind = P.kind := by
  cases P <;> simp only [mapEar, Network.Ear.kind_open, Network.Ear.kind_closed]

/-- Transporting the subnetwork traced by an ear agrees with transporting the ear. -/
@[simp]
theorem subnetworkOrderIso_ear_toSubnetwork (e : N ≃ₙ N') {S : N.Subnetwork}
    (P : N.Ear S) :
    e.subnetworkOrderIso P.toSubnetwork = (e.mapEar P).toSubnetwork := by
  cases P <;>
    simp only [Network.Ear.toSubnetwork_open, Network.Ear.toSubnetwork_closed, mapEar,
      mapOpenEar_walk, mapClosedEar_walk]
  all_goals exact e.subnetworkOrderIso_toSubnetwork _

/-- Adjoining an ear commutes with transport along a bounded-network isomorphism. -/
@[simp]
theorem subnetworkOrderIso_adjoin (e : N ≃ₙ N') {S : N.Subnetwork} (P : N.Ear S) :
    e.subnetworkOrderIso P.adjoin = (e.mapEar P).adjoin := by
  simp only [Network.Ear.adjoin_def, map_sup, subnetworkOrderIso_ear_toSubnetwork]

/-- Transport every stage and ear of a directed ear decomposition along a bounded-network
isomorphism. -/
@[expose]
def mapEarDecomposition (e : N ≃ₙ N') {T : N.Subnetwork}
    (D : N.EarDecomposition T) :
    N'.EarDecomposition (e.subnetworkOrderIso T) where
  length := D.length
  initialVertex := e.vertexEquiv D.initialVertex
  stage i := e.subnetworkOrderIso (D.stage i)
  ear i := e.mapEar (D.ear i)
  stage_zero := by simp
  stage_succ i := by simp [D.stage_succ]
  stage_last := by simp

/-- Transport does not change the number of ears. -/
@[simp]
theorem mapEarDecomposition_length (e : N ≃ₙ N') {T : N.Subnetwork}
    (D : N.EarDecomposition T) : (e.mapEarDecomposition D).length = D.length :=
  (rfl)

/-- Transport relabels the initial vertex. -/
@[simp]
theorem mapEarDecomposition_initialVertex (e : N ≃ₙ N') {T : N.Subnetwork}
    (D : N.EarDecomposition T) :
    (e.mapEarDecomposition D).initialVertex = e.vertexEquiv D.initialVertex :=
  (rfl)

/-- Every prefix stage is transported by the induced subnetwork order isomorphism. -/
@[simp]
theorem mapEarDecomposition_stage (e : N ≃ₙ N') {T : N.Subnetwork}
    (D : N.EarDecomposition T) (i : Fin (D.length + 1)) :
    (e.mapEarDecomposition D).stage i = e.subnetworkOrderIso (D.stage i) :=
  (rfl)

/-- Every displayed ear is transported along the network isomorphism. -/
@[simp]
theorem mapEarDecomposition_ear (e : N ≃ₙ N') {T : N.Subnetwork}
    (D : N.EarDecomposition T) (i : Fin D.length) :
    (e.mapEarDecomposition D).ear i = e.mapEar (D.ear i) :=
  (rfl)

/-- Transport preserves the kind of every displayed ear. -/
@[simp]
theorem mapEarDecomposition_kindAt (e : N ≃ₙ N') {T : N.Subnetwork}
    (D : N.EarDecomposition T) (i : Fin D.length) :
    (e.mapEarDecomposition D).kindAt i = D.kindAt i := by
  calc
    (e.mapEarDecomposition D).kindAt i = ((e.mapEarDecomposition D).ear i).kind :=
      Network.EarDecomposition.kindAt_def _ _
    _ = (e.mapEar (D.ear i)).kind := congrArg Network.Ear.kind (e.mapEarDecomposition_ear D i)
    _ = (D.ear i).kind := e.mapEar_kind (D.ear i)
    _ = D.kindAt i := (Network.EarDecomposition.kindAt_def _ _).symm

/-- Transport a full directed ear decomposition to a full decomposition of the isomorphic
network. -/
def mapFullEarDecomposition (e : N ≃ₙ N')
    (D : N.EarDecomposition (⊤ : N.Subnetwork)) :
    N'.EarDecomposition ⊤ :=
  (e.mapEarDecomposition D).copy (by simp)

/-- Transporting a full decomposition does not change its number of ears. -/
@[simp]
theorem mapFullEarDecomposition_length (e : N ≃ₙ N')
    (D : N.EarDecomposition (⊤ : N.Subnetwork)) :
    (e.mapFullEarDecomposition D).length = D.length :=
  (rfl)

/-- Transporting a full decomposition relabels its initial vertex. -/
@[simp]
theorem mapFullEarDecomposition_initialVertex (e : N ≃ₙ N')
    (D : N.EarDecomposition (⊤ : N.Subnetwork)) :
    (e.mapFullEarDecomposition D).initialVertex = e.vertexEquiv D.initialVertex :=
  (rfl)

/-- Isomorphic bounded networks admit full directed ear decompositions simultaneously. -/
theorem nonempty_earDecomposition_top_iff (e : N ≃ₙ N') :
    Nonempty (N'.EarDecomposition ⊤) ↔ Nonempty (N.EarDecomposition ⊤) := by
  constructor
  · rintro ⟨D⟩
    exact ⟨e.symm.mapFullEarDecomposition D⟩
  · rintro ⟨D⟩
    exact ⟨e.mapFullEarDecomposition D⟩

end TauCeti.Network.Iso

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Subnetwork

/-!
# Directed ear decompositions

This file packages the data used to build a directed network one ear at a time. An open directed
ear is a directed path whose distinct endpoints already belong to the current subnetwork, while
its internal vertices and all its arrows are new. A closed directed ear is a directed cycle that
meets the current subnetwork only at its base vertex and likewise uses only new arrows. Loops are
therefore closed ears of length one.

The subnetwork of a walk consists of exactly its visited vertices and traversed arrows. Adjoining
an ear takes its union with the current subnetwork and strictly enlarges it. A directed ear
decomposition records every prefix subnetwork, the ear adjoined at each successor stage, and its
initial and final subnetworks. Prefixes are again decompositions, `Network.EarDecomposition.snoc`
appends one more ear, `Network.EarDecomposition.ofIsCycle` packages a single directed cycle, and
the ears of any decomposition partition the arrow set of the decomposed subnetwork.

## References

* J. Bang-Jensen and G. Gutin, *Digraphs: Theory, Algorithms and Applications*, Section 5.3.
-/

public section

namespace TauCeti

universe u v w

variable {K : Type w} {V : Type u} [LE K] {N : Network K V}

namespace Network

/-- The two kinds of directed ears adjoined during an ear decomposition. -/
inductive EarKind
  /-- An open ear between distinct old endpoints. -/
  | open
  /-- A closed ear based at one old vertex. -/
  | closed
  deriving DecidableEq

/-- An open directed ear relative to a subnetwork. Its endpoints are distinct old vertices, its
internal vertices are new, and every traversed arrow is new. -/
structure OpenEar (S : N.Subnetwork) where
  /-- The first vertex of the ear. -/
  source : V
  /-- The last vertex of the ear. -/
  target : V
  /-- The directed walk underlying the ear. -/
  walk : ArrowWalk N.Hom source target
  /-- The underlying walk is a directed path. -/
  isPath : walk.IsPath
  /-- The first vertex already belongs to the current subnetwork. -/
  source_mem : source ∈ S.vertexSet
  /-- The last vertex already belongs to the current subnetwork. -/
  target_mem : target ∈ S.vertexSet
  /-- An open ear has distinct endpoints. -/
  source_ne_target : source ≠ target
  /-- Every vertex other than the endpoints is new. -/
  internal_notMem : ∀ x ∈ walk.vertices, x ≠ source → x ≠ target → x ∉ S.vertexSet
  /-- Every arrow of the ear is new. -/
  arrows_notMem : ∀ a ∈ walk.arrows, a ∉ S.arrowSet

namespace OpenEar

variable {S : N.Subnetwork}

/-- Open ears are equal when their endpoints and walks agree. -/
@[ext]
theorem ext {P Q : OpenEar S} (hsource : P.source = Q.source)
    (htarget : P.target = Q.target) (hwalk : HEq P.walk Q.walk) : P = Q := by
  cases P
  cases Q
  cases hsource
  cases htarget
  cases hwalk
  rfl

/-- The endpoint-indexed directed walk underlying an open ear. -/
def toWalk (P : OpenEar S) : Σ s t : V, ArrowWalk N.Hom s t :=
  ⟨P.source, P.target, P.walk⟩

@[simp]
theorem toWalk_mk (source target : V) (walk : ArrowWalk N.Hom source target)
    (isPath : walk.IsPath) (source_mem : source ∈ S.vertexSet) (target_mem : target ∈ S.vertexSet)
    (source_ne_target : source ≠ target)
    (internal_notMem : ∀ x ∈ walk.vertices, x ≠ source → x ≠ target → x ∉ S.vertexSet)
    (arrows_notMem : ∀ a ∈ walk.arrows, a ∉ S.arrowSet) :
    (OpenEar.mk source target walk isPath source_mem target_mem source_ne_target
      internal_notMem arrows_notMem).toWalk = ⟨source, target, walk⟩ :=
  (rfl)

/-- The subnetwork of an open ear meets the old vertex set exactly at its two endpoints. -/
theorem mem_toSubnetwork_vertexSet_and_mem_iff (P : OpenEar S) (x : V) :
    x ∈ P.walk.toSubnetwork.vertexSet ∧ x ∈ S.vertexSet ↔ x = P.source ∨ x = P.target := by
  constructor
  · rintro ⟨hx, hxS⟩
    by_contra h
    simp only [not_or] at h
    exact P.internal_notMem x (by simpa using hx) h.1 h.2 hxS
  · rintro (rfl | rfl)
    · exact ⟨P.walk.source_mem_toSubnetwork, P.source_mem⟩
    · exact ⟨P.walk.target_mem_toSubnetwork, P.target_mem⟩

/-- An open ear traverses at least one arrow. -/
theorem arrows_ne_nil (P : OpenEar S) : P.walk.arrows ≠ [] :=
  P.walk.arrows_ne_nil P.source_ne_target

/-- The walk of an open ear has positive length. -/
theorem length_pos (P : OpenEar S) : 0 < P.walk.length :=
  Nat.pos_of_ne_zero fun h ↦ P.arrows_ne_nil (ArrowWalk.arrows_eq_nil_iff.2 h)

/-- An unused arrow between two distinct vertices of `S` forms a single-arrow open ear. -/
def ofArrow {u v : V} (e : N.Hom u v) (hu : u ∈ S.vertexSet) (hv : v ∈ S.vertexSet)
    (huv : u ≠ v) (he : (⟨u, v, e⟩ : Σ x y, N.Hom x y) ∉ S.arrowSet) : OpenEar S where
  source := u
  target := v
  walk := (ArrowWalk.nil u).cons e
  isPath := by
    rw [ArrowWalk.isPath_def, ArrowWalk.vertices_cons, ArrowWalk.vertices_nil]
    simpa using huv
  source_mem := hu
  target_mem := hv
  source_ne_target := huv
  internal_notMem := by
    intro x hx hxu hxv
    simp only [ArrowWalk.vertices_cons, ArrowWalk.vertices_nil, List.concat_eq_append,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    exact hx.elim (fun h ↦ (hxu h).elim) (fun h ↦ (hxv h).elim)
  arrows_notMem := by
    intro a ha
    simp only [ArrowWalk.arrows_cons, ArrowWalk.arrows_nil, List.nil_append,
      List.mem_singleton] at ha
    exact ha ▸ he

@[simp]
theorem ofArrow_source {u v : V} (e : N.Hom u v) (hu : u ∈ S.vertexSet) (hv : v ∈ S.vertexSet)
    (huv : u ≠ v) (he : (⟨u, v, e⟩ : Σ x y, N.Hom x y) ∉ S.arrowSet) :
    (ofArrow e hu hv huv he).source = u :=
  (rfl)

@[simp]
theorem ofArrow_target {u v : V} (e : N.Hom u v) (hu : u ∈ S.vertexSet) (hv : v ∈ S.vertexSet)
    (huv : u ≠ v) (he : (⟨u, v, e⟩ : Σ x y, N.Hom x y) ∉ S.arrowSet) :
    (ofArrow e hu hv huv he).target = v :=
  (rfl)

@[simp]
theorem ofArrow_toWalk {u v : V} (e : N.Hom u v) (hu : u ∈ S.vertexSet) (hv : v ∈ S.vertexSet)
    (huv : u ≠ v) (he : (⟨u, v, e⟩ : Σ x y, N.Hom x y) ∉ S.arrowSet) :
    (ofArrow e hu hv huv he).toWalk = ⟨u, v, (ArrowWalk.nil u).cons e⟩ :=
  (rfl)

@[simp]
theorem ofArrow_walk_toSubnetwork {u v : V} (e : N.Hom u v) (hu : u ∈ S.vertexSet)
    (hv : v ∈ S.vertexSet) (huv : u ≠ v) (he : (⟨u, v, e⟩ : Σ x y, N.Hom x y) ∉ S.arrowSet) :
    (ofArrow e hu hv huv he).walk.toSubnetwork = ((ArrowWalk.nil u).cons e).toSubnetwork :=
  (rfl)

end OpenEar

/-- A closed directed ear relative to a subnetwork. Its directed cycle meets the old vertices only
at its base, and every traversed arrow is new. -/
structure ClosedEar (S : N.Subnetwork) where
  /-- The old vertex at which the closed ear is based. -/
  base : V
  /-- The directed closed walk underlying the ear. -/
  walk : ArrowWalk N.Hom base base
  /-- The underlying walk is a directed cycle. -/
  isCycle : walk.IsCycle
  /-- The base already belongs to the current subnetwork. -/
  base_mem : base ∈ S.vertexSet
  /-- The cycle meets the current subnetwork only at its base. -/
  eq_base_of_mem : ∀ x ∈ walk.vertices, x ∈ S.vertexSet → x = base
  /-- Every arrow of the ear is new. -/
  arrows_notMem : ∀ a ∈ walk.arrows, a ∉ S.arrowSet

namespace ClosedEar

variable {S : N.Subnetwork}

/-- Closed ears are equal when their bases and walks agree. -/
@[ext]
theorem ext {P Q : ClosedEar S} (hbase : P.base = Q.base) (hwalk : HEq P.walk Q.walk) :
    P = Q := by
  cases P
  cases Q
  cases hbase
  cases hwalk
  rfl

/-- The endpoint-indexed directed walk underlying a closed ear. -/
def toWalk (P : ClosedEar S) : Σ s t : V, ArrowWalk N.Hom s t :=
  ⟨P.base, P.base, P.walk⟩

@[simp]
theorem toWalk_mk (base : V) (walk : ArrowWalk N.Hom base base) (isCycle : walk.IsCycle)
    (base_mem : base ∈ S.vertexSet)
    (eq_base_of_mem : ∀ x ∈ walk.vertices, x ∈ S.vertexSet → x = base)
    (arrows_notMem : ∀ a ∈ walk.arrows, a ∉ S.arrowSet) :
    (ClosedEar.mk base walk isCycle base_mem eq_base_of_mem arrows_notMem).toWalk =
      ⟨base, base, walk⟩ :=
  (rfl)

/-- The subnetwork of a closed ear meets the old vertex set exactly at its base. -/
theorem mem_toSubnetwork_vertexSet_and_mem_iff (P : ClosedEar S) (x : V) :
    x ∈ P.walk.toSubnetwork.vertexSet ∧ x ∈ S.vertexSet ↔ x = P.base := by
  constructor
  · exact fun h ↦ P.eq_base_of_mem x (by simpa using h.1) h.2
  · rintro rfl
    exact ⟨P.walk.source_mem_toSubnetwork, P.base_mem⟩

/-- A closed ear traverses at least one arrow. -/
theorem arrows_ne_nil (P : ClosedEar S) : P.walk.arrows ≠ [] :=
  P.isCycle.arrows_ne_nil

/-- The walk of a closed ear has positive length. -/
theorem length_pos (P : ClosedEar S) : 0 < P.walk.length :=
  Nat.pos_of_ne_zero fun h ↦ P.arrows_ne_nil (ArrowWalk.arrows_eq_nil_iff.2 h)

/-- An unused loop at a vertex of `S` forms a closed ear of length one. -/
def ofLoop {u : V} (e : N.Hom u u) (hu : u ∈ S.vertexSet)
    (he : (⟨u, u, e⟩ : Σ x y, N.Hom x y) ∉ S.arrowSet) : ClosedEar S where
  base := u
  walk := (ArrowWalk.nil u).cons e
  isCycle := ArrowWalk.isCycle_loop e
  base_mem := hu
  eq_base_of_mem := by
    intro x hx _
    simp only [ArrowWalk.vertices_cons, ArrowWalk.vertices_nil, List.concat_eq_append,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      or_self] at hx
    exact hx
  arrows_notMem := by
    intro a ha
    simp only [ArrowWalk.arrows_cons, ArrowWalk.arrows_nil, List.nil_append,
      List.mem_singleton] at ha
    exact ha ▸ he

@[simp]
theorem ofLoop_base {u : V} (e : N.Hom u u) (hu : u ∈ S.vertexSet)
    (he : (⟨u, u, e⟩ : Σ x y, N.Hom x y) ∉ S.arrowSet) :
    (ofLoop e hu he).base = u :=
  (rfl)

@[simp]
theorem ofLoop_toWalk {u : V} (e : N.Hom u u) (hu : u ∈ S.vertexSet)
    (he : (⟨u, u, e⟩ : Σ x y, N.Hom x y) ∉ S.arrowSet) :
    (ofLoop e hu he).toWalk = ⟨u, u, (ArrowWalk.nil u).cons e⟩ :=
  (rfl)

@[simp]
theorem ofLoop_walk_toSubnetwork {u : V} (e : N.Hom u u) (hu : u ∈ S.vertexSet)
    (he : (⟨u, u, e⟩ : Σ x y, N.Hom x y) ∉ S.arrowSet) :
    (ofLoop e hu he).walk.toSubnetwork = ((ArrowWalk.nil u).cons e).toSubnetwork :=
  (rfl)

/-- Any directed cycle `c` at `v₀` is a closed ear over `N.singletonSubnetwork v₀`. -/
def ofIsCycle {v₀ : V} {c : ArrowWalk N.Hom v₀ v₀} (hc : c.IsCycle) :
    ClosedEar (N.singletonSubnetwork v₀) where
  base := v₀
  walk := c
  isCycle := hc
  base_mem := by simp
  eq_base_of_mem _ _ hx := by simpa using hx
  arrows_notMem _ _ ha := by simp at ha

@[simp]
theorem ofIsCycle_base {v₀ : V} {c : ArrowWalk N.Hom v₀ v₀} (hc : c.IsCycle) :
    (ofIsCycle (N := N) hc).base = v₀ :=
  (rfl)

@[simp]
theorem ofIsCycle_toWalk {v₀ : V} {c : ArrowWalk N.Hom v₀ v₀} (hc : c.IsCycle) :
    (ofIsCycle (N := N) hc).toWalk = ⟨v₀, v₀, c⟩ :=
  (rfl)

@[simp]
theorem ofIsCycle_walk_toSubnetwork {v₀ : V} {c : ArrowWalk N.Hom v₀ v₀} (hc : c.IsCycle) :
    (ofIsCycle (N := N) hc).walk.toSubnetwork = c.toSubnetwork :=
  (rfl)

end ClosedEar

/-- An open or closed directed ear relative to a subnetwork. -/
inductive Ear (S : N.Subnetwork) where
  /-- An ear with two distinct old endpoints. -/
  | open (ear : OpenEar S)
  /-- An ear based at one old vertex. -/
  | closed (ear : ClosedEar S)

namespace Ear

variable {S : N.Subnetwork}

/-- Whether an ear is open or closed. -/
def kind : Ear S → EarKind
  | .open _ => .open
  | .closed _ => .closed

@[simp]
theorem kind_open (P : OpenEar S) : (Ear.open P).kind = .open :=
  (rfl)

@[simp]
theorem kind_closed (P : ClosedEar S) : (Ear.closed P).kind = .closed :=
  (rfl)

/-- The endpoint-indexed directed walk underlying an ear. -/
def toWalk : Ear S → Σ s t : V, ArrowWalk N.Hom s t
  | .open P => P.toWalk
  | .closed P => P.toWalk

@[simp]
theorem toWalk_open (P : OpenEar S) : (Ear.open P).toWalk = P.toWalk :=
  (rfl)

@[simp]
theorem toWalk_closed (P : ClosedEar S) : (Ear.closed P).toWalk = P.toWalk :=
  (rfl)

/-- Ears over `S` are determined by their endpoint-indexed walk; distinctness vs. equality of the
walk's endpoints distinguishes open ears from closed ears. -/
@[ext]
theorem ext {P Q : Ear S} (hwalk : P.toWalk = Q.toWalk) : P = Q := by
  rcases P with ⟨s₁, t₁, w₁, _, _, _, hne₁, _, _⟩ | ⟨b₁, w₁, _, _, _, _⟩ <;>
    rcases Q with ⟨s₂, t₂, w₂, _, _, _, hne₂, _, _⟩ | ⟨b₂, w₂, _, _, _, _⟩
  · simp only [toWalk_open, OpenEar.toWalk_mk] at hwalk
    injection hwalk with hs htw
    subst hs
    injection htw with ht hw
    subst ht
    cases eq_of_heq hw
    rfl
  · simp only [toWalk_open, toWalk_closed, OpenEar.toWalk_mk, ClosedEar.toWalk_mk] at hwalk
    injection hwalk with hs htw
    subst hs
    exact (hne₁ (congrArg Sigma.fst (eq_of_heq htw)).symm).elim
  · simp only [toWalk_open, toWalk_closed, OpenEar.toWalk_mk, ClosedEar.toWalk_mk] at hwalk
    injection hwalk with hs htw
    subst hs
    exact (hne₂ (congrArg Sigma.fst (eq_of_heq htw))).elim
  · simp only [toWalk_closed, ClosedEar.toWalk_mk] at hwalk
    injection hwalk with hb hbw
    subst hb
    injection hbw with _ hw
    cases hw
    rfl

/-- Transport an ear when its base subnetwork is replaced by an equal one. -/
def copy {T : N.Subnetwork} (P : Ear S) (h : S = T) : Ear T :=
  h ▸ P

/-- Transporting an ear along an equality of base subnetworks leaves it unchanged. -/
theorem copy_heq {T : N.Subnetwork} (P : Ear S) (h : S = T) : HEq (P.copy h) P := by
  subst h
  rfl

@[simp]
theorem copy_rfl (P : Ear S) : P.copy rfl = P :=
  eq_of_heq (P.copy_heq rfl)

@[simp]
theorem kind_copy {T : N.Subnetwork} (P : Ear S) (h : S = T) : (P.copy h).kind = P.kind := by
  subst h
  rfl

@[simp]
theorem toWalk_copy {T : N.Subnetwork} (P : Ear S) (h : S = T) :
    (P.copy h).toWalk = P.toWalk := by
  subst h
  rfl

/-- The subnetwork consisting of the vertices and arrows traversed by an ear. -/
def toSubnetwork : Ear S → N.Subnetwork
  | .open P => P.walk.toSubnetwork
  | .closed P => P.walk.toSubnetwork

/-- Adjoin an ear to the current subnetwork. -/
def adjoin (P : Ear S) : N.Subnetwork :=
  S ⊔ P.toSubnetwork

/-- Adjoining an ear is the union of the current subnetwork and the ear's subnetwork. -/
theorem adjoin_def (P : Ear S) : P.adjoin = S ⊔ P.toSubnetwork :=
  (rfl)

@[simp]
theorem toSubnetwork_open (P : OpenEar S) : (Ear.open P).toSubnetwork = P.walk.toSubnetwork :=
  Eq.refl _

@[simp]
theorem toSubnetwork_closed (P : ClosedEar S) :
    (Ear.closed P).toSubnetwork = P.walk.toSubnetwork :=
  Eq.refl _

/-- The subnetwork of an ear is the subnetwork of its underlying walk. -/
theorem toSubnetwork_eq_toWalk (P : Ear S) : P.toSubnetwork = P.toWalk.2.2.toSubnetwork := by
  cases P <;> rfl

/-- Every ear traverses at least one arrow. -/
theorem arrows_ne_nil (P : Ear S) : P.toWalk.2.2.arrows ≠ [] := by
  cases P with
  | «open» P => exact P.arrows_ne_nil
  | closed P => exact P.arrows_ne_nil

/-- The walk underlying any ear has positive length. -/
theorem length_pos (P : Ear S) : 0 < P.toWalk.2.2.length := by
  cases P with
  | «open» P => exact P.length_pos
  | closed P => exact P.length_pos

/-- Transporting an ear does not change the subnetwork traced by its walk. -/
@[simp]
theorem toSubnetwork_copy {T : N.Subnetwork} (P : Ear S) (h : S = T) :
    (P.copy h).toSubnetwork = P.toSubnetwork := by
  subst h
  rfl

theorem kind_eq_of_heq {T : N.Subnetwork} {P : Ear S} {Q : Ear T} (hST : S = T) (h : HEq P Q) :
    P.kind = Q.kind := by
  cases hST
  cases h
  rfl

theorem toWalk_eq_of_heq {T : N.Subnetwork} {P : Ear S} {Q : Ear T} (hST : S = T) (h : HEq P Q) :
    P.toWalk = Q.toWalk := by
  cases hST
  cases h
  rfl

theorem toSubnetwork_eq_of_heq {T : N.Subnetwork} {P : Ear S} {Q : Ear T} (hST : S = T)
    (h : HEq P Q) : P.toSubnetwork = Q.toSubnetwork := by
  cases hST
  cases h
  rfl

/-- Transporting an ear along equality does not change the resulting enlarged subnetwork. -/
@[simp]
theorem adjoin_copy {T : N.Subnetwork} (P : Ear S) (h : S = T) :
    (P.copy h).adjoin = P.adjoin := by
  subst h
  rfl

/-- Adjoining an ear retains the current subnetwork. -/
theorem le_adjoin (P : Ear S) : S ≤ P.adjoin :=
  Network.Subnetwork.le_union_left _ _

/-- The subnetwork of an ear is contained in the subnetwork obtained by adjoining it. -/
theorem toSubnetwork_le_adjoin (P : Ear S) : P.toSubnetwork ≤ P.adjoin :=
  Network.Subnetwork.le_union_right _ _

/-- No arrow of an ear belongs to the old subnetwork. -/
theorem disjoint_arrowSet (P : Ear S) : Disjoint P.toSubnetwork.arrowSet S.arrowSet := by
  rw [Set.disjoint_left]
  cases P with
  | «open» P => exact fun a ha hS ↦ P.arrows_notMem a (by simpa using ha) hS
  | closed P => exact fun a ha hS ↦ P.arrows_notMem a (by simpa using ha) hS

@[simp]
theorem adjoin_vertexSet (P : Ear S) :
    P.adjoin.vertexSet = S.vertexSet ∪ P.toSubnetwork.vertexSet :=
  Network.Subnetwork.sup_vertexSet _ _

@[simp]
theorem adjoin_arrowSet (P : Ear S) :
    P.adjoin.arrowSet = S.arrowSet ∪ P.toSubnetwork.arrowSet :=
  Network.Subnetwork.sup_arrowSet _ _

/-- Every ear traverses at least one arrow. -/
theorem nonempty_toSubnetwork_arrowSet (P : Ear S) : P.toSubnetwork.arrowSet.Nonempty := by
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ P.arrows_ne_nil
  exact ⟨a, by simpa [P.toSubnetwork_eq_toWalk] using ha⟩

/-- Adjoining an ear strictly enlarges the current subnetwork, since its arrows are new. -/
theorem lt_adjoin (P : Ear S) : S < P.adjoin := by
  refine lt_of_le_of_ne P.le_adjoin fun h ↦ ?_
  obtain ⟨a, ha⟩ := P.nonempty_toSubnetwork_arrowSet
  have haS : a ∈ S.arrowSet := by
    rw [h, adjoin_arrowSet]
    exact Or.inr ha
  exact Set.disjoint_left.1 P.disjoint_arrowSet ha haS

end Ear

@[simp]
theorem ClosedEar.ofIsCycle_adjoin {v₀ : V} {c : ArrowWalk N.Hom v₀ v₀} (hc : c.IsCycle) :
    (Ear.closed (ClosedEar.ofIsCycle (N := N) hc)).adjoin = c.toSubnetwork := by
  rw [Ear.adjoin_def, Ear.toSubnetwork_closed, ClosedEar.ofIsCycle_walk_toSubnetwork]
  exact sup_eq_right.2 (Subnetwork.le_def.2 ⟨by simp, by simp⟩)

/-- A finite directed ear decomposition of the subnetwork `T`. It starts at one vertex and records
the subnetwork after every prefix, together with the ear adjoined at each successor stage. -/
structure EarDecomposition (T : N.Subnetwork) where
  /-- The number of ears. -/
  length : ℕ
  /-- The vertex at which the construction starts. -/
  initialVertex : V
  /-- The subnetwork after each prefix of the ear sequence. -/
  stage : Fin (length + 1) → N.Subnetwork
  /-- The ear adjoined after each proper prefix. -/
  ear : (i : Fin length) → Ear (stage i.castSucc)
  /-- The zeroth stage consists only of the initial vertex and has no arrows. -/
  stage_zero : stage 0 = N.singletonSubnetwork initialVertex
  /-- A successor stage is obtained by adjoining its displayed ear. -/
  stage_succ : ∀ i : Fin length, stage i.succ = (ear i).adjoin
  /-- The final stage is the decomposed subnetwork. -/
  stage_last : stage (Fin.last length) = T

namespace EarDecomposition

variable {T : N.Subnetwork}

/-- Two ear decompositions are equal when their construction data agree. -/
@[ext]
theorem ext {D E : EarDecomposition T} (hlength : D.length = E.length)
    (hinitial : D.initialVertex = E.initialVertex) (hstage : HEq D.stage E.stage)
    (hear : HEq D.ear E.ear) : D = E := by
  cases D
  cases E
  cases hlength
  cases hinitial
  cases hstage
  cases hear
  rfl

/-- The kind (open or closed) of the `i`-th ear in a decomposition. -/
def kindAt (D : EarDecomposition T) (i : Fin D.length) : EarKind :=
  (D.ear i).kind

theorem kindAt_def (D : EarDecomposition T) (i : Fin D.length) :
    D.kindAt i = (D.ear i).kind :=
  (rfl)

/-- The endpoint-indexed walk of the `i`-th ear in a decomposition. -/
def walkAt (D : EarDecomposition T) (i : Fin D.length) : Σ s t : V, ArrowWalk N.Hom s t :=
  (D.ear i).toWalk

theorem walkAt_def (D : EarDecomposition T) (i : Fin D.length) :
    D.walkAt i = (D.ear i).toWalk :=
  (rfl)

/-- Reindex the final subnetwork of an ear decomposition along an equality. -/
@[expose]
def copy {U : N.Subnetwork} (D : EarDecomposition T) (h : T = U) : EarDecomposition U where
  length := D.length
  initialVertex := D.initialVertex
  stage := D.stage
  ear := D.ear
  stage_zero := D.stage_zero
  stage_succ := D.stage_succ
  stage_last := D.stage_last.trans h

@[simp]
theorem copy_rfl (D : EarDecomposition T) : D.copy rfl = D :=
  rfl

@[simp]
theorem copy_length {U : N.Subnetwork} (D : EarDecomposition T) (h : T = U) :
    (D.copy h).length = D.length :=
  rfl

@[simp]
theorem copy_initialVertex {U : N.Subnetwork} (D : EarDecomposition T) (h : T = U) :
    (D.copy h).initialVertex = D.initialVertex :=
  rfl

@[simp]
theorem copy_stage {U : N.Subnetwork} (D : EarDecomposition T) (h : T = U) :
    (D.copy h).stage = D.stage :=
  rfl

/-- Reindexing the final subnetwork does not change the displayed ears. -/
@[simp]
theorem copy_ear {U : N.Subnetwork} (D : EarDecomposition T) (h : T = U) :
    HEq (D.copy h).ear D.ear := by
  subst h
  rfl

@[simp]
theorem copy_kindAt {U : N.Subnetwork} (D : EarDecomposition T) (h : T = U) (i : Fin D.length) :
    (D.copy h).kindAt i = D.kindAt i :=
  (rfl)

@[simp]
theorem copy_walkAt {U : N.Subnetwork} (D : EarDecomposition T) (h : T = U) (i : Fin D.length) :
    (D.copy h).walkAt i = D.walkAt i :=
  (rfl)

/-- The decomposition with no ears whose sole stage is the singleton subnetwork at `x`. -/
@[expose]
def singleton (x : V) : EarDecomposition (N.singletonSubnetwork x) where
  length := 0
  initialVertex := x
  stage _ := N.singletonSubnetwork x
  ear i := Fin.elim0 i
  stage_zero := rfl
  stage_succ i := Fin.elim0 i
  stage_last := rfl

@[simp]
theorem singleton_length (x : V) : (singleton (N := N) x).length = 0 :=
  rfl

@[simp]
theorem singleton_initialVertex (x : V) : (singleton (N := N) x).initialVertex = x :=
  rfl

@[simp]
theorem singleton_stage (x : V) (i : Fin 1) :
    (singleton (N := N) x).stage i = N.singletonSubnetwork x :=
  rfl

attribute [simp] EarDecomposition.stage_zero EarDecomposition.stage_last

/-- Each stage is strictly contained in its successor. -/
theorem stage_castSucc_lt_succ (D : EarDecomposition T) (i : Fin D.length) :
    D.stage i.castSucc < D.stage i.succ := by
  rw [D.stage_succ]
  exact (D.ear i).lt_adjoin

/-- The stages of an ear decomposition grow strictly. -/
theorem strictMono_stage (D : EarDecomposition T) : StrictMono D.stage :=
  Fin.strictMono_iff_lt_succ.2 D.stage_castSucc_lt_succ

/-- Each stage is contained in its successor. -/
theorem stage_le_succ (D : EarDecomposition T) (i : Fin D.length) :
    D.stage i.castSucc ≤ D.stage i.succ := by
  exact (D.stage_castSucc_lt_succ i).le

/-- Prefix subnetworks grow monotonically during an ear decomposition. -/
theorem monotone_stage (D : EarDecomposition T) : Monotone D.stage :=
  D.strictMono_stage.monotone

/-- The initial singleton subnetwork is contained in every stage. -/
theorem stage_zero_le (D : EarDecomposition T) (i : Fin (D.length + 1)) :
    D.stage 0 ≤ D.stage i :=
  D.monotone_stage (Fin.zero_le i)

/-- Every stage is contained in the final subnetwork. -/
theorem stage_le_final (D : EarDecomposition T) (i : Fin (D.length + 1)) :
    D.stage i ≤ T := by
  calc
    D.stage i ≤ D.stage (Fin.last D.length) := D.monotone_stage (Fin.le_last i)
    _ = T := D.stage_last

/-- The subnetwork of the displayed ear is contained in its successor stage. -/
theorem ear_toSubnetwork_le_stage_succ (D : EarDecomposition T) (i : Fin D.length) :
    (D.ear i).toSubnetwork ≤ D.stage i.succ := by
  rw [D.stage_succ]
  exact (D.ear i).toSubnetwork_le_adjoin

/-- The subnetwork of every displayed ear is contained in the final subnetwork. -/
theorem ear_toSubnetwork_le_final (D : EarDecomposition T) (i : Fin D.length) :
    (D.ear i).toSubnetwork ≤ T :=
  (D.ear_toSubnetwork_le_stage_succ i).trans (D.stage_le_final i.succ)

/-- Induction over the stages of an ear decomposition, following the order in which the ears are
adjoined. -/
theorem stage_induction (D : EarDecomposition T) (P : N.Subnetwork → Prop)
    (hzero : P (N.singletonSubnetwork D.initialVertex))
    (hsucc : ∀ i : Fin D.length, P (D.stage i.castSucc) → P ((D.ear i).adjoin))
    (j : Fin (D.length + 1)) : P (D.stage j) := by
  induction j using Fin.induction with
  | zero => simpa [D.stage_zero] using hzero
  | succ i ih =>
    rw [D.stage_succ]
    exact hsucc i ih

/-! ### Appending an ear -/

/-- Append one ear to the end of a directed ear decomposition.

This follows the undirected constructors `TauCeti.SimpleGraph.EarDecomposition.snoc` and
`TauCeti.Graph.EarDecomposition.snoc`. -/
@[expose]
def snoc (D : EarDecomposition T) (P : Ear T) : EarDecomposition P.adjoin where
  length := D.length + 1
  initialVertex := D.initialVertex
  stage := Fin.lastCases P.adjoin D.stage
  ear := Fin.lastCases
    (P.copy (by rw [Fin.lastCases_castSucc, D.stage_last]))
    (fun i ↦ (D.ear i).copy (by rw [Fin.lastCases_castSucc]))
  stage_zero := by
    rw [← Fin.castSucc_zero (n := D.length + 1), Fin.lastCases_castSucc, D.stage_zero]
  stage_succ := by
    let ear' : (i : Fin (D.length + 1)) →
        Ear (Fin.lastCases P.adjoin D.stage i.castSucc) :=
      Fin.lastCases
        (P.copy (by rw [Fin.lastCases_castSucc, D.stage_last]))
        (fun i ↦ (D.ear i).copy (by rw [Fin.lastCases_castSucc]))
    refine Fin.lastCases ?_ (fun i ↦ ?_)
    · rw [Fin.succ_last, Fin.lastCases_last]
      -- Projection reduction exposes the transported last ear at the dependent stage index.
      change P.adjoin = (ear' (Fin.last D.length)).adjoin
      simp only [ear', Fin.lastCases_last, Ear.adjoin_def, Ear.toSubnetwork_copy]
      rw [Fin.lastCases_castSucc, D.stage_last]
    · rw [Fin.succ_castSucc, Fin.lastCases_castSucc, D.stage_succ]
      -- Projection reduction exposes the transported old ear at the dependent stage index.
      change (D.ear i).adjoin = (ear' i.castSucc).adjoin
      simp only [ear', Fin.lastCases_castSucc, Ear.adjoin_def, Ear.toSubnetwork_copy]
  stage_last := Fin.lastCases_last

@[simp]
theorem snoc_length (D : EarDecomposition T) (P : Ear T) :
    (D.snoc P).length = D.length + 1 :=
  rfl

@[simp]
theorem snoc_initialVertex (D : EarDecomposition T) (P : Ear T) :
    (D.snoc P).initialVertex = D.initialVertex :=
  rfl

@[simp]
theorem snoc_stage_castSucc (D : EarDecomposition T) (P : Ear T)
    (i : Fin (D.length + 1)) : (D.snoc P).stage i.castSucc = D.stage i := by
  simp [snoc]

/-- The old ears are unchanged when a new ear is appended. -/
@[simp]
theorem snoc_ear_castSucc (D : EarDecomposition T) (P : Ear T) (i : Fin D.length) :
    HEq ((D.snoc P).ear i.castSucc) (D.ear i) := by
  simp only [snoc, Fin.lastCases_castSucc]
  exact Ear.copy_heq _ _

/-- The last ear of an appended decomposition is the appended ear. -/
@[simp]
theorem snoc_ear_last (D : EarDecomposition T) (P : Ear T) :
    HEq ((D.snoc P).ear (Fin.last D.length)) P := by
  simp only [snoc, Fin.lastCases_last]
  exact Ear.copy_heq _ _

@[simp]
theorem snoc_kindAt_castSucc (D : EarDecomposition T) (P : Ear T) (i : Fin D.length) :
    (D.snoc P).kindAt i.castSucc = D.kindAt i := by
  simp [snoc, kindAt]

@[simp]
theorem snoc_kindAt_last (D : EarDecomposition T) (P : Ear T) :
    (D.snoc P).kindAt (Fin.last D.length) = P.kind := by
  simp [snoc, kindAt]

@[simp]
theorem snoc_walkAt_castSucc (D : EarDecomposition T) (P : Ear T) (i : Fin D.length) :
    (D.snoc P).walkAt i.castSucc = D.walkAt i := by
  simp [snoc, walkAt]

@[simp]
theorem snoc_walkAt_last (D : EarDecomposition T) (P : Ear T) :
    (D.snoc P).walkAt (Fin.last D.length) = P.toWalk := by
  simp [snoc, walkAt]

/-- Stage `(⟨0, h⟩ : Fin D.length).castSucc` is the singleton subnetwork at `initialVertex`. -/
theorem stage_zero_castSucc (D : EarDecomposition T) (h : 0 < D.length) :
    D.stage (⟨0, h⟩ : Fin D.length).castSucc = N.singletonSubnetwork D.initialVertex :=
  (congrArg D.stage (Fin.ext rfl)).trans D.stage_zero

/-- Every vertex of stage `0` is the initial vertex. -/
theorem eq_initialVertex_of_mem_stage_zero (D : EarDecomposition T) {x : V}
    (hx : x ∈ (D.stage 0).vertexSet) : x = D.initialVertex := by
  simpa [D.stage_zero] using hx

/-- The initial vertex belongs to every stage of an ear decomposition. -/
theorem initialVertex_mem_stage (D : EarDecomposition T) (j : Fin (D.length + 1)) :
    D.initialVertex ∈ (D.stage j).vertexSet :=
  (D.stage_zero_le j).1 (by simp [D.stage_zero])

/-- The initial vertex belongs to the decomposed subnetwork. -/
theorem initialVertex_mem (D : EarDecomposition T) : D.initialVertex ∈ T.vertexSet := by
  have h := (D.monotone_stage (Fin.zero_le (Fin.last D.length))).1
  rw [D.stage_zero, D.stage_last] at h
  exact h (by simp)

/-- Any subnetwork admitting an ear decomposition has a nonempty vertex set. -/
theorem vertexSet_nonempty (D : EarDecomposition T) : T.vertexSet.Nonempty :=
  ⟨D.initialVertex, D.initialVertex_mem⟩

/-- The first `k` ears, as an ear decomposition of the `k`-th stage. -/
@[expose]
def prefixDecomposition (D : EarDecomposition T) (k : Fin (D.length + 1)) :
    EarDecomposition (D.stage k) where
  length := k
  initialVertex := D.initialVertex
  stage i := D.stage ⟨i, i.isLt.trans_le (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt))⟩
  ear i := D.ear ⟨i, i.isLt.trans_le (Nat.le_of_lt_succ k.isLt)⟩
  stage_zero := D.stage_zero
  stage_succ i := D.stage_succ ⟨i, i.isLt.trans_le (Nat.le_of_lt_succ k.isLt)⟩
  stage_last := by
    apply congrArg D.stage
    exact Fin.ext rfl

@[simp]
theorem prefixDecomposition_length (D : EarDecomposition T) (k : Fin (D.length + 1)) :
    (D.prefixDecomposition k).length = k :=
  rfl

@[simp]
theorem prefixDecomposition_initialVertex (D : EarDecomposition T)
    (k : Fin (D.length + 1)) :
    (D.prefixDecomposition k).initialVertex = D.initialVertex :=
  rfl

@[simp]
theorem prefixDecomposition_stage (D : EarDecomposition T) (k : Fin (D.length + 1))
    (i : Fin (k + 1)) :
    (D.prefixDecomposition k).stage i =
      D.stage ⟨i, i.isLt.trans_le (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt))⟩ :=
  rfl

@[simp]
theorem prefixDecomposition_ear (D : EarDecomposition T) (k : Fin (D.length + 1))
    (i : Fin k) :
    (D.prefixDecomposition k).ear i =
      D.ear ⟨i, i.isLt.trans_le (Nat.le_of_lt_succ k.isLt)⟩ :=
  rfl

@[simp]
theorem prefixDecomposition_kindAt (D : EarDecomposition T) (k : Fin (D.length + 1))
    (i : Fin k) :
    (D.prefixDecomposition k).kindAt i =
      D.kindAt ⟨i, i.isLt.trans_le (Nat.le_of_lt_succ k.isLt)⟩ :=
  (rfl)

@[simp]
theorem prefixDecomposition_walkAt (D : EarDecomposition T) (k : Fin (D.length + 1))
    (i : Fin k) :
    (D.prefixDecomposition k).walkAt i =
      D.walkAt ⟨i, i.isLt.trans_le (Nat.le_of_lt_succ k.isLt)⟩ :=
  (rfl)

/-! ### Vertex and arrow sets, disjointness, and cycle decompositions -/

/-- The vertex set at stage `j` consists of the initial vertex together with the vertices visited
by the first `j` ears. -/
theorem stage_vertexSet_eq_insert_iUnion (D : EarDecomposition T) (j : Fin (D.length + 1)) :
    (D.stage j).vertexSet =
      insert D.initialVertex (⋃ (i : Fin D.length) (_ : i.val < j.val),
        (D.ear i).toSubnetwork.vertexSet) := by
  induction j using Fin.induction with
  | zero =>
    ext x
    simp [D.stage_zero]
  | succ k ih =>
    ext x
    rw [D.stage_succ, Ear.adjoin_vertexSet, Set.mem_union, ih, Set.mem_insert_iff,
      Set.mem_insert_iff, Set.mem_iUnion, Set.mem_iUnion]
    simp only [Set.mem_iUnion, exists_prop, Fin.val_succ, Nat.lt_succ_iff_lt_or_eq]
    constructor
    · rintro ((rfl | ⟨i, hik, hx⟩) | hx)
      · exact .inl rfl
      · exact .inr ⟨i, .inl hik, hx⟩
      · exact .inr ⟨k, .inr rfl, hx⟩
    · rintro (rfl | ⟨i, hik | hik, hx⟩)
      · exact .inl (.inl rfl)
      · exact .inl (.inr ⟨i, hik, hx⟩)
      · obtain rfl : i = k := Fin.ext hik
        exact .inr hx

/-- The vertex set of the decomposed subnetwork consists of the initial vertex together with the
vertices visited by all ears. -/
theorem vertexSet_eq_insert_iUnion (D : EarDecomposition T) :
    T.vertexSet =
      insert D.initialVertex (⋃ i : Fin D.length, (D.ear i).toSubnetwork.vertexSet) := by
  rw [← congrArg Subnetwork.vertexSet D.stage_last, D.stage_vertexSet_eq_insert_iUnion]
  ext x
  simp

/-- The arrow set at stage `j` is the union of the arrow sets of the first `j` ears. -/
theorem stage_arrowSet_eq_iUnion (D : EarDecomposition T) (j : Fin (D.length + 1)) :
    (D.stage j).arrowSet =
      ⋃ (i : Fin D.length) (_ : i.val < j.val), (D.ear i).toSubnetwork.arrowSet := by
  induction j using Fin.induction with
  | zero =>
    ext a
    simp [D.stage_zero]
  | succ k ih =>
    ext a
    rw [D.stage_succ, Ear.adjoin_arrowSet, Set.mem_union, ih, Set.mem_iUnion, Set.mem_iUnion]
    simp only [Set.mem_iUnion, exists_prop, Fin.val_succ, Nat.lt_succ_iff_lt_or_eq]
    constructor
    · rintro (⟨i, hik, ha⟩ | ha)
      · exact ⟨i, .inl hik, ha⟩
      · exact ⟨k, .inr rfl, ha⟩
    · rintro ⟨i, hik | hik, ha⟩
      · exact .inl ⟨i, hik, ha⟩
      · obtain rfl : i = k := Fin.ext hik
        exact .inr ha

/-- The arrow set of the decomposed subnetwork is the union of the arrow sets of its ears. -/
theorem arrowSet_eq_iUnion (D : EarDecomposition T) :
    T.arrowSet = ⋃ i : Fin D.length, (D.ear i).toSubnetwork.arrowSet := by
  rw [← congrArg Subnetwork.arrowSet D.stage_last, D.stage_arrowSet_eq_iUnion]
  ext a
  simp

/-- Earlier ears are arrow-disjoint from later ears. -/
theorem disjoint_ear_arrowSet_of_lt (D : EarDecomposition T) {i j : Fin D.length} (hij : i < j) :
    Disjoint (D.ear i).toSubnetwork.arrowSet (D.ear j).toSubnetwork.arrowSet := by
  have hle : (D.ear i).toSubnetwork ≤ D.stage j.castSucc :=
    (D.ear_toSubnetwork_le_stage_succ i).trans (D.monotone_stage (Fin.succ_le_castSucc_iff.2 hij))
  exact ((D.ear j).disjoint_arrowSet.mono_right hle.2).symm

/-- Distinct ears in a decomposition have disjoint arrow sets. -/
theorem pairwise_disjoint_ear_arrowSet (D : EarDecomposition T) :
    Pairwise fun i j : Fin D.length ↦
      Disjoint (D.ear i).toSubnetwork.arrowSet (D.ear j).toSubnetwork.arrowSet :=
  fun _ _ hij ↦ (Ne.lt_or_gt hij).elim D.disjoint_ear_arrowSet_of_lt
    fun hji ↦ (D.disjoint_ear_arrowSet_of_lt hji).symm

/-- Every arrow of `T` belongs to a unique ear of any ear decomposition of `T`. -/
theorem existsUnique_ear_of_mem_arrowSet (D : EarDecomposition T) {a : Σ x y, N.Hom x y}
    (ha : a ∈ T.arrowSet) :
    ∃! i : Fin D.length, a ∈ (D.ear i).toSubnetwork.arrowSet := by
  rw [D.arrowSet_eq_iUnion, Set.mem_iUnion] at ha
  obtain ⟨i, hi⟩ := ha
  refine ⟨i, hi, fun j hj ↦ ?_⟩
  by_contra hji
  exact (D.pairwise_disjoint_ear_arrowSet hji).le_bot ⟨hj, hi⟩

/-- Every arrow of the ambient network belongs to a unique ear of an ear decomposition of `⊤`. -/
theorem existsUnique_ear (D : EarDecomposition (⊤ : N.Subnetwork)) (a : Σ x y, N.Hom x y) :
    ∃! i : Fin D.length, a ∈ (D.ear i).toSubnetwork.arrowSet :=
  D.existsUnique_ear_of_mem_arrowSet (by simp)

/-- A full ear decomposition has zero ears if and only if the network has at most one vertex and
no arrows. -/
theorem length_eq_zero_iff (D : EarDecomposition (⊤ : N.Subnetwork)) :
    D.length = 0 ↔ Subsingleton V ∧ IsEmpty (Σ x y, N.Hom x y) := by
  constructor
  · intro h0
    have h0stage : (⊤ : N.Subnetwork) = D.stage 0 :=
      D.stage_last.symm.trans (congrArg D.stage (Fin.ext h0))
    refine ⟨⟨fun x y ↦ ?_⟩, ⟨fun a ↦ ?_⟩⟩
    · have eq_init (z : V) : z = D.initialVertex :=
        D.eq_initialVertex_of_mem_stage_zero
          (h0stage ▸ (by simp : z ∈ (⊤ : N.Subnetwork).vertexSet))
      exact (eq_init x).trans (eq_init y).symm
    · have ha : a ∈ (D.stage 0).arrowSet :=
        h0stage ▸ (by simp : a ∈ (⊤ : N.Subnetwork).arrowSet)
      simp [D.stage_zero] at ha
  · rintro ⟨_, hE⟩
    by_contra hne
    obtain ⟨a, _⟩ := (D.ear ⟨0, Nat.pos_of_ne_zero hne⟩).nonempty_toSubnetwork_arrowSet
    exact hE.false a

/-- If a network has at least one arrow, every ear decomposition of `⊤` has at least one ear. -/
theorem length_pos_of_arrow (D : EarDecomposition (⊤ : N.Subnetwork)) {x y : V} (e : N.Hom x y) :
    0 < D.length :=
  Nat.pos_of_ne_zero fun h0 ↦ (D.length_eq_zero_iff.1 h0).2.false ⟨x, y, e⟩

/-- On a nontrivial vertex type, every ear decomposition of `⊤` has at least one ear. -/
theorem length_pos_of_nontrivial [Nontrivial V] (D : EarDecomposition (⊤ : N.Subnetwork)) :
    0 < D.length :=
  Nat.pos_of_ne_zero fun h0 ↦ not_subsingleton V (D.length_eq_zero_iff.1 h0).1

/-- In any positive-length ear decomposition, ear `0` is a closed ear based at `initialVertex` and
stage `1` is the cycle subnetwork traced by its walk. -/
theorem exists_closedEar_zero (D : EarDecomposition T) (h : 0 < D.length) :
    ∃ C : ClosedEar (D.stage (⟨0, h⟩ : Fin D.length).castSucc),
      D.ear ⟨0, h⟩ = .closed C ∧ C.base = D.initialVertex ∧
        D.stage ⟨1, Nat.succ_lt_succ h⟩ = C.walk.toSubnetwork := by
  have h0 : (⟨0, h⟩ : Fin D.length).castSucc = 0 := Fin.ext rfl
  cases h₀ : D.ear ⟨0, h⟩ with
  | «open» P =>
    exact (P.source_ne_target <|
      (D.eq_initialVertex_of_mem_stage_zero (h0 ▸ P.source_mem)).trans
        (D.eq_initialVertex_of_mem_stage_zero (h0 ▸ P.target_mem)).symm).elim
  | closed C =>
    have hbase : C.base = D.initialVertex :=
      D.eq_initialVertex_of_mem_stage_zero (h0 ▸ C.base_mem)
    refine ⟨C, rfl, hbase, ?_⟩
    have hsucc : D.stage ⟨1, Nat.succ_lt_succ h⟩ = D.stage (⟨0, h⟩ : Fin D.length).succ :=
      congrArg D.stage (Fin.ext rfl)
    rw [hsucc, D.stage_succ, h₀, Ear.adjoin_def, Ear.toSubnetwork_closed]
    refine sup_eq_right.2 (Subnetwork.le_def.2 ⟨?_, ?_⟩)
    · rw [congrArg Subnetwork.vertexSet (D.stage_zero_castSucc h), ← hbase]
      simp
    · rw [congrArg Subnetwork.arrowSet (D.stage_zero_castSucc h)]
      simp

/-- The first ear of any positive-length ear decomposition is closed. -/
theorem kindAt_zero_eq_closed (D : EarDecomposition T) (h : 0 < D.length) :
    D.kindAt ⟨0, h⟩ = .closed := by
  obtain ⟨C, hC, -, -⟩ := D.exists_closedEar_zero h
  rw [D.kindAt_def, hC]
  exact Ear.kind_closed C

/-- The one-ear decomposition of the subnetwork traced by a directed cycle `c`. -/
def ofIsCycle {v₀ : V} {c : ArrowWalk N.Hom v₀ v₀} (hc : c.IsCycle) :
    EarDecomposition c.toSubnetwork :=
  ((singleton (N := N) v₀).snoc (.closed (.ofIsCycle hc))).copy
    (ClosedEar.ofIsCycle_adjoin hc)

@[simp]
theorem ofIsCycle_length {v₀ : V} {c : ArrowWalk N.Hom v₀ v₀} (hc : c.IsCycle) :
    (ofIsCycle (N := N) hc).length = 1 := by
  simp [ofIsCycle]

@[simp]
theorem ofIsCycle_initialVertex {v₀ : V} {c : ArrowWalk N.Hom v₀ v₀} (hc : c.IsCycle) :
    (ofIsCycle (N := N) hc).initialVertex = v₀ := by
  simp [ofIsCycle]

@[simp]
theorem ofIsCycle_stage_one {v₀ : V} {c : ArrowWalk N.Hom v₀ v₀} (hc : c.IsCycle)
    (hj : 1 < (ofIsCycle (N := N) hc).length + 1) :
    (ofIsCycle (N := N) hc).stage ⟨1, hj⟩ = c.toSubnetwork := by
  have hlast : (⟨1, hj⟩ : Fin ((ofIsCycle (N := N) hc).length + 1)) =
      Fin.last (ofIsCycle (N := N) hc).length :=
    Fin.ext (ofIsCycle_length (N := N) hc).symm
  rw [hlast, stage_last]

@[simp]
theorem ofIsCycle_kindAt {v₀ : V} {c : ArrowWalk N.Hom v₀ v₀} (hc : c.IsCycle)
    (i : Fin (ofIsCycle (N := N) hc).length) :
    (ofIsCycle (N := N) hc).kindAt i = .closed := by
  rcases i with ⟨i, hi⟩
  obtain rfl : i = 0 := Nat.lt_one_iff.1 (by simpa [ofIsCycle_length] using hi)
  exact (singleton (N := N) v₀).snoc_kindAt_last (.closed (.ofIsCycle hc))

@[simp]
theorem ofIsCycle_walkAt {v₀ : V} {c : ArrowWalk N.Hom v₀ v₀} (hc : c.IsCycle)
    (i : Fin (ofIsCycle (N := N) hc).length) :
    (ofIsCycle (N := N) hc).walkAt i = ⟨v₀, v₀, c⟩ := by
  rcases i with ⟨i, hi⟩
  obtain rfl : i = 0 := Nat.lt_one_iff.1 (by simpa [ofIsCycle_length] using hi)
  exact (singleton (N := N) v₀).snoc_walkAt_last (.closed (.ofIsCycle hc))

end EarDecomposition

end Network

end TauCeti

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
an ear takes its union with the current subnetwork and strictly enlarges the subnetwork while
preserving strong connectivity. A directed ear decomposition records every prefix subnetwork, the
ear adjoined at each successor stage, and its initial and final subnetworks; decompositions can be
truncated to prefixes or extended by one ear at the end, and their ears partition the arrow set of
the decomposed subnetwork.

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

/-- Adjoining an open ear preserves strong connectivity of the subnetwork. -/
theorem isStronglyConnected_adjoin (P : OpenEar S) (hS : S.IsStronglyConnected) :
    (S ⊔ P.walk.toSubnetwork).IsStronglyConnected :=
  hS.sup_toSubnetwork P.walk P.source_mem P.target_mem

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
theorem walk_toSubnetwork_ofArrow {u v : V} (e : N.Hom u v) (hu : u ∈ S.vertexSet)
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

/-- Adjoining a closed ear preserves strong connectivity of the subnetwork. -/
theorem isStronglyConnected_adjoin (P : ClosedEar S) (hS : S.IsStronglyConnected) :
    (S ⊔ P.walk.toSubnetwork).IsStronglyConnected :=
  hS.sup_toSubnetwork P.walk P.base_mem P.base_mem

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
theorem walk_toSubnetwork_ofLoop {u : V} (e : N.Hom u u) (hu : u ∈ S.vertexSet)
    (he : (⟨u, u, e⟩ : Σ x y, N.Hom x y) ∉ S.arrowSet) :
    (ofLoop e hu he).walk.toSubnetwork = ((ArrowWalk.nil u).cons e).toSubnetwork :=
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
  | .open P => ⟨P.source, P.target, P.walk⟩
  | .closed P => ⟨P.base, P.base, P.walk⟩

@[simp]
theorem toWalk_open (P : OpenEar S) :
    (Ear.open P).toWalk = ⟨P.source, P.target, P.walk⟩ :=
  (rfl)

@[simp]
theorem toWalk_closed (P : ClosedEar S) :
    (Ear.closed P).toWalk = ⟨P.base, P.base, P.walk⟩ :=
  (rfl)

/-- Ears are equal when they have the same kind and the same endpoint-indexed walk. -/
@[ext]
theorem ext {P Q : Ear S} (hkind : P.kind = Q.kind) (hwalk : P.toWalk = Q.toWalk) :
    P = Q := by
  rcases P with ⟨s₁, t₁, w₁, _, _, _, _, _, _⟩ | ⟨b₁, w₁, _, _, _, _⟩ <;>
    rcases Q with ⟨s₂, t₂, w₂, _, _, _, _, _, _⟩ | ⟨b₂, w₂, _, _, _, _⟩
  · simp only [toWalk_open] at hwalk
    injection hwalk with hs htw
    subst hs
    cases eq_of_heq htw
    rfl
  · simp only [kind_open, kind_closed] at hkind
    exact EarKind.noConfusion hkind
  · simp only [kind_open, kind_closed] at hkind
    exact EarKind.noConfusion hkind
  · simp only [toWalk_closed] at hwalk
    injection hwalk with hb hbw
    subst hb
    cases eq_of_heq hbw
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

/-- The walk underlying any ear has positive length. -/
theorem length_pos (P : Ear S) : 0 < P.toWalk.2.2.length := by
  cases P with
  | «open» P => exact P.length_pos
  | closed P => exact P.length_pos

/-- Every ear traverses at least one arrow. -/
theorem arrows_ne_nil (P : Ear S) : P.toWalk.2.2.arrows ≠ [] := by
  cases P with
  | «open» P => exact P.arrows_ne_nil
  | closed P => exact P.arrows_ne_nil

/-- The arrow set of an ear's subnetwork is nonempty. -/
theorem arrowSet_nonempty (P : Ear S) : P.toSubnetwork.arrowSet.Nonempty := by
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ P.arrows_ne_nil
  exact ⟨a, by simpa [P.toSubnetwork_eq_toWalk] using ha⟩

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

/-- Adjoining an ear strictly enlarges the subnetwork. -/
theorem lt_adjoin (P : Ear S) : S < P.adjoin := by
  refine lt_of_le_of_ne P.le_adjoin fun h ↦ ?_
  obtain ⟨a, ha⟩ := P.arrowSet_nonempty
  have haS : a ∈ S.arrowSet := by
    have ha' : a ∈ P.adjoin.arrowSet := P.toSubnetwork_le_adjoin.2 ha
    rwa [← h] at ha'
  exact P.disjoint_arrowSet.le_bot ⟨ha, haS⟩

/-- Adjoining any ear preserves strong connectivity of the subnetwork. -/
theorem isStronglyConnected_adjoin (P : Ear S) (hS : S.IsStronglyConnected) :
    P.adjoin.IsStronglyConnected := by
  cases P with
  | «open» P => exact P.isStronglyConnected_adjoin hS
  | closed P => exact P.isStronglyConnected_adjoin hS

/-- Reindex an ear along an equality of base subnetworks. -/
def copy {S S' : N.Subnetwork} (P : Ear S) (h : S = S') : Ear S' :=
  h ▸ P

@[simp]
theorem copy_rfl (P : Ear S) : P.copy rfl = P :=
  (rfl)

@[simp]
theorem kind_copy {S S' : N.Subnetwork} (P : Ear S) (h : S = S') :
    (P.copy h).kind = P.kind := by
  subst h
  rfl

@[simp]
theorem toWalk_copy {S S' : N.Subnetwork} (P : Ear S) (h : S = S') :
    (P.copy h).toWalk = P.toWalk := by
  subst h
  rfl

@[simp]
theorem toSubnetwork_copy {S S' : N.Subnetwork} (P : Ear S) (h : S = S') :
    (P.copy h).toSubnetwork = P.toSubnetwork := by
  subst h
  rfl

@[simp]
theorem adjoin_copy {S S' : N.Subnetwork} (P : Ear S) (h : S = S') :
    (P.copy h).adjoin = S' ⊔ P.toSubnetwork := by
  subst h
  rfl

end Ear

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

/-- Each stage is contained in its successor. -/
theorem stage_le_succ (D : EarDecomposition T) (i : Fin D.length) :
    D.stage i.castSucc ≤ D.stage i.succ := by
  rw [D.stage_succ]
  exact (D.ear i).le_adjoin

/-- Prefix subnetworks grow monotonically during an ear decomposition. -/
theorem monotone_stage (D : EarDecomposition T) : Monotone D.stage :=
  Fin.monotone_iff_le_succ.2 D.stage_le_succ

/-- The subnetwork of the displayed ear is contained in its successor stage. -/
theorem ear_toSubnetwork_le_stage_succ (D : EarDecomposition T) (i : Fin D.length) :
    (D.ear i).toSubnetwork ≤ D.stage i.succ := by
  rw [D.stage_succ]
  exact (D.ear i).toSubnetwork_le_adjoin

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

/-- Reindex an ear decomposition along an equality of final subnetworks. -/
def copy {T T' : N.Subnetwork} (D : EarDecomposition T) (h : T = T') :
    EarDecomposition T' where
  length := D.length
  initialVertex := D.initialVertex
  stage := D.stage
  ear := D.ear
  stage_zero := D.stage_zero
  stage_succ := D.stage_succ
  stage_last := D.stage_last.trans h

@[simp]
theorem length_copy {T T' : N.Subnetwork} (D : EarDecomposition T) (h : T = T') :
    (D.copy h).length = D.length :=
  (rfl)

@[simp]
theorem initialVertex_copy {T T' : N.Subnetwork} (D : EarDecomposition T) (h : T = T') :
    (D.copy h).initialVertex = D.initialVertex :=
  (rfl)

@[simp]
theorem stage_copy {T T' : N.Subnetwork} (D : EarDecomposition T) (h : T = T')
    (j : Fin (D.length + 1)) :
    (D.copy h).stage (Fin.cast (congrArg (· + 1) (D.length_copy h).symm) j) = D.stage j := by
  dsimp only [copy]
  rw [Fin.cast_eq_self]

@[simp]
theorem kindAt_copy {T T' : N.Subnetwork} (D : EarDecomposition T) (h : T = T')
    (i : Fin D.length) :
    (D.copy h).kindAt (Fin.cast (D.length_copy h).symm i) = D.kindAt i := by
  dsimp only [copy, kindAt]
  rw [Fin.cast_eq_self]

@[simp]
theorem ear_toSubnetwork_copy {T T' : N.Subnetwork} (D : EarDecomposition T) (h : T = T')
    (i : Fin D.length) :
    ((D.copy h).ear (Fin.cast (D.length_copy h).symm i)).toSubnetwork =
      (D.ear i).toSubnetwork := by
  dsimp only [copy]
  rw [Fin.cast_eq_self]

/-- Adjoin one ear at the end of an ear decomposition. -/
def snoc (D : EarDecomposition T) (P : Ear T) : EarDecomposition P.adjoin where
  length := D.length + 1
  initialVertex := D.initialVertex
  stage := Fin.lastCases P.adjoin D.stage
  ear := Fin.lastCases
    (P.copy (by rw [Fin.lastCases_castSucc, D.stage_last]))
    fun i ↦ (D.ear i).copy (by rw [Fin.lastCases_castSucc])
  stage_zero := by
    rw [← Fin.castSucc_zero, Fin.lastCases_castSucc, D.stage_zero]
  stage_succ := Fin.lastCases
    (by simp [Ear.adjoin_def])
    fun i ↦ by
      rw [Fin.succ_castSucc, Fin.lastCases_castSucc, D.stage_succ]
      simp [Ear.adjoin_def]
  stage_last := Fin.lastCases_last

@[simp]
theorem length_snoc (D : EarDecomposition T) (P : Ear T) :
    (D.snoc P).length = D.length + 1 :=
  (rfl)

@[simp]
theorem initialVertex_snoc (D : EarDecomposition T) (P : Ear T) :
    (D.snoc P).initialVertex = D.initialVertex :=
  (rfl)

@[simp]
theorem stage_snoc_castSucc (D : EarDecomposition T) (P : Ear T) (j : Fin (D.length + 1)) :
    (D.snoc P).stage ((Fin.cast (D.length_snoc P).symm j).castSucc) = D.stage j := by
  dsimp only [snoc]
  rw [Fin.cast_eq_self, Fin.lastCases_castSucc]

@[simp]
theorem kindAt_snoc_castSucc (D : EarDecomposition T) (P : Ear T) (i : Fin D.length) :
    (D.snoc P).kindAt (Fin.cast (D.length_snoc P).symm i.castSucc) = D.kindAt i := by
  dsimp only [snoc, kindAt]
  rw [Fin.cast_eq_self]
  simp only [Fin.lastCases_castSucc, Ear.kind_copy]

@[simp]
theorem kindAt_snoc_last (D : EarDecomposition T) (P : Ear T) :
    (D.snoc P).kindAt (Fin.cast (D.length_snoc P).symm (Fin.last D.length)) = P.kind := by
  dsimp only [snoc, kindAt]
  rw [Fin.cast_eq_self]
  simp only [Fin.lastCases_last, Ear.kind_copy]

@[simp]
theorem ear_toSubnetwork_snoc_castSucc (D : EarDecomposition T) (P : Ear T) (i : Fin D.length) :
    ((D.snoc P).ear (Fin.cast (D.length_snoc P).symm i.castSucc)).toSubnetwork =
      (D.ear i).toSubnetwork := by
  dsimp only [snoc]
  rw [Fin.cast_eq_self]
  simp only [Fin.lastCases_castSucc, Ear.toSubnetwork_copy]

@[simp]
theorem ear_toSubnetwork_snoc_last (D : EarDecomposition T) (P : Ear T) :
    ((D.snoc P).ear (Fin.cast (D.length_snoc P).symm (Fin.last D.length))).toSubnetwork =
      P.toSubnetwork := by
  dsimp only [snoc]
  rw [Fin.cast_eq_self]
  simp only [Fin.lastCases_last, Ear.toSubnetwork_copy]

/-- Each stage is strictly contained in its successor. -/
theorem stage_lt_succ (D : EarDecomposition T) (i : Fin D.length) :
    D.stage i.castSucc < D.stage i.succ := by
  rw [D.stage_succ]
  exact (D.ear i).lt_adjoin

/-- Prefix subnetworks grow strictly along an ear decomposition. -/
theorem strictMono_stage (D : EarDecomposition T) : StrictMono D.stage :=
  Fin.strictMono_iff_lt_succ.2 D.stage_lt_succ

/-- Every stage of an ear decomposition is contained in the final subnetwork. -/
theorem stage_le (D : EarDecomposition T) (j : Fin (D.length + 1)) : D.stage j ≤ T :=
  (D.monotone_stage (Fin.le_last j)).trans_eq D.stage_last

/-- The subnetwork of every displayed ear is contained in the final subnetwork. -/
theorem ear_toSubnetwork_le (D : EarDecomposition T) (i : Fin D.length) :
    (D.ear i).toSubnetwork ≤ T :=
  (D.ear_toSubnetwork_le_stage_succ i).trans (D.stage_le i.succ)

/-- The initial vertex belongs to every stage of an ear decomposition. -/
theorem initialVertex_mem_stage (D : EarDecomposition T) (j : Fin (D.length + 1)) :
    D.initialVertex ∈ (D.stage j).vertexSet := by
  have h0 : D.stage 0 ≤ D.stage j := D.monotone_stage (Fin.zero_le j)
  exact h0.1 (by simp [D.stage_zero])

/-- The initial vertex belongs to the decomposed subnetwork. -/
theorem initialVertex_mem (D : EarDecomposition T) : D.initialVertex ∈ T.vertexSet :=
  (D.stage_le 0).1 (D.initialVertex_mem_stage 0)

/-- Any subnetwork admitting an ear decomposition has a nonempty vertex set. -/
theorem vertexSet_nonempty (D : EarDecomposition T) : T.vertexSet.Nonempty :=
  ⟨D.initialVertex, D.initialVertex_mem⟩

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

/-- Every stage of a directed ear decomposition is strongly connected. -/
theorem isStronglyConnected_stage (D : EarDecomposition T) (j : Fin (D.length + 1)) :
    (D.stage j).IsStronglyConnected :=
  D.stage_induction Subnetwork.IsStronglyConnected
    (Subnetwork.isStronglyConnected_singleton D.initialVertex)
    (fun i ih ↦ (D.ear i).isStronglyConnected_adjoin ih) j

/-- Every subnetwork admitting a directed ear decomposition is strongly connected. -/
theorem isStronglyConnected (D : EarDecomposition T) : T.IsStronglyConnected := by
  have h := D.isStronglyConnected_stage (Fin.last D.length)
  rwa [D.stage_last] at h

/-- A network admitting a directed ear decomposition of `⊤` is strongly connected. -/
theorem isStronglyConnected_network (D : EarDecomposition (⊤ : N.Subnetwork)) :
    N.IsStronglyConnected :=
  Subnetwork.isStronglyConnected_top_iff.1 D.isStronglyConnected

end EarDecomposition

end Network

end TauCeti

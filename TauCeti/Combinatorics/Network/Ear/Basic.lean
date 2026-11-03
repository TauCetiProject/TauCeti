/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Subnetwork
public import TauCeti.Combinatorics.Network.Walk

/-!
# Directed ear decompositions

This file packages the data used to build a directed network one ear at a time. An open directed
ear is a directed path whose distinct endpoints already belong to the current subnetwork, while
its internal vertices and all its arrows are new. A closed directed ear is a directed cycle that
meets the current subnetwork only at its base vertex and likewise uses only new arrows. Loops are
therefore closed ears of length one.

The trace of a walk is the subnetwork consisting of exactly its visited vertices and traversed
arrows. Adjoining an ear takes the union of its trace with the current subnetwork. A directed ear
decomposition records every prefix subnetwork, the ear adjoined at each successor stage, and its
initial and final subnetworks. Prefixes are again decompositions, which lets arguments follow the
construction order.

## References

* J. Bang-Jensen and G. Gutin, *Digraphs: Theory, Algorithms and Applications*, Section 5.3.
-/

public section

namespace TauCeti

universe u v w

variable {K : Type w} {V : Type u} [LE K] {N : Network K V}

namespace ArrowWalk

/-- The subnetwork traced by a directed walk: exactly its visited vertices and traversed arrows. -/
def trace {s t : V} (p : ArrowWalk N.Hom s t) : N.Subnetwork where
  vertexSet := {x | x ∈ p.vertices}
  arrowSet := {a | a ∈ p.arrows}
  source_mem := by
    rintro ⟨x, y, e⟩ he
    induction p with
    | nil => simp at he
    | @cons z _ p e' ih =>
      change ⟨x, y, e⟩ ∈ ArrowWalk.arrows (ArrowWalk.cons p e') at he
      change x ∈ ArrowWalk.vertices (ArrowWalk.cons p e')
      rw [arrows_cons, List.mem_append, List.mem_singleton] at he
      rw [vertices_cons, List.concat_eq_append, List.mem_append, List.mem_singleton]
      exact he.elim (fun h ↦ Or.inl (ih h)) fun h ↦ by
        obtain rfl : x = z := (Sigma.mk.inj_iff.1 h).1
        exact Or.inl (@Quiver.Path.end_mem_vertices V ⟨N.Hom⟩ _ _ p)
  target_mem := by
    rintro ⟨x, y, e⟩ he
    rw [vertices_eq_cons_map_target_arrows]
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem (f := fun a ↦ a.2.1) he)

@[simp]
theorem trace_vertexSet {s t : V} (p : ArrowWalk N.Hom s t) :
    p.trace.vertexSet = {x | x ∈ p.vertices} :=
  (rfl)

@[simp]
theorem trace_arrowSet {s t : V} (p : ArrowWalk N.Hom s t) :
    p.trace.arrowSet = {a | a ∈ p.arrows} :=
  (rfl)

theorem source_mem_trace {s t : V} (p : ArrowWalk N.Hom s t) : s ∈ p.trace.vertexSet :=
  @Quiver.Path.start_mem_vertices V ⟨N.Hom⟩ s t p

theorem target_mem_trace {s t : V} (p : ArrowWalk N.Hom s t) : t ∈ p.trace.vertexSet :=
  @Quiver.Path.end_mem_vertices V ⟨N.Hom⟩ s t p

end ArrowWalk

namespace Network

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

/-- The trace subnetwork of an open ear. -/
def trace (P : OpenEar S) : N.Subnetwork :=
  P.walk.trace

@[simp]
theorem trace_vertexSet (P : OpenEar S) : P.trace.vertexSet = {x | x ∈ P.walk.vertices} :=
  ArrowWalk.trace_vertexSet P.walk

@[simp]
theorem trace_arrowSet (P : OpenEar S) : P.trace.arrowSet = {a | a ∈ P.walk.arrows} :=
  ArrowWalk.trace_arrowSet P.walk

/-- The trace of an open ear meets the old vertex set exactly at its two endpoints. -/
theorem mem_trace_vertexSet_and_mem_iff (P : OpenEar S) (x : V) :
    x ∈ P.trace.vertexSet ∧ x ∈ S.vertexSet ↔ x = P.source ∨ x = P.target := by
  constructor
  · rintro ⟨hx, hxS⟩
    by_contra h
    simp only [not_or] at h
    exact P.internal_notMem x hx h.1 h.2 hxS
  · rintro (rfl | rfl)
    · exact ⟨P.walk.source_mem_trace, P.source_mem⟩
    · exact ⟨P.walk.target_mem_trace, P.target_mem⟩

/-- No arrow of an open ear belongs to the old subnetwork. -/
theorem disjoint_arrowSet (P : OpenEar S) : Disjoint P.trace.arrowSet S.arrowSet := by
  rw [Set.disjoint_left]
  exact fun a ha hS ↦ P.arrows_notMem a ha hS

/-- Adjoin an open ear to the current subnetwork. -/
def adjoin (P : OpenEar S) : N.Subnetwork :=
  S ⊔ P.trace

theorem le_adjoin (P : OpenEar S) : S ≤ P.adjoin :=
  Network.Subnetwork.le_union_left _ _

@[simp]
theorem adjoin_vertexSet (P : OpenEar S) :
    P.adjoin.vertexSet = S.vertexSet ∪ {x | x ∈ P.walk.vertices} :=
  (Network.Subnetwork.vertexSet_union S P.trace).trans <|
    congrArg (S.vertexSet ∪ ·) P.trace_vertexSet

@[simp]
theorem adjoin_arrowSet (P : OpenEar S) :
    P.adjoin.arrowSet = S.arrowSet ∪ {a | a ∈ P.walk.arrows} :=
  (Network.Subnetwork.arrowSet_union S P.trace).trans <|
    congrArg (S.arrowSet ∪ ·) P.trace_arrowSet

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
  vertex_mem_of_mem : ∀ x ∈ walk.vertices, x ∈ S.vertexSet → x = base
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

/-- The trace subnetwork of a closed ear. -/
def trace (P : ClosedEar S) : N.Subnetwork :=
  P.walk.trace

@[simp]
theorem trace_vertexSet (P : ClosedEar S) : P.trace.vertexSet = {x | x ∈ P.walk.vertices} :=
  ArrowWalk.trace_vertexSet P.walk

@[simp]
theorem trace_arrowSet (P : ClosedEar S) : P.trace.arrowSet = {a | a ∈ P.walk.arrows} :=
  ArrowWalk.trace_arrowSet P.walk

/-- The trace of a closed ear meets the old vertex set exactly at its base. -/
theorem mem_trace_vertexSet_and_mem_iff (P : ClosedEar S) (x : V) :
    x ∈ P.trace.vertexSet ∧ x ∈ S.vertexSet ↔ x = P.base := by
  constructor
  · exact fun h ↦ P.vertex_mem_of_mem x h.1 h.2
  · rintro rfl
    exact ⟨P.walk.source_mem_trace, P.base_mem⟩

/-- No arrow of a closed ear belongs to the old subnetwork. -/
theorem disjoint_arrowSet (P : ClosedEar S) : Disjoint P.trace.arrowSet S.arrowSet := by
  rw [Set.disjoint_left]
  exact fun a ha hS ↦ P.arrows_notMem a ha hS

/-- Adjoin a closed ear to the current subnetwork. -/
def adjoin (P : ClosedEar S) : N.Subnetwork :=
  S ⊔ P.trace

theorem le_adjoin (P : ClosedEar S) : S ≤ P.adjoin :=
  Network.Subnetwork.le_union_left _ _

@[simp]
theorem adjoin_vertexSet (P : ClosedEar S) :
    P.adjoin.vertexSet = S.vertexSet ∪ {x | x ∈ P.walk.vertices} :=
  (Network.Subnetwork.vertexSet_union S P.trace).trans <|
    congrArg (S.vertexSet ∪ ·) P.trace_vertexSet

@[simp]
theorem adjoin_arrowSet (P : ClosedEar S) :
    P.adjoin.arrowSet = S.arrowSet ∪ {a | a ∈ P.walk.arrows} :=
  (Network.Subnetwork.arrowSet_union S P.trace).trans <|
    congrArg (S.arrowSet ∪ ·) P.trace_arrowSet

end ClosedEar

/-- An open or closed directed ear relative to a subnetwork. -/
inductive Ear (S : N.Subnetwork) where
  /-- An ear with two distinct old endpoints. -/
  | open (ear : OpenEar S)
  /-- An ear based at one old vertex. -/
  | closed (ear : ClosedEar S)

namespace Ear

variable {S : N.Subnetwork}

/-- The trace subnetwork of an ear. -/
def trace : Ear S → N.Subnetwork
  | .open P => P.trace
  | .closed P => P.trace

/-- Adjoin an ear to the current subnetwork. -/
def adjoin : Ear S → N.Subnetwork
  | .open P => P.adjoin
  | .closed P => P.adjoin

@[simp]
theorem trace_open (P : OpenEar S) : (Ear.open P).trace = P.trace :=
  Eq.refl _

@[simp]
theorem trace_closed (P : ClosedEar S) : (Ear.closed P).trace = P.trace :=
  Eq.refl _

@[simp]
theorem adjoin_open (P : OpenEar S) : (Ear.open P).adjoin = P.adjoin :=
  Eq.refl _

@[simp]
theorem adjoin_closed (P : ClosedEar S) : (Ear.closed P).adjoin = P.adjoin :=
  Eq.refl _

/-- Adjoining an ear retains the current subnetwork. -/
theorem le_adjoin (P : Ear S) : S ≤ P.adjoin := by
  cases P with
  | «open» P => exact P.le_adjoin
  | closed P => exact P.le_adjoin

/-- The trace subnetwork of an ear is contained in the subnetwork obtained by adjoining it. -/
theorem trace_le_adjoin (P : Ear S) : P.trace ≤ P.adjoin := by
  cases P with
  | «open» P => exact Network.Subnetwork.le_union_right _ _
  | closed P => exact Network.Subnetwork.le_union_right _ _

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
theorem singleton_stage (x : V) (i : Fin 1) :
    (singleton (N := N) x).stage i = N.singletonSubnetwork x :=
  rfl

/-- The initial stage of a directed ear decomposition. -/
@[simp]
theorem stage_zero_eq (D : EarDecomposition T) :
    D.stage 0 = N.singletonSubnetwork D.initialVertex :=
  D.stage_zero

/-- The final stage of a directed ear decomposition. -/
@[simp]
theorem stage_last_eq (D : EarDecomposition T) : D.stage (Fin.last D.length) = T :=
  D.stage_last

/-- Each stage is contained in its successor. -/
theorem stage_le_succ (D : EarDecomposition T) (i : Fin D.length) :
    D.stage i.castSucc ≤ D.stage i.succ := by
  rw [D.stage_succ]
  exact (D.ear i).le_adjoin

/-- Prefix subnetworks grow monotonically during an ear decomposition. -/
theorem monotone_stage (D : EarDecomposition T) : Monotone D.stage :=
  Fin.monotone_iff_le_succ.2 D.stage_le_succ

/-- The trace of the displayed ear is contained in its successor stage. -/
theorem ear_trace_le_stage_succ (D : EarDecomposition T) (i : Fin D.length) :
    (D.ear i).trace ≤ D.stage i.succ := by
  rw [D.stage_succ]
  exact (D.ear i).trace_le_adjoin

/-- Induction over the stages of an ear decomposition, following the order in which the ears are
adjoined. -/
theorem stage_induction (D : EarDecomposition T) (P : N.Subnetwork → Prop)
    (hzero : P (N.singletonSubnetwork D.initialVertex))
    (hsucc : ∀ i : Fin D.length, P (D.stage i.castSucc) → P ((D.ear i).adjoin))
    (j : Fin (D.length + 1)) : P (D.stage j) := by
  have h : ∀ m (hm : m ≤ D.length), P (D.stage ⟨m, Nat.lt_succ_of_le hm⟩) := by
    intro m hm
    induction m with
    | zero => simpa [D.stage_zero] using hzero
    | succ m ih =>
      have hm' : m < D.length := Nat.lt_of_succ_le hm
      rw [show (⟨m + 1, Nat.lt_succ_of_le hm⟩ : Fin (D.length + 1)) =
        (⟨m, hm'⟩ : Fin D.length).succ by ext; rfl, D.stage_succ]
      exact hsucc ⟨m, hm'⟩ (ih hm'.le)
  exact h j (Nat.le_of_lt_succ j.isLt)

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
theorem prefix_length (D : EarDecomposition T) (k : Fin (D.length + 1)) :
    (D.prefixDecomposition k).length = k :=
  rfl

@[simp]
theorem prefix_initialVertex (D : EarDecomposition T) (k : Fin (D.length + 1)) :
    (D.prefixDecomposition k).initialVertex = D.initialVertex :=
  rfl

@[simp]
theorem prefix_stage (D : EarDecomposition T) (k : Fin (D.length + 1))
    (i : Fin (k + 1)) :
    (D.prefixDecomposition k).stage i =
      D.stage ⟨i, i.isLt.trans_le (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt))⟩ :=
  rfl

@[simp]
theorem prefix_ear (D : EarDecomposition T) (k : Fin (D.length + 1)) (i : Fin k) :
    (D.prefixDecomposition k).ear i =
      D.ear ⟨i, i.isLt.trans_le (Nat.le_of_lt_succ k.isLt)⟩ :=
  rfl

end EarDecomposition

end Network

end TauCeti

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
an ear takes its union with the current subnetwork. A directed ear decomposition records every
prefix subnetwork, the ear adjoined at each successor stage, and its initial and final subnetworks.
Prefixes are again decompositions, which lets arguments follow the construction order.

## References

* J. Bang-Jensen and G. Gutin, *Digraphs: Theory, Algorithms and Applications*, Section 5.3.
-/

public section

namespace TauCeti

universe u v w

variable {K : Type w} {V : Type u} [LE K] {N : Network K V}

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

end ClosedEar

/-- An open or closed directed ear relative to a subnetwork. -/
inductive Ear (S : N.Subnetwork) where
  /-- An ear with two distinct old endpoints. -/
  | open (ear : OpenEar S)
  /-- An ear based at one old vertex. -/
  | closed (ear : ClosedEar S)

namespace Ear

variable {S : N.Subnetwork}

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

end EarDecomposition

end Network

end TauCeti

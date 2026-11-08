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
Prefixes are again decompositions, and `Network.EarDecomposition.snoc` appends one more ear. These
operations let constructions and arguments follow the ears in their natural order.

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

/-- Transporting an ear does not change the subnetwork traced by its walk. -/
@[simp]
theorem toSubnetwork_copy {T : N.Subnetwork} (P : Ear S) (h : S = T) :
    (P.copy h).toSubnetwork = P.toSubnetwork := by
  subst h
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

/-- Adjoining an ear strictly enlarges its base subnetwork. -/
theorem lt_adjoin (P : Ear S) : S < P.adjoin := by
  refine lt_of_le_of_ne P.le_adjoin fun h ↦ ?_
  have hex : ∃ a, a ∈ P.toSubnetwork.arrowSet := by
    cases P with
    | «open» P =>
        obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ (P.walk.arrows_ne_nil P.source_ne_target)
        exact ⟨a, by simpa using ha⟩
    | closed P =>
        obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ P.isCycle.arrows_ne_nil
        exact ⟨a, by simpa using ha⟩
  obtain ⟨a, ha⟩ := hex
  have ha' : a ∈ P.adjoin.arrowSet := by
    rw [adjoin_def, Network.Subnetwork.sup_arrowSet]
    exact Or.inr ha
  exact (Set.disjoint_left.1 P.disjoint_arrowSet ha) (h.symm ▸ ha')

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

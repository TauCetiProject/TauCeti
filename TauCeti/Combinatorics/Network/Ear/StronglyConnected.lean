/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Ear.Basic

/-!
# Directed ear decompositions and strong connectivity

A finite network on a nonempty vertex type is strongly connected exactly when it has a directed
ear decomposition covering every vertex and every arrow. One direction holds without finiteness:
adjoining an open or closed ear to a strongly connected subnetwork keeps it strongly connected, so
every stage of a directed ear decomposition is strongly connected. Conversely, in a strongly
connected network every arrow leaving a subnetwork returns to it along a directed walk, and the
first return closes an ear through that arrow. Since each ear adds a new arrow, finitely many
ears exhaust a finite network, starting from any vertex.

## Main results

* `TauCeti.Network.EarDecomposition.isStronglyConnected_stage`: every stage of a directed ear
  decomposition is strongly connected.
* `TauCeti.Network.Ear.exists_mem_toSubnetwork_arrowSet`: an arrow leaving a subnetwork, whose
  target can return to it, lies on an ear.
* `TauCeti.Network.EarDecomposition.exists_earDecomposition_top_extend`: in a finite strongly
  connected network, every directed ear decomposition of a subnetwork extends to the whole
  network.
* `TauCeti.Network.isStronglyConnected_iff_nonempty_earDecomposition`: the directed ear
  characterization of strong connectivity.

## References

* J. Bang-Jensen and G. Gutin, *Digraphs: Theory, Algorithms and Applications*, 2nd ed.,
  Springer, 2009, Section 5.3.
-/

public section

namespace TauCeti

universe u w

variable {K : Type w} {V : Type u} [LE K] {N : Network K V}

namespace Network

namespace Ear

variable {S : N.Subnetwork}

/-- Adjoining an ear to a strongly connected subnetwork gives a strongly connected subnetwork. -/
theorem isStronglyConnected_adjoin (hS : S.IsStronglyConnected) (P : Ear S) :
    P.adjoin.IsStronglyConnected := by
  rw [adjoin_def]
  cases P with
  | «open» P =>
    rw [toSubnetwork_open]
    exact hS.sup_toSubnetwork P.walk P.source_mem P.target_mem
  | closed P =>
    rw [toSubnetwork_closed]
    exact hS.sup_toSubnetwork P.walk P.base_mem P.base_mem

/-- An arrow from a vertex `x` of `S`, not in `S`, followed by a path that meets `S` only at its
last vertex `b`, is an ear: closed if `b = x` and open otherwise. -/
private theorem exists_mem_toSubnetwork_arrowSet_of_isPath {x y b : V} (e : N.Hom x y)
    (hx : x ∈ S.vertexSet) (he : ⟨x, y, e⟩ ∉ S.arrowSet) (hb : b ∈ S.vertexSet)
    (q : ArrowWalk N.Hom y b) (hq : q.IsPath)
    (hqS : ∀ v ∈ q.vertices, v ∈ S.vertexSet → v = b) :
    ∃ P : Ear S, ⟨x, y, e⟩ ∈ P.toSubnetwork.arrowSet := by
  -- An arrow of `q` in `S` would leave `b`, which a path cannot do.
  have hqA (c : Σ x y, N.Hom x y) (hc : c ∈ q.arrows) : c ∉ S.arrowSet := fun hcS ↦
    hq.fst_ne_of_mem_arrows hc
      (hqS c.1 (q.source_mem_vertices_of_mem_arrows hc) (S.source_mem c hcS))
  have hvert : (((ArrowWalk.nil x).cons e).comp q).vertices = x :: q.vertices :=
    ArrowWalk.vertices_comp ((ArrowWalk.nil x).cons e) q
  have harr : (((ArrowWalk.nil x).cons e).comp q).arrows = ⟨x, y, e⟩ :: q.arrows := by
    simp [ArrowWalk.arrows_comp]
  have hW : ∀ c ∈ (((ArrowWalk.nil x).cons e).comp q).arrows, c ∉ S.arrowSet := by
    rw [harr]
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    exacts [he, hqA c hc]
  have hmem : ⟨x, y, e⟩ ∈ (((ArrowWalk.nil x).cons e).comp q).toSubnetwork.arrowSet := by
    simp [harr]
  by_cases hxb : x = b
  · subst hxb
    refine ⟨.closed ⟨x, ((ArrowWalk.nil x).cons e).comp q, (ArrowWalk.isCycle_def _).2 ⟨?_, ?_⟩,
      hx, ?_, hW⟩, by rw [toSubnetwork_closed]; exact hmem⟩
    · rw [← ArrowWalk.length_arrows, harr]
      simp
    · rw [hvert]
      exact (ArrowWalk.isPath_def q).1 hq
    · rw [hvert]
      intro v hv hvS
      rcases List.mem_cons.1 hv with rfl | hv
      exacts [rfl, hqS v hv hvS]
  · have hxq : x ∉ q.vertices := fun h ↦ hxb (hqS x h hx)
    refine ⟨.open ⟨x, b, ((ArrowWalk.nil x).cons e).comp q, ?_, hx, hb, hxb, ?_, hW⟩,
      by rw [toSubnetwork_open]; exact hmem⟩
    · rw [ArrowWalk.isPath_def, hvert]
      exact List.nodup_cons.2 ⟨hxq, (ArrowWalk.isPath_def q).1 hq⟩
    · rw [hvert]
      intro v hv hvx hvb hvS
      rcases List.mem_cons.1 hv with rfl | hv
      exacts [hvx rfl, hvb (hqS v hv hvS)]

/-- **Ears through a leaving arrow.** An arrow leaving a vertex of `S`, not itself in `S`, whose
target can return to `S` along a directed walk, is traversed by some ear relative to `S`. -/
theorem exists_mem_toSubnetwork_arrowSet {x y z : V} (e : N.Hom x y) (hx : x ∈ S.vertexSet)
    (he : ⟨x, y, e⟩ ∉ S.arrowSet) (hz : z ∈ S.vertexSet) (p : ArrowWalk N.Hom y z) :
    ∃ P : Ear S, ⟨x, y, e⟩ ∈ P.toSubnetwork.arrowSet := by
  by_cases hy : y ∈ S.vertexSet
  · exact exists_mem_toSubnetwork_arrowSet_of_isPath e hx he hy (ArrowWalk.nil y)
      (ArrowWalk.isPath_nil y) (by simp)
  -- Otherwise follow `e` by a path from `y` back to its first vertex `b` in `S`.
  obtain ⟨a, ha, b, hb, q, hq, -, -, hint⟩ :=
    p.exists_isPath_interior_notMem (A := {y}) (B := S.vertexSet) rfl hz
  rw [Set.mem_singleton_iff] at ha
  subst ha
  refine exists_mem_toSubnetwork_arrowSet_of_isPath e hx he hb q hq fun v hv hvS ↦ ?_
  by_contra hvb
  exact (hint v hv (fun h ↦ hy (h ▸ hvS)) hvb).2 hvS

/-- A proper nonempty subnetwork of a strongly connected network admits an ear. -/
theorem nonempty_of_ne_top (hN : @Quiver.IsStronglyConnected V ⟨N.Hom⟩)
    (hne : S.vertexSet.Nonempty) (hS : S ≠ ⊤) : Nonempty (Ear S) := by
  obtain ⟨x, hx⟩ := hne
  -- Some arrow leaves a vertex of `S` without belonging to `S`.
  obtain ⟨⟨u, w, e⟩, hu, he⟩ : ∃ a : Σ x y, N.Hom x y, a.1 ∈ S.vertexSet ∧ a ∉ S.arrowSet := by
    by_contra! h
    have hV (y : V) : y ∈ S.vertexSet :=
      (reachableWithout_empty_iff.2 (hN x y)).mem_of_mem hx
        fun v w e hv _ ↦ S.target_mem ⟨v, w, e⟩ (h _ hv)
    refine hS (Subnetwork.ext ?_ ?_)
    · rw [Subnetwork.vertexSet_top]
      exact Set.eq_univ_of_forall hV
    · rw [Subnetwork.arrowSet_top]
      exact Set.eq_univ_of_forall fun a ↦ h a (hV a.1)
  obtain ⟨p⟩ := hN w u
  exact ⟨(exists_mem_toSubnetwork_arrowSet e hu he hu p).choose⟩

end Ear

namespace EarDecomposition

variable {T : N.Subnetwork}

/-- Every stage of a directed ear decomposition is strongly connected. -/
theorem isStronglyConnected_stage (D : EarDecomposition T) (i : Fin (D.length + 1)) :
    (D.stage i).IsStronglyConnected :=
  D.stage_induction _ (Subnetwork.isStronglyConnected_singleton _)
    (fun _ h ↦ Ear.isStronglyConnected_adjoin h _) i

/-- A subnetwork with a directed ear decomposition is strongly connected. -/
theorem isStronglyConnected (D : EarDecomposition T) : T.IsStronglyConnected := by
  simpa using D.isStronglyConnected_stage (Fin.last D.length)

/-- In a finite strongly connected network, every directed ear decomposition of a subnetwork
extends to one of the whole network: the extension starts at the same vertex and passes through
the same stages before adjoining further ears. -/
theorem exists_earDecomposition_top_extend [Finite V] [∀ v w, Finite (N.Hom v w)]
    (hN : @Quiver.IsStronglyConnected V ⟨N.Hom⟩) (D : EarDecomposition T) :
    ∃ (D' : EarDecomposition (⊤ : N.Subnetwork)) (h : D.length ≤ D'.length),
      D'.initialVertex = D.initialVertex ∧
        ∀ i : Fin (D.length + 1), D'.stage (Fin.castLE (Nat.succ_le_succ h) i) = D.stage i := by
  induction T using WellFoundedGT.induction with
  | _ T ih =>
  by_cases hT : T = ⊤
  · subst hT
    exact ⟨D, le_rfl, rfl, fun i ↦ rfl⟩
  obtain ⟨P⟩ := Ear.nonempty_of_ne_top hN ⟨_, D.initialVertex_mem⟩ hT
  obtain ⟨D', h, hinit, hstage⟩ := ih P.adjoin P.lt_adjoin (D.snoc P)
  refine ⟨D', (Nat.le_succ _).trans h, hinit, fun i ↦ ?_⟩
  rw [← D.snoc_stage_castSucc P i, ← hstage i.castSucc]
  -- Both indices have value `i`; `simp` cannot see this through the length of `D.snoc P`.
  exact congrArg D'.stage (Fin.ext rfl)

end EarDecomposition

/-- **Directed ear decomposition.** A finite network on a nonempty vertex type is strongly
connected exactly when it can be built from a single vertex by adjoining directed open and closed
ears, covering every vertex and arrow. -/
theorem isStronglyConnected_iff_nonempty_earDecomposition [Finite V] [∀ v w, Finite (N.Hom v w)]
    [Nonempty V] :
    @Quiver.IsStronglyConnected V ⟨N.Hom⟩ ↔ Nonempty (EarDecomposition (⊤ : N.Subnetwork)) := by
  refine ⟨fun hN ↦ ?_, fun ⟨D⟩ ↦ Subnetwork.isStronglyConnected_top_iff.1 D.isStronglyConnected⟩
  obtain ⟨D, -⟩ := EarDecomposition.exists_earDecomposition_top_extend hN
    (EarDecomposition.singleton (N := N) (Classical.arbitrary V))
  exact ⟨D⟩

end Network

end TauCeti

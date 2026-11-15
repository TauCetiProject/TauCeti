/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.DirectedCycle
public import TauCeti.Combinatorics.Network.Ear.Basic

/-!
# Directed ear decompositions and strong connectivity

Adjoining a directed open or closed ear to a strongly connected subnetwork preserves strong
connectivity. Consequently, every prefix of a directed ear decomposition is strongly connected,
including its final subnetwork. For a decomposition of the full subnetwork this gives strong
connectivity of the ambient arrow family.

The proof records the two reachability properties of an ear that are useful independently. Every
vertex of an adjoined ear is reachable from an old vertex and can reach an old vertex: for an open
ear, follow a prefix from its old source and a suffix to its old target; for a closed ear, use the
two pieces obtained by splitting its cycle at the chosen vertex.

Conversely, a finite network on a nonempty vertex type is strongly connected only if it has a
directed ear decomposition covering every vertex and every arrow. In a strongly connected network
every arrow leaving a subnetwork returns to it along a directed walk, and the first return closes
an ear through that arrow. Since each ear adds a new arrow, finitely many ears exhaust a finite
network, starting from any vertex or any directed cycle.

## Main results

* `TauCeti.Network.Ear.isStronglyConnected_adjoin`: adjoining an ear preserves strong
  connectivity.
* `TauCeti.Network.EarDecomposition.isStronglyConnected_stage`: every prefix stage is strongly
  connected.
* `TauCeti.Network.EarDecomposition.isStronglyConnected`: the final subnetwork of a directed ear
  decomposition is strongly connected.
* `TauCeti.Network.EarDecomposition.isStronglyConnected_full`: a decomposition of the full
  subnetwork makes the ambient arrow family strongly connected.
* `TauCeti.Network.Ear.exists_mem_toSubnetwork_arrowSet`: an arrow leaving a subnetwork, whose
  target can return to it, lies on an ear.
* `TauCeti.Network.EarDecomposition.exists_earDecomposition_top_extend`: in a finite strongly
  connected network, every directed ear decomposition of a subnetwork extends to the whole
  network, preserving its initial vertex, prefix stages, and displayed ears.
* `TauCeti.Network.isStronglyConnected_iff_exists_earDecomposition_initialVertex`,
  `TauCeti.Network.isStronglyConnected_iff_nonempty_earDecomposition`, and
  `TauCeti.Network.nonempty_earDecomposition_top_iff`: directed ear characterizations of strong
  connectivity.
* `TauCeti.Network.exists_earDecomposition_of_isCycle` and
  `TauCeti.Network.isStronglyConnected_iff_exists_cycle_earDecomposition`: extending a directed
  cycle to a full ear decomposition and the cycle-starting characterization on nontrivial vertex
  types.

## References

* J. Bang-Jensen, G. Gutin, *Digraphs: Theory, Algorithms and Applications*, 2nd ed., Springer,
  2009, Section 5.3.
-/

public section

namespace TauCeti.Network

universe u v w

variable {K : Type w} {V : Type u} [LE K] {N : Network K V}

namespace Ear

variable {S : N.Subnetwork}

/-- Every vertex obtained by adjoining an ear is reachable from some vertex of the old
subnetwork. -/
theorem exists_reachable_from_vertexSet (P : Ear S) {x : V} (hx : x ∈ P.adjoin.vertexSet) :
    ∃ a ∈ S.vertexSet, P.adjoin.Reachable a x := by
  rw [P.adjoin_vertexSet] at hx
  rcases hx with hx | hx
  · exact ⟨x, hx, .refl _ _⟩
  · cases P with
    | «open» P =>
        rw [Ear.toSubnetwork_open] at hx
        have hx' : x ∈ P.walk.vertices := by simpa using hx
        have hP : P.walk.toSubnetwork ≤ (Ear.open P).adjoin := by
          simpa only [Ear.toSubnetwork_open] using (Ear.open P).toSubnetwork_le_adjoin
        exact ⟨P.source, P.source_mem,
          (P.walk.reachable_of_mem_vertices hx').1.mono hP⟩
    | closed P =>
        rw [Ear.toSubnetwork_closed] at hx
        have hx' : x ∈ P.walk.vertices := by simpa using hx
        have hP : P.walk.toSubnetwork ≤ (Ear.closed P).adjoin := by
          simpa only [Ear.toSubnetwork_closed] using (Ear.closed P).toSubnetwork_le_adjoin
        exact ⟨P.base, P.base_mem,
          (P.walk.reachable_of_mem_vertices hx').1.mono hP⟩

/-- Every vertex obtained by adjoining an ear can reach some vertex of the old subnetwork. -/
theorem exists_reachable_to_vertexSet (P : Ear S) {x : V} (hx : x ∈ P.adjoin.vertexSet) :
    ∃ a ∈ S.vertexSet, P.adjoin.Reachable x a := by
  rw [P.adjoin_vertexSet] at hx
  rcases hx with hx | hx
  · exact ⟨x, hx, .refl _ _⟩
  · cases P with
    | «open» P =>
        rw [Ear.toSubnetwork_open] at hx
        have hx' : x ∈ P.walk.vertices := by simpa using hx
        have hP : P.walk.toSubnetwork ≤ (Ear.open P).adjoin := by
          simpa only [Ear.toSubnetwork_open] using (Ear.open P).toSubnetwork_le_adjoin
        exact ⟨P.target, P.target_mem,
          (P.walk.reachable_of_mem_vertices hx').2.mono hP⟩
    | closed P =>
        rw [Ear.toSubnetwork_closed] at hx
        have hx' : x ∈ P.walk.vertices := by simpa using hx
        have hP : P.walk.toSubnetwork ≤ (Ear.closed P).adjoin := by
          simpa only [Ear.toSubnetwork_closed] using (Ear.closed P).toSubnetwork_le_adjoin
        exact ⟨P.base, P.base_mem,
          (P.walk.reachable_of_mem_vertices hx').2.mono hP⟩

/-- Adjoining a directed open or closed ear to a strongly connected subnetwork preserves strong
connectivity. -/
theorem isStronglyConnected_adjoin (P : Ear S)
    (hS : @Quiver.IsStronglyConnected ↥S.vertexSet ⟨S.Hom⟩) :
    @Quiver.IsStronglyConnected ↥P.adjoin.vertexSet ⟨P.adjoin.Hom⟩ := by
  rw [Subnetwork.isStronglyConnected_iff] at hS ⊢
  intro x hx y hy
  obtain ⟨a, ha, hxa⟩ := P.exists_reachable_to_vertexSet hx
  obtain ⟨b, hb, hby⟩ := P.exists_reachable_from_vertexSet hy
  exact hxa.trans ((hS a ha b hb).mono P.le_adjoin) |>.trans hby

end Ear

namespace EarDecomposition

variable {T : N.Subnetwork}

/-- Every prefix stage of a directed ear decomposition is strongly connected. -/
theorem isStronglyConnected_stage (D : EarDecomposition T) (j : Fin (D.length + 1)) :
    @Quiver.IsStronglyConnected ↥(D.stage j).vertexSet ⟨(D.stage j).Hom⟩ := by
  refine D.stage_induction
    (fun S ↦ @Quiver.IsStronglyConnected ↥S.vertexSet ⟨S.Hom⟩) ?_ ?_ j
  · exact Subnetwork.isStronglyConnected_singleton D.initialVertex
  · intro i hi
    exact (D.ear i).isStronglyConnected_adjoin hi

/-- The final subnetwork of every directed ear decomposition is strongly connected. -/
theorem isStronglyConnected (D : EarDecomposition T) :
    @Quiver.IsStronglyConnected ↥T.vertexSet ⟨T.Hom⟩ := by
  rw [← D.stage_last]
  exact D.isStronglyConnected_stage (Fin.last D.length)

/-- A directed ear decomposition of the full subnetwork makes the ambient arrow family strongly
connected. -/
theorem isStronglyConnected_full (D : EarDecomposition (⊤ : N.Subnetwork)) :
    @Quiver.IsStronglyConnected V ⟨N.Hom⟩ := by
  intro x y
  have h := (Subnetwork.isStronglyConnected_iff (⊤ : N.Subnetwork)).1
    D.isStronglyConnected x (by simp) y (by simp)
  exact Subnetwork.reachable_top_iff.1 h

end EarDecomposition

/-! ### Ear decompositions of strongly connected networks -/

namespace Ear

variable {S : N.Subnetwork}

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
    ArrowWalk.vertices_nil_cons_comp e q
  have harr : (((ArrowWalk.nil x).cons e).comp q).arrows = ⟨x, y, e⟩ :: q.arrows := by
    simp [ArrowWalk.arrows_comp]
  have hW : ∀ c ∈ (((ArrowWalk.nil x).cons e).comp q).arrows, c ∉ S.arrowSet := by
    rw [harr]
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    exacts [he, hqA c hc]
  have hmem : ⟨x, y, e⟩ ∈ (((ArrowWalk.nil x).cons e).comp q).toSubnetwork.arrowSet := by
    simp
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

/-- In a finite strongly connected network, every directed ear decomposition of a subnetwork
extends to one of the whole network: the extension starts at the same vertex, passes through the
same stages, and preserves the displayed ears before adjoining further ears. -/
theorem exists_earDecomposition_top_extend [Finite V] [∀ v w, Finite (N.Hom v w)]
    (hN : @Quiver.IsStronglyConnected V ⟨N.Hom⟩) (D : EarDecomposition T) :
    ∃ (D' : EarDecomposition (⊤ : N.Subnetwork)) (h : D.length ≤ D'.length),
      D'.initialVertex = D.initialVertex ∧
        (∀ i : Fin (D.length + 1), D'.stage (Fin.castLE (Nat.succ_le_succ h) i) = D.stage i) ∧
        ∀ i : Fin D.length, HEq (D'.ear (Fin.castLE h i)) (D.ear i) := by
  induction T using WellFoundedGT.induction with
  | _ T ih =>
  by_cases hT : T = ⊤
  · subst hT
    exact ⟨D, le_rfl, rfl, fun _ ↦ rfl, fun _ ↦ HEq.rfl⟩
  obtain ⟨P⟩ := Ear.nonempty_of_ne_top hN ⟨_, D.initialVertex_mem⟩ hT
  obtain ⟨D', h, hinit, hstage, hear⟩ := ih P.adjoin P.lt_adjoin (D.snoc P)
  have h' : D.length ≤ D'.length := (Nat.le_succ _).trans ((D.snoc_length P).symm.trans_le h)
  refine ⟨D', h', hinit.trans (D.snoc_initialVertex P), fun i ↦ ?_, fun i ↦ ?_⟩
  · -- Both indices have value `i`; `simp` cannot see this through the length of `D.snoc P`.
    exact (congrArg D'.stage (Fin.ext rfl)).trans
      ((hstage i.castSucc).trans (D.snoc_stage_castSucc P i))
  · have hi : Fin.castLE h' i = Fin.castLE h i.castSucc := Fin.ext rfl
    rw [hi]
    exact (hear i.castSucc).trans (D.snoc_ear_castSucc P i)

end EarDecomposition

/-- A finite network is strongly connected if and only if `⊤` admits a directed ear decomposition
starting at a prescribed vertex `v₀`. -/
theorem isStronglyConnected_iff_exists_earDecomposition_initialVertex
    [Finite V] [∀ v w, Finite (N.Hom v w)] (v₀ : V) :
    @Quiver.IsStronglyConnected V ⟨N.Hom⟩ ↔
      ∃ D : EarDecomposition (⊤ : N.Subnetwork), D.initialVertex = v₀ := by
  refine ⟨fun hN ↦ ?_, fun ⟨D, _⟩ ↦ D.isStronglyConnected_full⟩
  obtain ⟨D, _, hinit, -, -⟩ := EarDecomposition.exists_earDecomposition_top_extend hN
    (EarDecomposition.singleton (N := N) v₀)
  exact ⟨D, hinit⟩

/-- **Directed ear decomposition.** A finite network on a nonempty vertex type is strongly
connected exactly when it can be built from a single vertex by adjoining directed open and closed
ears, covering every vertex and arrow. -/
theorem isStronglyConnected_iff_nonempty_earDecomposition [Finite V] [∀ v w, Finite (N.Hom v w)]
    [Nonempty V] :
    @Quiver.IsStronglyConnected V ⟨N.Hom⟩ ↔ Nonempty (EarDecomposition (⊤ : N.Subnetwork)) := by
  refine ⟨fun hN ↦ ?_, fun ⟨D⟩ ↦ D.isStronglyConnected_full⟩
  obtain ⟨D, -⟩ := EarDecomposition.exists_earDecomposition_top_extend hN
    (EarDecomposition.singleton (N := N) (Classical.arbitrary V))
  exact ⟨D⟩

/-- On any finite network, `⊤` admits a directed ear decomposition if and only if the vertex type
is nonempty and the network is strongly connected. -/
theorem nonempty_earDecomposition_top_iff [Finite V] [∀ v w, Finite (N.Hom v w)] :
    Nonempty (EarDecomposition (⊤ : N.Subnetwork)) ↔
      Nonempty V ∧ @Quiver.IsStronglyConnected V ⟨N.Hom⟩ :=
  ⟨fun ⟨D⟩ ↦ ⟨⟨D.initialVertex⟩, D.isStronglyConnected_full⟩,
    fun ⟨_, hN⟩ ↦ isStronglyConnected_iff_nonempty_earDecomposition.1 hN⟩

/-- In a finite strongly connected network, every directed cycle appears as the initial closed ear
and first positive stage (`stage 1`) of a directed ear decomposition of `⊤`. -/
theorem exists_earDecomposition_of_isCycle [Finite V] [∀ v w, Finite (N.Hom v w)]
    (hN : @Quiver.IsStronglyConnected V ⟨N.Hom⟩) {v₀ : V} {c : ArrowWalk N.Hom v₀ v₀}
    (hc : c.IsCycle) :
    ∃ (D : EarDecomposition (⊤ : N.Subnetwork)) (h : 0 < D.length),
      D.initialVertex = v₀ ∧ D.kindAt ⟨0, h⟩ = .closed ∧ D.walkAt ⟨0, h⟩ = ⟨v₀, v₀, c⟩ ∧
        D.stage ⟨1, Nat.succ_lt_succ h⟩ = c.toSubnetwork := by
  let D₀ := EarDecomposition.ofIsCycle (N := N) hc
  obtain ⟨D, hlen, hinit, hstage, hear⟩ :=
    EarDecomposition.exists_earDecomposition_top_extend hN D₀
  have hpos : 0 < D.length :=
    (EarDecomposition.ofIsCycle_length (N := N) hc ▸ Nat.zero_lt_one).trans_le hlen
  let i₀ : Fin D₀.length := ⟨0, by simp [D₀]⟩
  have hi : (⟨0, hpos⟩ : Fin D.length) = Fin.castLE hlen i₀ := Fin.ext rfl
  have hwalk : D.walkAt ⟨0, hpos⟩ = ⟨v₀, v₀, c⟩ := by
    rw [hi, EarDecomposition.walkAt_def]
    have hstage₀ : D.stage (Fin.castLE hlen i₀).castSucc = D₀.stage i₀.castSucc :=
      (congrArg D.stage (Fin.ext rfl)).trans (hstage i₀.castSucc)
    exact (Ear.toWalk_eq_of_heq hstage₀ (hear i₀)).trans
      ((D₀.walkAt_def i₀).symm.trans (EarDecomposition.ofIsCycle_walkAt hc i₀))
  refine ⟨D, hpos, hinit.trans (EarDecomposition.ofIsCycle_initialVertex hc),
    D.kindAt_zero_eq_closed hpos, hwalk, ?_⟩
  let j₁ : Fin (D₀.length + 1) := ⟨1, Nat.succ_lt_succ (by simp [D₀])⟩
  have hj : (⟨1, Nat.succ_lt_succ hpos⟩ : Fin (D.length + 1)) =
      Fin.castLE (Nat.succ_le_succ hlen) j₁ := Fin.ext rfl
  rw [hj, hstage j₁]
  exact EarDecomposition.ofIsCycle_stage_one hc j₁.isLt

/-- **Cycle-starting directed ear characterization on nontrivial vertex types.** On a finite
network with at least two vertices, strong connectivity is equivalent to the existence of a
directed cycle of length at least `2` that forms `stage 1` of a directed ear decomposition of
`⊤`. -/
theorem isStronglyConnected_iff_exists_cycle_earDecomposition
    [Nontrivial V] [Finite V] [∀ v w, Finite (N.Hom v w)] :
    @Quiver.IsStronglyConnected V ⟨N.Hom⟩ ↔
      ∃ (v₀ : V) (c : ArrowWalk N.Hom v₀ v₀) (D : EarDecomposition (⊤ : N.Subnetwork))
        (h : 0 < D.length),
        c.IsCycle ∧ 2 ≤ c.length ∧ D.initialVertex = v₀ ∧
          D.stage ⟨1, Nat.succ_lt_succ h⟩ = c.toSubnetwork := by
  refine ⟨fun hN ↦ ?_, fun ⟨_, _, D, _, _, _, _, _⟩ ↦ D.isStronglyConnected_full⟩
  obtain ⟨v₀, c, hc, hlen2⟩ := ArrowWalk.exists_isCycle_two_le_length hN
  obtain ⟨D, hpos, hinit, -, -, hstage1⟩ := exists_earDecomposition_of_isCycle hN hc
  exact ⟨v₀, c, D, hpos, hc, hlen2, hinit, hstage1⟩

end TauCeti.Network

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Ear.Basic

/-!
# Directed ear characterization of strongly connected networks

This file proves the directed ear-decomposition characterization of strong connectivity for finite
networks, allowing parallel arrows, loops (closed ears of length one), and the zero-ear
decomposition of an isolated single vertex:

* `TauCeti.Network.nonempty_ear`: in any strongly connected network (without finiteness
  assumptions), every nonempty proper subnetwork admits an open or closed directed ear.
* `TauCeti.Network.exists_earDecomposition_top_of_earDecomposition`: in a finite strongly connected
  network, every partial ear decomposition extends to a full ear decomposition of `⊤` preserving
  its initial vertex, prefix stages, and ear kinds.
* `TauCeti.Network.isStronglyConnected_iff_nonempty_earDecomposition` and
  `TauCeti.Network.isStronglyConnected_iff_exists_earDecomposition_initialVertex`: a finite
  network on a nonempty vertex type is strongly connected if and only if `⊤` admits a directed ear
  decomposition (and starting at any prescribed vertex).
* `TauCeti.Network.EarDecomposition.exists_closedEar_zero`,
  `TauCeti.Network.EarDecomposition.ofIsCycle`, and
  `TauCeti.Network.isStronglyConnected_iff_exists_cycle_earDecomposition`: relation between the
  initial-vertex convention of `EarDecomposition` and the cycle-starting formulation on
  nontrivial vertex types.

## References

* J. Bang-Jensen and G. Gutin, *Digraphs: Theory, Algorithms and Applications*, 2nd ed.,
  Section 5.3 (Theorem 5.3.2).
-/

public section

namespace TauCeti

universe u v w

variable {K : Type w} {V : Type u} [LE K] {N : Network K V}

namespace Network

/-! ### Existence of a single ear in a strongly connected network -/

/-- In a strongly connected network, every nonempty proper subnetwork has an ambient arrow outside
`S` whose source already belongs to `S`. No finiteness hypothesis on vertices or arrows is
needed. -/
theorem exists_arrow_notMem_of_ne_top {S : N.Subnetwork}
    (hN : @Quiver.IsStronglyConnected V ⟨N.Hom⟩) (hS_ne : S.vertexSet.Nonempty) (hS_top : S ≠ ⊤) :
    ∃ (u y : V) (e : N.Hom u y),
      u ∈ S.vertexSet ∧ (⟨u, y, e⟩ : Σ x w, N.Hom x w) ∉ S.arrowSet := by
  by_cases hV : S.vertexSet = Set.univ
  · have hA : S.arrowSet ≠ Set.univ := fun hA ↦
      hS_top (Subnetwork.ext (hV.trans Subnetwork.vertexSet_top.symm)
        (hA.trans Subnetwork.arrowSet_top.symm))
    obtain ⟨⟨u, y, e⟩, ha⟩ := Set.nonempty_compl.2 hA
    exact ⟨u, y, e, hV.symm ▸ Set.mem_univ u, ha⟩
  · obtain ⟨v₀, hv₀⟩ := hS_ne
    obtain ⟨z, hz⟩ := Set.nonempty_compl.2 hV
    have hreach : ReachableWithout (Q := N.Hom) ∅ v₀ z :=
      reachableWithout_empty_iff.2 ((@Quiver.isStronglyConnected_iff V ⟨N.Hom⟩).1 hN v₀ z)
    by_contra! hall
    refine hz (hreach.mem_of_mem hv₀ fun v w e hv _ ↦ ?_)
    exact S.target_mem ⟨v, w, e⟩ (hall v w e hv)

/-- In a strongly connected network, every nonempty proper subnetwork admits a new open or closed
directed ear. No finiteness hypothesis on vertices or arrows is needed. -/
theorem nonempty_ear {S : N.Subnetwork} (hN : @Quiver.IsStronglyConnected V ⟨N.Hom⟩)
    (hS_ne : S.vertexSet.Nonempty) (hS_top : S ≠ ⊤) : Nonempty (N.Ear S) := by
  obtain ⟨u, y, e, hu, he⟩ := N.exists_arrow_notMem_of_ne_top hN hS_ne hS_top
  by_cases hy : y ∈ S.vertexSet
  · -- Single-arrow case: both endpoints of `e` already lie in `S`.
    by_cases huy : u = y
    · subst huy
      exact ⟨.closed (.ofLoop e hu he)⟩
    · exact ⟨.open (.ofArrow e hu hy huy he)⟩
  · -- Multi-arrow case: trim a walk from `y ∉ S` back into `S` to a path `r` meeting `S` only at
    -- its target `w`, then prepend `e`.
    obtain ⟨q : ArrowWalk N.Hom y u⟩ := (@Quiver.isStronglyConnected_iff V ⟨N.Hom⟩).1 hN y u
    obtain ⟨y', hy', w, hw, r, hr, _, _, hint⟩ :=
      q.exists_isPath_interior_notMem (A := ({y} : Set V)) (B := S.vertexSet) rfl hu
    cases (Set.mem_singleton_iff.1 hy').symm
    have hr_notMem : ∀ v ∈ r.vertices, v ≠ w → v ∉ S.vertexSet := by
      intro v hv hvw
      by_cases hvy : v = y
      · exact hvy ▸ hy
      · exact (hint v hv hvy hvw).2
    have hr_arrows : ∀ b ∈ r.arrows, b ∉ S.arrowSet := fun ⟨x₁, _, _⟩ hb hbS ↦
      hr_notMem x₁ (r.source_mem_vertices_of_mem_arrows hb)
        (hr.source_ne_target_of_mem_arrows hb) (S.source_mem _ hbS)
    let p : ArrowWalk N.Hom u w := ((ArrowWalk.nil u).cons e).comp r
    have hp_verts : p.vertices = u :: r.vertices := ArrowWalk.vertices_cons_nil_comp e r
    have hp_arrows : ∀ b ∈ p.arrows, b ∉ S.arrowSet := by
      intro b hb
      rw [show p.arrows = ⟨u, y, e⟩ :: r.arrows from ArrowWalk.arrows_cons_nil_comp e r,
        List.mem_cons] at hb
      exact hb.elim (fun h ↦ h ▸ he) (hr_arrows b)
    by_cases huw : u = w
    · -- Closed-ear case: `r` returns to `u`, so `p` is a directed cycle meeting `S` only at `u`.
      subst huw
      have hcycle : p.IsCycle := by
        rw [ArrowWalk.isCycle_def, hp_verts]
        exact ⟨by simp [p], (ArrowWalk.isPath_def r).1 hr⟩
      refine ⟨.closed ⟨u, p, hcycle, hu, ?_, hp_arrows⟩⟩
      intro x hx hxS
      rw [hp_verts, List.mem_cons] at hx
      rcases hx with rfl | hx
      · rfl
      · by_contra hxu
        exact hr_notMem x hx hxu hxS
    · -- Open-ear case: `u ≠ w`, so `p` is a directed path between distinct vertices of `S`.
      have hpath : p.IsPath := by
        rw [ArrowWalk.isPath_def, hp_verts, List.nodup_cons]
        exact ⟨fun hur ↦ hr_notMem u hur huw hu, (ArrowWalk.isPath_def r).1 hr⟩
      refine ⟨.open ⟨u, w, p, hpath, hu, hw, huw, ?_, hp_arrows⟩⟩
      intro x hx hxu hxw
      rw [hp_verts, List.mem_cons] at hx
      exact hr_notMem x (hx.resolve_left hxu) hxw

/-! ### Extending partial ear decompositions and characterizing strong connectivity -/

/-- In a finite strongly connected network, any ear decomposition of a subnetwork `S` extends to a
full ear decomposition of `⊤` with the same initial vertex and the same prefix stages, ear kinds,
and ear subnetworks. -/
theorem exists_earDecomposition_top_of_earDecomposition
    [Finite V] [∀ x y, Finite (N.Hom x y)] (hN : @Quiver.IsStronglyConnected V ⟨N.Hom⟩)
    {S : N.Subnetwork} (D : N.EarDecomposition S) :
    ∃ (D' : N.EarDecomposition ⊤) (h : D.length ≤ D'.length),
      D'.initialVertex = D.initialVertex ∧
      (∀ j : Fin (D.length + 1), D'.stage (Fin.castLE (Nat.succ_le_succ h) j) = D.stage j) ∧
      (∀ i : Fin D.length, D'.kindAt (Fin.castLE h i) = D.kindAt i) ∧
      (∀ i : Fin D.length,
        (D'.ear (Fin.castLE h i)).toSubnetwork = (D.ear i).toSubnetwork) := by
  induction S using (wellFounded_gt (α := N.Subnetwork)).induction with
  | h S ih =>
    by_cases hStop : S = ⊤
    · exact ⟨D.copy hStop, le_rfl, D.initialVertex_copy hStop, D.stage_copy hStop,
        D.kindAt_copy hStop, D.ear_toSubnetwork_copy hStop⟩
    · obtain ⟨P⟩ := N.nonempty_ear hN D.vertexSet_nonempty hStop
      obtain ⟨D', h₁, hinit, hstage, hkind, hear⟩ := ih P.adjoin P.lt_adjoin (D.snoc P)
      have h : D.length ≤ D'.length := (Nat.le_succ D.length).trans h₁
      refine ⟨D', h, hinit.trans (D.initialVertex_snoc P), ?_, ?_, ?_⟩
      · intro j
        have hj : Fin.castLE (Nat.succ_le_succ h) j =
            Fin.castLE (Nat.succ_le_succ h₁) j.castSucc := Fin.ext rfl
        rw [hj, hstage j.castSucc, D.stage_snoc_castSucc]
      · intro i
        have hi : Fin.castLE h i = Fin.castLE h₁ i.castSucc := Fin.ext rfl
        rw [hi, hkind i.castSucc, D.kindAt_snoc_castSucc]
      · intro i
        have hi : Fin.castLE h i = Fin.castLE h₁ i.castSucc := Fin.ext rfl
        rw [hi, hear i.castSucc, D.ear_toSubnetwork_snoc_castSucc]

/-- A finite network is strongly connected if and only if `⊤` admits a directed ear decomposition
starting at a prescribed vertex `v₀`. -/
theorem isStronglyConnected_iff_exists_earDecomposition_initialVertex (N : Network K V)
    [Finite V] [∀ x y, Finite (N.Hom x y)] (v₀ : V) :
    @Quiver.IsStronglyConnected V ⟨N.Hom⟩ ↔
      ∃ D : N.EarDecomposition ⊤, D.initialVertex = v₀ := by
  refine ⟨fun hN ↦ ?_, fun ⟨D, _⟩ ↦ D.isStronglyConnected_network⟩
  obtain ⟨D, _, hinit, _, _, _⟩ :=
    N.exists_earDecomposition_top_of_earDecomposition hN (EarDecomposition.singleton (N := N) v₀)
  exact ⟨D, hinit⟩

/-- **Directed ear characterization of strong connectivity.** A finite network on a nonempty vertex
type is strongly connected if and only if `⊤` admits a directed ear decomposition. -/
theorem isStronglyConnected_iff_nonempty_earDecomposition (N : Network K V)
    [Nonempty V] [Finite V] [∀ x y, Finite (N.Hom x y)] :
    @Quiver.IsStronglyConnected V ⟨N.Hom⟩ ↔ Nonempty (N.EarDecomposition ⊤) := by
  obtain ⟨v₀⟩ := ‹Nonempty V›
  rw [N.isStronglyConnected_iff_exists_earDecomposition_initialVertex v₀]
  exact ⟨fun ⟨D, _⟩ ↦ ⟨D⟩, fun ⟨D⟩ ↦
    (N.isStronglyConnected_iff_exists_earDecomposition_initialVertex v₀).1
      D.isStronglyConnected_network⟩

/-- On any finite network, `⊤` admits a directed ear decomposition if and only if the vertex type
is nonempty and the network is strongly connected. -/
theorem nonempty_earDecomposition_top_iff (N : Network K V)
    [Finite V] [∀ x y, Finite (N.Hom x y)] :
    Nonempty (N.EarDecomposition ⊤) ↔ Nonempty V ∧ @Quiver.IsStronglyConnected V ⟨N.Hom⟩ :=
  ⟨fun ⟨D⟩ ↦ ⟨⟨D.initialVertex⟩, D.isStronglyConnected_network⟩,
    fun ⟨_, hN⟩ ↦ N.isStronglyConnected_iff_nonempty_earDecomposition.1 hN⟩

/-! ### Zero-ear decompositions and the cycle-starting formulation -/

namespace EarDecomposition

/-- A full ear decomposition has zero ears if and only if the network has at most one vertex and
no arrows. -/
theorem length_eq_zero_iff (D : N.EarDecomposition ⊤) :
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
    obtain ⟨a, _⟩ := (D.ear ⟨0, Nat.pos_of_ne_zero hne⟩).arrowSet_nonempty
    exact hE.false a

/-- If a network has at least one arrow, every ear decomposition of `⊤` has at least one ear. -/
theorem length_pos_of_arrow (D : N.EarDecomposition ⊤) {x y : V} (e : N.Hom x y) :
    0 < D.length :=
  Nat.pos_of_ne_zero fun h0 ↦ (D.length_eq_zero_iff.1 h0).2.false ⟨x, y, e⟩

/-- On a nontrivial vertex type, every ear decomposition of `⊤` has at least one ear. -/
theorem length_pos_of_nontrivial [Nontrivial V] (D : N.EarDecomposition ⊤) :
    0 < D.length :=
  Nat.pos_of_ne_zero fun h0 ↦ not_subsingleton V (D.length_eq_zero_iff.1 h0).1

/-- In any positive-length ear decomposition, ear `0` is a closed ear based at `initialVertex` and
stage `1` is the cycle subnetwork traced by its walk. -/
theorem exists_closedEar_zero {T : N.Subnetwork} (D : N.EarDecomposition T) (h : 0 < D.length) :
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
theorem kindAt_zero_eq_closed {T : N.Subnetwork} (D : N.EarDecomposition T) (h : 0 < D.length) :
    D.kindAt ⟨0, h⟩ = .closed := by
  obtain ⟨C, hC, -, -⟩ := D.exists_closedEar_zero h
  rw [D.kindAt_def, hC]
  exact Ear.kind_closed C

end EarDecomposition

/-- Any directed cycle `c` at `v₀` is a closed ear over `N.singletonSubnetwork v₀`. -/
def ClosedEar.ofIsCycle {v₀ : V} {c : ArrowWalk N.Hom v₀ v₀} (hc : c.IsCycle) :
    N.ClosedEar (N.singletonSubnetwork v₀) where
  base := v₀
  walk := c
  isCycle := hc
  base_mem := by simp
  eq_base_of_mem _ _ hx := by simpa using hx
  arrows_notMem _ _ ha := by simp at ha

@[simp]
theorem ClosedEar.ofIsCycle_base {v₀ : V} {c : ArrowWalk N.Hom v₀ v₀} (hc : c.IsCycle) :
    (ClosedEar.ofIsCycle (N := N) hc).base = v₀ :=
  (rfl)

@[simp]
theorem ClosedEar.walk_toSubnetwork_ofIsCycle {v₀ : V} {c : ArrowWalk N.Hom v₀ v₀}
    (hc : c.IsCycle) :
    (ClosedEar.ofIsCycle (N := N) hc).walk.toSubnetwork = c.toSubnetwork :=
  (rfl)

@[simp]
theorem ClosedEar.adjoin_ofIsCycle {v₀ : V} {c : ArrowWalk N.Hom v₀ v₀} (hc : c.IsCycle) :
    (Ear.closed (ClosedEar.ofIsCycle (N := N) hc)).adjoin = c.toSubnetwork := by
  rw [Ear.adjoin_def, Ear.toSubnetwork_closed, walk_toSubnetwork_ofIsCycle]
  exact sup_eq_right.2 (Subnetwork.le_def.2 ⟨by simp, by simp⟩)

/-- The one-ear decomposition of the subnetwork traced by a directed cycle `c`. -/
def EarDecomposition.ofIsCycle {v₀ : V} {c : ArrowWalk N.Hom v₀ v₀} (hc : c.IsCycle) :
    N.EarDecomposition c.toSubnetwork :=
  ((EarDecomposition.singleton (N := N) v₀).snoc (.closed (.ofIsCycle hc))).copy
    (ClosedEar.adjoin_ofIsCycle hc)

@[simp]
theorem EarDecomposition.length_ofIsCycle {v₀ : V} {c : ArrowWalk N.Hom v₀ v₀} (hc : c.IsCycle) :
    (EarDecomposition.ofIsCycle (N := N) hc).length = 1 := by
  simp [ofIsCycle]

@[simp]
theorem EarDecomposition.initialVertex_ofIsCycle {v₀ : V} {c : ArrowWalk N.Hom v₀ v₀}
    (hc : c.IsCycle) :
    (EarDecomposition.ofIsCycle (N := N) hc).initialVertex = v₀ := by
  simp [ofIsCycle]

@[simp]
theorem EarDecomposition.stage_one_ofIsCycle {v₀ : V} {c : ArrowWalk N.Hom v₀ v₀}
    (hc : c.IsCycle) :
    (EarDecomposition.ofIsCycle (N := N) hc).stage
      ⟨1, Nat.succ_lt_succ (by simp [length_ofIsCycle])⟩ = c.toSubnetwork := by
  have hlast : (⟨1, Nat.succ_lt_succ (by simp [length_ofIsCycle])⟩ :
      Fin ((EarDecomposition.ofIsCycle (N := N) hc).length + 1)) =
      Fin.last (EarDecomposition.ofIsCycle (N := N) hc).length :=
    Fin.ext (EarDecomposition.length_ofIsCycle (N := N) hc).symm
  rw [hlast, EarDecomposition.stage_last]

/-- In a finite strongly connected network, every directed cycle appears as the first positive
stage (`stage 1`) of a directed ear decomposition of `⊤`. -/
theorem exists_earDecomposition_of_isCycle (N : Network K V)
    [Finite V] [∀ x y, Finite (N.Hom x y)] (hN : @Quiver.IsStronglyConnected V ⟨N.Hom⟩)
    {v₀ : V} {c : ArrowWalk N.Hom v₀ v₀} (hc : c.IsCycle) :
    ∃ (D : N.EarDecomposition ⊤) (h : 0 < D.length),
      D.initialVertex = v₀ ∧ D.kindAt ⟨0, h⟩ = .closed ∧
        D.stage ⟨1, Nat.succ_lt_succ h⟩ = c.toSubnetwork := by
  let D₀ := EarDecomposition.ofIsCycle (N := N) hc
  obtain ⟨D, hlen, hinit, hstage, _, _⟩ :=
    N.exists_earDecomposition_top_of_earDecomposition hN D₀
  have hpos : 0 < D.length :=
    (EarDecomposition.length_ofIsCycle (N := N) hc ▸ Nat.zero_lt_one).trans_le hlen
  refine ⟨D, hpos, hinit.trans (EarDecomposition.initialVertex_ofIsCycle hc),
    D.kindAt_zero_eq_closed hpos, ?_⟩
  let j₁ : Fin (D₀.length + 1) :=
    ⟨1, Nat.succ_lt_succ (by simp [D₀, EarDecomposition.length_ofIsCycle])⟩
  have hj : (⟨1, Nat.succ_lt_succ hpos⟩ : Fin (D.length + 1)) =
      Fin.castLE (Nat.succ_le_succ hlen) j₁ := Fin.ext rfl
  rw [hj, hstage j₁]
  exact EarDecomposition.stage_one_ofIsCycle hc

/-- **Cycle-starting directed ear characterization on nontrivial vertex types.** On a finite
network with at least two vertices, strong connectivity is equivalent to the existence of a
directed cycle of length at least `2` that forms `stage 1` of a directed ear decomposition of
`⊤`. -/
theorem isStronglyConnected_iff_exists_cycle_earDecomposition (N : Network K V)
    [Nontrivial V] [Finite V] [∀ x y, Finite (N.Hom x y)] :
    @Quiver.IsStronglyConnected V ⟨N.Hom⟩ ↔
      ∃ (v₀ : V) (c : ArrowWalk N.Hom v₀ v₀) (D : N.EarDecomposition ⊤) (h : 0 < D.length),
        c.IsCycle ∧ 2 ≤ c.length ∧ D.initialVertex = v₀ ∧
          D.stage ⟨1, Nat.succ_lt_succ h⟩ = c.toSubnetwork := by
  refine ⟨fun hN ↦ ?_, fun ⟨_, _, D, _, _, _, _, _⟩ ↦ D.isStronglyConnected_network⟩
  obtain ⟨v₀, c, hc, hlen2⟩ := ArrowWalk.exists_isCycle_two_le_length hN
  obtain ⟨D, hpos, hinit, _, hstage1⟩ := N.exists_earDecomposition_of_isCycle hN hc
  exact ⟨v₀, c, D, hpos, hc, hlen2, hinit, hstage1⟩

end Network

end TauCeti

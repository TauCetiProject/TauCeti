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

* `TauCeti.Network.IsStronglyConnected.nonempty_ear`: in any strongly connected network (without
  finiteness assumptions), every nonempty proper subnetwork admits an open or closed directed ear.
* `TauCeti.Network.IsStronglyConnected.exists_earDecomposition_top_of_earDecomposition`: in a
  finite strongly connected network, every partial ear decomposition extends to a full ear
  decomposition of `⊤` preserving its initial vertex, prefix stages, and ear kinds.
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
theorem IsStronglyConnected.exists_arrow_notMem_of_ne_top {S : N.Subnetwork}
    (hN : N.IsStronglyConnected) (hS_ne : S.vertexSet.Nonempty) (hS_top : S ≠ ⊤) :
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
      reachableWithout_empty_iff.2 ((N.isStronglyConnected_iff.1 hN) v₀ z)
    by_contra! hall
    refine hz (hreach.mem_of_mem hv₀ fun v w e hv _ ↦ ?_)
    exact S.target_mem ⟨v, w, e⟩ (hall v w e hv)

/-- In a strongly connected network, every nonempty proper subnetwork admits a new open or closed
directed ear. No finiteness hypothesis on vertices or arrows is needed. -/
theorem IsStronglyConnected.nonempty_ear {S : N.Subnetwork} (hN : N.IsStronglyConnected)
    (hS_ne : S.vertexSet.Nonempty) (hS_top : S ≠ ⊤) : Nonempty (N.Ear S) := by
  obtain ⟨u, y, e, hu, he⟩ := hN.exists_arrow_notMem_of_ne_top hS_ne hS_top
  by_cases hy : y ∈ S.vertexSet
  · by_cases huy : u = y
    · subst huy
      exact ⟨.closed (.ofLoop e hu he)⟩
    · exact ⟨.open (.ofArrow e hu hy huy he)⟩
  · obtain ⟨q⟩ := (N.isStronglyConnected_iff.1 hN) y u
    obtain ⟨y', hy', w, hw, r, hr, _, _, hint⟩ :=
      q.exists_isPath_interior_notMem (A := ({y} : Set V)) (B := S.vertexSet) rfl hu
    cases (Set.mem_singleton_iff.1 hy').symm
    have hr_notMem : ∀ v ∈ r.vertices, v ≠ w → v ∉ S.vertexSet := by
      intro v hv hvw
      by_cases hvy : v = y
      · exact hvy ▸ hy
      · exact (hint v hv hvy hvw).2
    have hr_arrows : ∀ b ∈ r.arrows, b ∉ S.arrowSet := by
      intro ⟨x₁, x₂, f⟩ hb hbS
      have hx₁w : x₁ ≠ w := by
        cases r with
        | nil => simp at hb
        | @cons z _ r₀ f₀ =>
          have hw_notMem : w ∉ ArrowWalk.vertices r₀ := hr.target_notMem_vertices_of_cons
          rw [@ArrowWalk.arrows_cons V N.Hom _ _ _ r₀ f₀, List.mem_append,
            List.mem_singleton] at hb
          rcases hb with hb | hb
          · exact fun h ↦ hw_notMem (h ▸ ArrowWalk.source_mem_vertices_of_mem_arrows r₀ hb)
          · injection hb with hxz _
            exact fun h ↦ hw_notMem (h ▸ hxz ▸ @Quiver.Path.end_mem_vertices V ⟨N.Hom⟩ _ _ r₀)
      exact hr_notMem x₁ (r.source_mem_vertices_of_mem_arrows hb) hx₁w (S.source_mem _ hbS)
    let p : ArrowWalk N.Hom u w := ((ArrowWalk.nil u).cons e).comp r
    have hp_verts : p.vertices = u :: r.vertices := by
      have hcomp : p.vertices = ((ArrowWalk.nil u).cons e).vertices.dropLast ++ r.vertices :=
        @Quiver.Path.vertices_comp V ⟨N.Hom⟩ _ _ _ ((ArrowWalk.nil u).cons e) r
      simpa [ArrowWalk.vertices_cons, ArrowWalk.vertices_nil] using hcomp
    have hp_arrows : ∀ b ∈ p.arrows, b ∉ S.arrowSet := by
      intro b hb
      rw [ArrowWalk.arrows_comp, ArrowWalk.arrows_cons, ArrowWalk.arrows_nil] at hb
      simp only [List.nil_append, List.singleton_append, List.mem_cons] at hb
      exact hb.elim (fun h ↦ h ▸ he) (hr_arrows b)
    by_cases huw : u = w
    · subst huw
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
    · have hpath : p.IsPath := by
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
theorem IsStronglyConnected.exists_earDecomposition_top_of_earDecomposition
    [Finite V] [∀ x y, Finite (N.Hom x y)] (hN : N.IsStronglyConnected)
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
    · refine ⟨D.copy hStop, (D.length_copy hStop).ge, D.initialVertex_copy hStop, ?_, ?_, ?_⟩
      · intro j
        have hj : Fin.castLE (Nat.succ_le_succ (D.length_copy hStop).ge) j =
            Fin.cast (congrArg (· + 1) (D.length_copy hStop).symm) j := Fin.ext rfl
        rw [hj, D.stage_copy]
      · intro i
        have hi : Fin.castLE (D.length_copy hStop).ge i =
            Fin.cast (D.length_copy hStop).symm i := Fin.ext rfl
        rw [hi, D.kindAt_copy]
      · intro i
        have hi : Fin.castLE (D.length_copy hStop).ge i =
            Fin.cast (D.length_copy hStop).symm i := Fin.ext rfl
        rw [hi, D.ear_toSubnetwork_copy]
    · obtain ⟨P⟩ := hN.nonempty_ear D.vertexSet_nonempty hStop
      obtain ⟨D', h₁, hinit, hstage, hkind, hear⟩ := ih P.adjoin P.lt_adjoin (D.snoc P)
      have h : D.length ≤ D'.length :=
        (Nat.le_succ D.length).trans ((D.length_snoc P).symm.trans_le h₁)
      refine ⟨D', h, hinit.trans (D.initialVertex_snoc P), ?_, ?_, ?_⟩
      · intro j
        let j₁ : Fin ((D.snoc P).length + 1) := (Fin.cast (D.length_snoc P).symm j).castSucc
        have hj : Fin.castLE (Nat.succ_le_succ h) j =
            Fin.castLE (Nat.succ_le_succ h₁) j₁ := Fin.ext rfl
        rw [hj, hstage j₁, D.stage_snoc_castSucc]
      · intro i
        let i₁ : Fin (D.snoc P).length := Fin.cast (D.length_snoc P).symm i.castSucc
        have hi : Fin.castLE h i = Fin.castLE h₁ i₁ := Fin.ext rfl
        rw [hi, hkind i₁, D.kindAt_snoc_castSucc]
      · intro i
        let i₁ : Fin (D.snoc P).length := Fin.cast (D.length_snoc P).symm i.castSucc
        have hi : Fin.castLE h i = Fin.castLE h₁ i₁ := Fin.ext rfl
        rw [hi, hear i₁, D.ear_toSubnetwork_snoc_castSucc]

/-- A finite network is strongly connected if and only if `⊤` admits a directed ear decomposition
starting at a prescribed vertex `v₀`. -/
theorem isStronglyConnected_iff_exists_earDecomposition_initialVertex
    [Finite V] [∀ x y, Finite (N.Hom x y)] (v₀ : V) :
    N.IsStronglyConnected ↔ ∃ D : N.EarDecomposition ⊤, D.initialVertex = v₀ := by
  refine ⟨fun hN ↦ ?_, fun ⟨D, _⟩ ↦ D.isStronglyConnected_network⟩
  obtain ⟨D, _, hinit, _, _, _⟩ :=
    hN.exists_earDecomposition_top_of_earDecomposition (EarDecomposition.singleton (N := N) v₀)
  exact ⟨D, hinit⟩

/-- **Directed ear characterization of strong connectivity.** A finite network on a nonempty vertex
type is strongly connected if and only if `⊤` admits a directed ear decomposition. -/
theorem isStronglyConnected_iff_nonempty_earDecomposition
    [Nonempty V] [Finite V] [∀ x y, Finite (N.Hom x y)] :
    N.IsStronglyConnected ↔ Nonempty (N.EarDecomposition ⊤) := by
  obtain ⟨v₀⟩ := ‹Nonempty V›
  rw [N.isStronglyConnected_iff_exists_earDecomposition_initialVertex v₀]
  exact ⟨fun ⟨D, _⟩ ↦ ⟨D⟩, fun ⟨D⟩ ↦
    (N.isStronglyConnected_iff_exists_earDecomposition_initialVertex v₀).1
      D.isStronglyConnected_network⟩

/-- On any finite network, `⊤` admits a directed ear decomposition if and only if the vertex type
is nonempty and the network is strongly connected. -/
theorem nonempty_earDecomposition_top_iff [Finite V] [∀ x y, Finite (N.Hom x y)] :
    Nonempty (N.EarDecomposition ⊤) ↔ Nonempty V ∧ N.IsStronglyConnected :=
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
    have hlast : Fin.last D.length = 0 := Fin.ext h0
    have htop : (⊤ : N.Subnetwork) = N.singletonSubnetwork D.initialVertex :=
      D.stage_last.symm.trans ((congrArg D.stage hlast).trans D.stage_zero)
    refine ⟨⟨fun x y ↦ ?_⟩, ⟨fun a ↦ ?_⟩⟩
    · have hx : x ∈ (N.singletonSubnetwork D.initialVertex).vertexSet :=
        htop ▸ (by simp : x ∈ (⊤ : N.Subnetwork).vertexSet)
      have hy : y ∈ (N.singletonSubnetwork D.initialVertex).vertexSet :=
        htop ▸ (by simp : y ∈ (⊤ : N.Subnetwork).vertexSet)
      simp only [Subnetwork.vertexSet_singleton, Set.mem_singleton_iff] at hx hy
      exact hx.trans hy.symm
    · have ha : a ∈ (N.singletonSubnetwork D.initialVertex).arrowSet :=
        htop ▸ (by simp : a ∈ (⊤ : N.Subnetwork).arrowSet)
      simp at ha
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

/-- The first ear of any positive-length ear decomposition is closed. -/
theorem kindAt_zero_eq_closed {T : N.Subnetwork} (D : N.EarDecomposition T) (h : 0 < D.length) :
    D.kindAt ⟨0, h⟩ = .closed := by
  rw [D.kindAt_def]
  cases h₀ : D.ear ⟨0, h⟩ with
  | «open» P =>
    have h0eq : D.stage (⟨0, h⟩ : Fin D.length).castSucc =
        N.singletonSubnetwork D.initialVertex :=
      (congrArg D.stage (Fin.ext rfl)).trans D.stage_zero
    have hs : P.source = D.initialVertex := by
      have hmem := P.source_mem
      rwa [congrArg Subnetwork.vertexSet h0eq, Subnetwork.vertexSet_singleton,
        Set.mem_singleton_iff] at hmem
    have ht : P.target = D.initialVertex := by
      have hmem := P.target_mem
      rwa [congrArg Subnetwork.vertexSet h0eq, Subnetwork.vertexSet_singleton,
        Set.mem_singleton_iff] at hmem
    exact (P.source_ne_target (hs.trans ht.symm)).elim
  | closed C => exact Ear.kind_closed C

/-- In any positive-length ear decomposition, ear `0` is a closed ear based at `initialVertex` and
stage `1` is the cycle subnetwork traced by its walk. -/
theorem exists_closedEar_zero {T : N.Subnetwork} (D : N.EarDecomposition T) (h : 0 < D.length) :
    ∃ C : ClosedEar (D.stage (⟨0, h⟩ : Fin D.length).castSucc),
      D.ear ⟨0, h⟩ = .closed C ∧ C.base = D.initialVertex ∧
        D.stage ⟨1, Nat.succ_lt_succ h⟩ = C.walk.toSubnetwork := by
  have h0eq : D.stage (⟨0, h⟩ : Fin D.length).castSucc =
      N.singletonSubnetwork D.initialVertex :=
    (congrArg D.stage (Fin.ext rfl)).trans D.stage_zero
  cases h₀ : D.ear ⟨0, h⟩ with
  | «open» P =>
    have hs : P.source = D.initialVertex := by
      have hmem := P.source_mem
      rwa [congrArg Subnetwork.vertexSet h0eq, Subnetwork.vertexSet_singleton,
        Set.mem_singleton_iff] at hmem
    have ht : P.target = D.initialVertex := by
      have hmem := P.target_mem
      rwa [congrArg Subnetwork.vertexSet h0eq, Subnetwork.vertexSet_singleton,
        Set.mem_singleton_iff] at hmem
    exact (P.source_ne_target (hs.trans ht.symm)).elim
  | closed C =>
    have hbase : C.base = D.initialVertex := by
      have hmem := C.base_mem
      rwa [congrArg Subnetwork.vertexSet h0eq, Subnetwork.vertexSet_singleton,
        Set.mem_singleton_iff] at hmem
    refine ⟨C, rfl, hbase, ?_⟩
    have hsucc : D.stage ⟨1, Nat.succ_lt_succ h⟩ = D.stage (⟨0, h⟩ : Fin D.length).succ :=
      congrArg D.stage (Fin.ext rfl)
    rw [hsucc, D.stage_succ, h₀, Ear.adjoin_def, Ear.toSubnetwork_closed]
    refine sup_eq_right.2 (Subnetwork.le_def.2 ⟨?_, ?_⟩)
    · rw [congrArg Subnetwork.vertexSet h0eq, ← hbase]
      simp
    · rw [congrArg Subnetwork.arrowSet h0eq]
      simp

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
theorem IsStronglyConnected.exists_earDecomposition_of_isCycle
    [Finite V] [∀ x y, Finite (N.Hom x y)] (hN : N.IsStronglyConnected)
    {v₀ : V} {c : ArrowWalk N.Hom v₀ v₀} (hc : c.IsCycle) :
    ∃ (D : N.EarDecomposition ⊤) (h : 0 < D.length),
      D.initialVertex = v₀ ∧ D.kindAt ⟨0, h⟩ = .closed ∧
        D.stage ⟨1, Nat.succ_lt_succ h⟩ = c.toSubnetwork := by
  let D₀ := EarDecomposition.ofIsCycle (N := N) hc
  obtain ⟨D, hlen, hinit, hstage, _, _⟩ :=
    hN.exists_earDecomposition_top_of_earDecomposition D₀
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

/-- Every strongly connected network on a nontrivial vertex type contains a directed cycle of
length at least `2` (without finiteness assumptions). -/
theorem IsStronglyConnected.exists_isCycle_two_le_length [Nontrivial V]
    (hN : N.IsStronglyConnected) :
    ∃ (v : V) (c : ArrowWalk N.Hom v v), c.IsCycle ∧ 2 ≤ c.length := by
  obtain ⟨u, v, huv⟩ := exists_pair_ne V
  obtain ⟨q₁⟩ := (N.isStronglyConnected_iff.1 hN) u v
  obtain ⟨p₁, hp₁, _⟩ := q₁.exists_isPath_arrows_subset
  cases p₁ with
  | nil => exact (huv rfl).elim
  | @cons x _ p₀ e =>
    have hxv : x ≠ v := fun h ↦
      hp₁.target_notMem_vertices_of_cons (h ▸ @Quiver.Path.end_mem_vertices V ⟨N.Hom⟩ _ _ p₀)
    obtain ⟨q₂⟩ := (N.isStronglyConnected_iff.1 hN) v x
    obtain ⟨r, hr, _⟩ := q₂.exists_isPath_arrows_subset
    have hr_pos : 0 < r.length := by
      cases r with
      | nil => exact (hxv.symm rfl).elim
      | cons _ _ => simp
    refine ⟨v, r.cons e, ?_, Nat.succ_le_succ hr_pos⟩
    rw [ArrowWalk.isCycle_def]
    refine ⟨by simp, ?_⟩
    have hv : (r.cons e).vertices = r.vertices.concat v :=
      @Quiver.Path.vertices_cons V ⟨N.Hom⟩ _ _ _ r e
    have hne : r.vertices ≠ [] := @Quiver.Path.vertices_ne_nil V ⟨N.Hom⟩ _ _ r
    have hh : r.vertices.head hne = v := @Quiver.Path.vertices_head_eq V ⟨N.Hom⟩ _ _ r hne
    have hhead : r.vertices = v :: r.vertices.tail := by
      conv_lhs => rw [← List.cons_head_tail hne, hh]
    have hr_nodup := (ArrowWalk.isPath_def r).1 hr
    rw [hhead, List.nodup_cons] at hr_nodup
    rw [hv, List.concat_eq_append, List.tail_append_of_ne_nil hne]
    exact hr_nodup.2.append (List.nodup_singleton v) (List.disjoint_singleton.2 hr_nodup.1)

/-- **Cycle-starting directed ear characterization on nontrivial vertex types.** On a finite
network with at least two vertices, strong connectivity is equivalent to the existence of a
directed cycle of length at least `2` that forms `stage 1` of a directed ear decomposition of
`⊤`. -/
theorem isStronglyConnected_iff_exists_cycle_earDecomposition
    [Nontrivial V] [Finite V] [∀ x y, Finite (N.Hom x y)] :
    N.IsStronglyConnected ↔
      ∃ (v₀ : V) (c : ArrowWalk N.Hom v₀ v₀) (D : N.EarDecomposition ⊤) (h : 0 < D.length),
        c.IsCycle ∧ 2 ≤ c.length ∧ D.initialVertex = v₀ ∧
          D.stage ⟨1, Nat.succ_lt_succ h⟩ = c.toSubnetwork := by
  refine ⟨fun hN ↦ ?_, fun ⟨_, _, D, _, _, _, _, _⟩ ↦ D.isStronglyConnected_network⟩
  obtain ⟨v₀, c, hc, hlen2⟩ := hN.exists_isCycle_two_le_length
  obtain ⟨D, hpos, hinit, _, hstage1⟩ := hN.exists_earDecomposition_of_isCycle hc
  exact ⟨v₀, c, D, hpos, hc, hlen2, hinit, hstage1⟩

end Network

end TauCeti

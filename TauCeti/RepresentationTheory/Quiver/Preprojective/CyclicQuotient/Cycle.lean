/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.NeighborChoice
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Cyclic.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.GradedOrientation
public import TauCeti.RepresentationTheory.Quiver.Preprojective.PathAlgebra
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Grading
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Necklace
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Connected
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Orientation

/-!
# Positive-degree cyclic classes of preprojective algebras from graph cycles

Every simple cycle of length `d ≥ 3` in a finite simple graph `G` produces a homogeneous element of
path degree `d` outside the commutator submodule, both in the signless preprojective algebra
`Π⁺(G)` and in the additive preprojective algebra `Π_k(Q)` of any orientation `Q` of `G`, over
every nontrivial commutative ring `k`.

The two presentations use distinct mechanisms that both work in arbitrary characteristic:

* For an oriented quiver `Q`, a simple cycle of `G` becomes a directed closed path in a suitable
  reorientation `Reorient Q σ` obtained by directing edges forward along the cycle. In that
  reorientation, the closed path embeds via `TauCeti.pathAlgebraToPreprojective`, whose left inverse
  `TauCeti.preprojectiveToPathAlgebra` maps commutators to commutators in the path algebra, where no
  closed path is a sum of commutators (`TauCeti.PathAlgebra.ofPath_notMem_commutatorSubmodule`).
  Transporting along `TauCeti.reorientPreprojectiveAlgebraEquiv` preserves path degree and
  non-membership in the commutator submodule.
* For the signless preprojective algebra `Π⁺(G)`, the indicator weight of the cycle's vertex
  necklace satisfies `TauCeti.IsSignlessNecklaceWeight` because every backtrack necklace `v w v …`
  either has length `2 < 3` or repeats `v` and is therefore not a rotation of a simple cycle. Thus
  `TauCeti.signlessNecklaceFunctional` separates the cycle walk from the commutator submodule.

## Main results

* `TauCeti.pathAlgebraToPreprojective_ofPath_notMem_commutatorSubmodule`: a directed closed path of
  `Q` embeds outside the commutator submodule of `Π_k(Q)`.
* `TauCeti.exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_reorient_cycle`: a directed
  closed path in a reorientation of `Q` yields a homogeneous cyclic class of the same path length in
  `Π_k(Q)`.
* `TauCeti.exists_mem_preprojectiveGrade_orientedQuiver_notMem_commutatorSubmodule_of_isCycle` and
  `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isCycle`: a simple
  graph cycle of length `d` gives a degree-`d` class outside the commutator submodule in both the
  oriented and signless preprojective algebras.
* `TauCeti.exists_mem_preprojectiveGrade_orientedQuiver_notMem_commutatorSubmodule_of_not_isAcyclic`
  and `TauCeti.exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic`:
  any finite graph that is not acyclic has a nonzero cyclic class in some degree `d ≥ 3`.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u v w

/-! ### Directed cycles in quivers and their reorientations -/

section Quiver

variable (k : Type w) (Q : Type u) [CommRing k] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- A basis path of `Q` maps into the path-length piece of `Π_k(Q)` given by its length. -/
theorem pathAlgebraToPreprojective_ofPath_mem_preprojectiveGrade (x : Quiver.TotalPath Q) :
    pathAlgebraToPreprojective k Q (ofPath x) ∈ preprojectiveGrade k Q x.2.2.length := by
  rw [pathAlgebraToPreprojective_ofPath]
  exact preprojectiveMk_mem_preprojectiveGrade k Q
    (ofPath_mem_grade_of_length (Prefunctor.length_mapTotalPath _root_.Quiver.Symmetrify.of x))

/-- The canonical embedding `kQ →ₐ[k] Π_k(Q)` preserves path-length homogeneity. -/
theorem pathAlgebraToPreprojective_mem_preprojectiveGrade {n : ℕ} {x : pathAlgebra k Q}
    (hx : x ∈ PathAlgebra.grade k Q n) :
    pathAlgebraToPreprojective k Q x ∈ preprojectiveGrade k Q n := by
  rw [grade_eq_span_range] at hx
  induction hx using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨⟨p, hp⟩, rfl⟩ := h
    exact hp ▸ pathAlgebraToPreprojective_ofPath_mem_preprojectiveGrade k Q p
  | zero => rw [map_zero]; exact zero_mem _
  | add _ _ _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r _ _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-- Over a nontrivial commutative ring, no closed path of `Q` maps into the commutator submodule of
`Π_k(Q)`. -/
theorem pathAlgebraToPreprojective_ofPath_notMem_commutatorSubmodule [Nontrivial k] {a : Q}
    (p : _root_.Quiver.Path a a) :
    pathAlgebraToPreprojective k Q (ofPath ⟨a, a, p⟩) ∉
      commutatorSubmodule k (preprojectiveAlgebra k Q) := by
  intro hmem
  have hret := map_mem_commutatorSubmodule (preprojectiveToPathAlgebra k Q) hmem
  rw [preprojectiveToPathAlgebra_pathAlgebraToPreprojective] at hret
  exact ofPath_notMem_commutatorSubmodule k p hret

variable {Q} in
/-- A closed path of length `d` in any reorientation of `Q` produces a homogeneous element of degree
`d` outside the commutator submodule of `Π_k(Q)`. -/
theorem exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_reorient_cycle [Nontrivial k]
    (σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool) {a : Reorient Q σ} (p : _root_.Quiver.Path a a) :
    ∃ x ∈ preprojectiveGrade k Q p.length,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k Q) := by
  let e := reorientPreprojectiveAlgebraEquiv k σ
  let y := pathAlgebraToPreprojective k (Reorient Q σ) (ofPath ⟨a, a, p⟩)
  refine ⟨e y, (reorientPreprojectiveAlgebraEquiv_mem_preprojectiveGrade k σ).mpr
    (pathAlgebraToPreprojective_ofPath_mem_preprojectiveGrade k (Reorient Q σ) ⟨a, a, p⟩), ?_⟩
  intro hmem
  have hy := map_mem_commutatorSubmodule e.symm hmem
  rw [AlgEquiv.symm_apply_apply] at hy
  exact pathAlgebraToPreprojective_ofPath_notMem_commutatorSubmodule k (Reorient Q σ) p hy

end Quiver

/-! ### Simple cycles in oriented quivers -/

section OrientedGraph

variable {V : Type u} {G : SimpleGraph V}

private theorem isCycle_reorient_step (o : Orientation G) {u : V} {c : G.Walk u u}
    (hc : c.IsCycle) :
    ∃ σ : ∀ ⦃i j : OrientedQuiver G o⦄, (i ⟶ j) → Bool,
      ∀ m < c.length, Nonempty
        (reorientVertex σ (OrientedQuiver.vertex G o (c.getVert m)) ⟶
          reorientVertex σ (OrientedQuiver.vertex G o (c.getVert (m + 1)))) := by
  classical
  have hl := hc.three_le_length
  choose! idx hidx using fun s (hs : s ∈ c.support) => hc.exists_getVert_eq hs
  have hinj : ∀ m < c.length, idx (c.getVert m) = m := fun m hm => by
    obtain ⟨hlt, heq⟩ := hidx _ (c.getVert_mem_support m)
    exact hc.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) heq
  let g : V → V := fun s => c.getVert (idx s + 1)
  let φ := (OrientedQuiver.vertexEquiv G o).symm
  refine ⟨fun i j _ => decide (φ j ∈ c.support ∧ g (φ j) = φ i), fun m hm => ?_⟩
  have hg_ne : g (c.getVert (m + 1)) ≠ c.getVert m := by
    obtain hm' | hm' : m + 1 < c.length ∨ m + 1 = c.length := by omega
    · simp only [g, hinj _ hm']
      exact (hc.getVert_sub_one_ne_getVert_add_one (i := m + 1) hm'.le).symm
    · have h0 : idx u = 0 := by simpa using hinj 0 (by omega)
      have hm'' : m = c.length - 1 := by omega
      dsimp only [g]
      rw [hm', SimpleGraph.Walk.getVert_length, h0, hm'']
      exact hc.snd_ne_penultimate
  have hadj : G.Adj (c.getVert m) (c.getVert (m + 1)) := c.adj_getVert_succ hm
  by_cases ho : (⟨(c.getVert m, c.getVert (m + 1)), hadj⟩ : G.Dart) ∈ o
  · refine ⟨reorientKeep _ (OrientedQuiver.arrow G o hadj ho) ?_⟩
    simp only [φ, OrientedQuiver.vertexEquiv_symm_vertex, decide_eq_true_eq, not_and]
    exact fun _ => hg_ne
  · have ho' : (⟨(c.getVert (m + 1), c.getVert m), hadj.symm⟩ : G.Dart) ∈ o :=
      (o.symm_mem_iff_not_mem _).2 ho
    refine ⟨reorientFlip _ (OrientedQuiver.arrow G o hadj.symm ho') ?_⟩
    simp only [φ, OrientedQuiver.vertexEquiv_symm_vertex, decide_eq_true_eq]
    exact ⟨c.getVert_mem_support m, by simp only [g, hinj m hm]⟩

/-- Any simple cycle `c` of a graph `G` becomes a directed closed path of length `c.length` in a
suitable reorientation of `OrientedQuiver G o`. -/
theorem exists_reorient_cycle_of_isCycle (o : Orientation G) {u : V} {c : G.Walk u u}
    (hc : c.IsCycle) :
    ∃ (σ : ∀ ⦃i j : OrientedQuiver G o⦄, (i ⟶ j) → Bool)
      (p : _root_.Quiver.Path (reorientVertex σ (OrientedQuiver.vertex G o u))
        (reorientVertex σ (OrientedQuiver.vertex G o u))),
      p.length = c.length := by
  obtain ⟨σ, hstep⟩ := isCycle_reorient_step o hc
  have hprefix : ∀ m ≤ c.length,
      ∃ p : _root_.Quiver.Path (reorientVertex σ (OrientedQuiver.vertex G o u))
          (reorientVertex σ (OrientedQuiver.vertex G o (c.getVert m))),
        p.length = m := by
    intro m hm
    induction m with
    | zero =>
      rw [SimpleGraph.Walk.getVert_zero]
      exact ⟨_root_.Quiver.Path.nil, rfl⟩
    | succ m ih =>
      obtain ⟨p, hp⟩ := ih (Nat.le_of_succ_le hm)
      obtain ⟨e⟩ := hstep m hm
      exact ⟨p.cons e, by simp [hp]⟩
  obtain ⟨p, hp⟩ := hprefix c.length le_rfl
  have hend : c.getVert c.length = u := SimpleGraph.Walk.getVert_length c
  generalize c.getVert c.length = w at p hend
  subst hend
  exact ⟨σ, p, hp⟩

section FiniteOriented

variable (k : Type w) [CommRing k] [Nontrivial k] [Finite V]

/-- A simple cycle `c` of a finite graph `G` yields a homogeneous element of degree `c.length`
outside the commutator submodule in the preprojective algebra of every orientation of `G`. -/
theorem exists_mem_preprojectiveGrade_orientedQuiver_notMem_commutatorSubmodule_of_isCycle
    (o : Orientation G) {u : V} {c : G.Walk u u} (hc : c.IsCycle)
    [instV : Fintype (OrientedQuiver G o)]
    [instHom : ∀ i j : OrientedQuiver G o, Fintype (i ⟶ j)] :
    ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) c.length,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  obtain ⟨σ, p, hp⟩ := exists_reorient_cycle_of_isCycle o hc
  rw [← hp]
  exact exists_mem_preprojectiveGrade_notMem_commutatorSubmodule_of_reorient_cycle k σ p

/-- If a finite graph `G` is not acyclic, then for every orientation of `G` there exists a degree
`d ≥ 3` in which `preprojectiveGrade` is not contained in the commutator submodule. -/
theorem exists_mem_preprojectiveGrade_orientedQuiver_notMem_commutatorSubmodule_of_not_isAcyclic
    (hc : ¬ G.IsAcyclic) (o : Orientation G)
    [instV : Fintype (OrientedQuiver G o)]
    [instHom : ∀ i j : OrientedQuiver G o, Fintype (i ⟶ j)] :
    ∃ d, 3 ≤ d ∧ ∃ x ∈ preprojectiveGrade k (OrientedQuiver G o) d,
      x ∉ commutatorSubmodule k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  obtain ⟨u, c, hcycle⟩ := SimpleGraph.not_isAcyclic_iff_exists_isCycle.mp hc
  exact ⟨c.length, hcycle.three_le_length,
    exists_mem_preprojectiveGrade_orientedQuiver_notMem_commutatorSubmodule_of_isCycle
      k o hcycle⟩

end FiniteOriented

end OrientedGraph

/-! ### Simple cycles in signless preprojective algebras -/

section SignlessGraph

variable {V : Type u} {G : SimpleGraph V}

private theorem map_vertexEquiv_symm_vertices_walkToPath :
    ∀ {i j : V} (p : G.Walk i j),
      (walkToPath G p).vertices.map (vertexEquiv G).symm = p.support
  | _, _, .nil => by simp [vertexEquiv_symm_vertex]
  | _, _, .cons h p => by
    rw [walkToPath_cons, _root_.Quiver.Path.vertices_comp, _root_.Quiver.Path.vertices_toPath,
      List.dropLast_cons_cons, List.dropLast_singleton, List.cons_append, List.nil_append,
      List.map_cons, vertexEquiv_symm_vertex, map_vertexEquiv_symm_vertices_walkToPath p,
      SimpleGraph.Walk.support_cons]

private theorem nodup_dropLast_support_of_isCycle {u : V} {c : G.Walk u u} (hc : c.IsCycle) :
    c.support.dropLast.Nodup := by
  have hhead : u :: c.support.tail = c.support := by
    simpa only [SimpleGraph.Walk.head_support] using List.cons_head_tail c.support_ne_nil
  have hconcat : c.support.dropLast ++ [u] = u :: c.support.tail := by
    have h1 := List.dropLast_append_getLast c.support_ne_nil
    rw [SimpleGraph.Walk.getLast_support] at h1
    exact h1.trans hhead.symm
  have hperm : (u :: c.support.dropLast).Perm (u :: c.support.tail) := by
    have hp := (List.perm_append_singleton u c.support.dropLast).symm
    rwa [hconcat] at hp
  exact hc.support_nodup.perm hperm.cons_inv.symm

open Classical in
private theorem isSignlessNecklaceWeight_indicator_of_isCycle {k : Type w} [CommRing k]
    [∀ i, Fintype (G.neighborSet i)] {u : V} {c : G.Walk u u} (hc : c.IsCycle) :
    IsSignlessNecklaceWeight G
      (fun s : Cycle V => if s = (c.support.dropLast : Cycle V) then (1 : k) else 0) := by
  have hnodup := nodup_dropLast_support_of_isCycle hc
  have hlen : 3 ≤ c.support.dropLast.length := by
    rw [List.length_dropLast, SimpleGraph.Walk.length_support, Nat.add_sub_cancel]
    exact hc.three_le_length
  rw [isSignlessNecklaceWeight_iff]
  intro v L _ hhead
  refine Finset.sum_eq_zero fun w _ => ?_
  simp only [ite_eq_right_iff]
  intro heq
  have hperm := (Cycle.coe_eq_coe.mp heq).perm
  cases L with
  | nil =>
    have hl := hperm.length_eq
    simp only [List.length_cons, List.length_nil] at hl
    omega
  | cons a L' =>
    have ha : a = v := hhead a rfl
    subst a
    have hnd : (v :: (w : V) :: v :: L').Nodup := hperm.nodup_iff.mpr hnodup
    rw [List.nodup_cons] at hnd
    exact absurd (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hnd.1

section FiniteSignless

variable (k : Type w) [CommRing k] [Nontrivial k] [Finite V] [∀ i, Fintype (G.neighborSet i)]

/-- Over a nontrivial commutative ring, the doubled-quiver path along a simple cycle of a finite
graph `G` lies outside the commutator submodule of the signless preprojective algebra `Π⁺(G)`. -/
theorem signlessPreprojectiveMk_walkToPath_notMem_commutatorSubmodule
    {u : V} {c : G.Walk u u} (hc : c.IsCycle) :
    signlessPreprojectiveMk k (DoubledQuiver G) (ofPath ⟨vertex G u, vertex G u, walkToPath G c⟩) ∉
      commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  classical
  refine signlessPreprojectiveMk_ofPath_notMem_commutatorSubmodule
    (isSignlessNecklaceWeight_indicator_of_isCycle (k := k) hc) (walkToPath G c) ?_
  rw [List.map_dropLast, map_vertexEquiv_symm_vertices_walkToPath]
  simp only [↓reduceIte]
  exact one_ne_zero

/-- A simple cycle `c` of a finite graph `G` yields a homogeneous element of degree `c.length`
outside the commutator submodule of `Π⁺(G)`. -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isCycle
    {u : V} {c : G.Walk u u} (hc : c.IsCycle) :
    ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) c.length,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  refine ⟨signlessPreprojectiveMk k (DoubledQuiver G)
      (ofPath ⟨vertex G u, vertex G u, walkToPath G c⟩), ?_,
    signlessPreprojectiveMk_walkToPath_notMem_commutatorSubmodule k hc⟩
  exact signlessPreprojectiveMk_mem_grade k (DoubledQuiver G)
    (ofPath_mem_grade_of_length (length_walkToPath G c))

/-- If a finite graph `G` is not acyclic, then there exists a degree `d ≥ 3` in which
`signlessPreprojectiveGrade` is not contained in the commutator submodule of `Π⁺(G)`. -/
theorem exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_not_isAcyclic
    (hc : ¬ G.IsAcyclic) :
    ∃ d, 3 ≤ d ∧ ∃ x ∈ signlessPreprojectiveGrade k (DoubledQuiver G) d,
      x ∉ commutatorSubmodule k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  obtain ⟨u, c, hcycle⟩ := SimpleGraph.not_isAcyclic_iff_exists_isCycle.mp hc
  exact ⟨c.length, hcycle.three_le_length,
    exists_mem_signlessPreprojectiveGrade_notMem_commutatorSubmodule_of_isCycle k hcycle⟩

end FiniteSignless

end SignlessGraph

end TauCeti

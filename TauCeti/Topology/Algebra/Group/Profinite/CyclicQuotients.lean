/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.QuotientTower
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Topology.Connected.Separation

/-!
# Topological generators from cyclic quotient towers

A compact subgroup of a group presented by a tower of finite quotients is topologically
cyclic if its images at every level are cyclic. The sets of lifts of generators at individual
levels are nested and compact, so one element generates at all levels simultaneously.

See Ribes and Zalesskii, *Profinite Groups*, §2.3, for the characterization of procyclic groups
by their finite quotients.
-/

public section

namespace TauCeti.FiniteQuotientTower

variable {G : Type*} [Group G] [TopologicalSpace G] {A : ℕ → Type*}
  [∀ n, Group (A n)] [∀ n, TopologicalSpace (A n)] [∀ n, DiscreteTopology (A n)]

/-- A compact set in a quotient tower is determined by its image at each level. -/
theorem mem_iff_forall_mem_q_image (T : FiniteQuotientTower G A) {S : Set G}
    (hS : IsCompact S) {x : G} : x ∈ S ↔ ∀ n, T.q n x ∈ T.q n '' S := by
  refine ⟨fun hx n ↦ ⟨x, hx, rfl⟩, fun h ↦ ?_⟩
  let F (n : ℕ) := S ∩ (T.q n) ⁻¹' {T.q n x}
  have hclosed (n : ℕ) : IsClosed ((T.q n) ⁻¹' {T.q n x}) :=
    (isClosed_discrete _).preimage (T.q n).continuous
  have hmono (n : ℕ) : F (n + 1) ⊆ F n := fun y ⟨hy, hyq⟩ ↦
    ⟨hy, by simpa only [Set.mem_preimage, Set.mem_singleton_iff, T.t_q] using
      (congrArg (T.t (Nat.le_succ n)) (Set.mem_singleton_iff.mp hyq))⟩
  have := T.totallySeparatedSpace
  obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed F hmono
    (fun n ↦ by obtain ⟨y, hy, hyq⟩ := h n; exact ⟨y, hy, hyq⟩)
    (hS.inter_right (hclosed 0)) (fun n ↦ hS.isClosed.inter (hclosed n))
  have hxy : y = x := T.eq_of_forall_q_eq fun n ↦ (Set.mem_iInter.mp hy n).2
  exact hxy ▸ (Set.mem_iInter.mp hy 0).1

/-- A compact subgroup with cyclic images at every level of a quotient tower is the closure
of the integer powers of one of its elements. -/
theorem exists_topologicalClosure_zpowers_eq (T : FiniteQuotientTower G A)
    [IsTopologicalGroup G] {H : Subgroup G} (hH : IsCompact (H : Set G))
    (hcyc : ∀ n, IsCyclic (H.map (T.q n : G →* A n))) :
    ∃ u : G, (Subgroup.zpowers u).topologicalClosure = H := by
  let F (n : ℕ) := (H : Set G) ∩ (T.q n) ⁻¹'
    {v | Subgroup.zpowers v = H.map (T.q n : G →* A n)}
  have hclosed (n : ℕ) : IsClosed ((T.q n) ⁻¹'
      {v | Subgroup.zpowers v = H.map (T.q n : G →* A n)}) :=
    (isClosed_discrete _).preimage (T.q n).continuous
  have hmono (n : ℕ) : F (n + 1) ⊆ F n := by
    intro u ⟨hu, hgen⟩
    refine ⟨hu, ?_⟩
    simpa only [Set.mem_preimage, Set.mem_ofPred_eq, MonoidHom.map_zpowers,
      T.t_q, Subgroup.map_map, T.t_comp_q] using congrArg (Subgroup.map (T.t (Nat.le_succ n))) hgen
  have hnonempty (n : ℕ) : (F n).Nonempty := by
    obtain ⟨a, ha⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (hcyc n)
    obtain ⟨u, hu, hq⟩ := a.property
    refine ⟨u, hu, ?_⟩
    -- Map the generator's cyclic subgroup out of the subtype of the image.
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    have hqa : T.q n u = a.val := hq
    rw [hqa]
    simpa only [MonoidHom.map_zpowers, Subgroup.coe_subtype, Subgroup.map_top,
      Subgroup.range_subtype] using congrArg (Subgroup.map
        (H.map (T.q n : G →* A n)).subtype) ha
  have := T.totallySeparatedSpace
  obtain ⟨u, hu⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed F hmono
    hnonempty (hH.inter_right (hclosed 0)) (fun n ↦ hH.isClosed.inter (hclosed n))
  have hle : (Subgroup.zpowers u).topologicalClosure ≤ H := Subgroup.topologicalClosure_minimal _
    (Subgroup.zpowers_le.mpr (Set.mem_iInter.mp hu 0).1) hH.isClosed
  refine ⟨u, le_antisymm hle fun x hx ↦ ?_⟩
  have hcomp := hH.of_isClosed_subset
    (Subgroup.isClosed_topologicalClosure (Subgroup.zpowers u)) hle
  refine (T.mem_iff_forall_mem_q_image hcomp).2 fun n ↦ ?_
  have hgen : Subgroup.zpowers (T.q n u) = H.map (T.q n : G →* A n) :=
    (Set.mem_iInter.mp hu n).2
  have hx' : T.q n x ∈ (Subgroup.zpowers u).map (T.q n : G →* A n) := by
    rw [MonoidHom.map_zpowers]
    exact hgen.symm ▸ Subgroup.mem_map_of_mem (T.q n : G →* A n) hx
  obtain ⟨y, hy, hqy⟩ := hx'
  exact ⟨y, Subgroup.le_topologicalClosure _ hy, hqy⟩

end TauCeti.FiniteQuotientTower

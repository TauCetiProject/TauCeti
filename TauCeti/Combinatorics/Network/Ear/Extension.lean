/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.ConnectedComponent
public import TauCeti.Combinatorics.Network.Ear.Basic

/-!
# Extending subnetworks by directed ears

Every nonempty proper subnetwork of a strongly connected arrow family admits a directed open or
closed ear. If the subnetwork omits a vertex, follow a first arrow leaving its vertex set and then
return to the old vertices along a path, stopping at the first return. If it contains every vertex
but omits an arrow, that arrow alone is an open ear or a loop ear.

This extension step does not require finiteness. Finiteness is needed only when the step is
iterated to construct a finite ear decomposition.

## References

* J. Bang-Jensen and G. Gutin, *Digraphs: Theory, Algorithms and Applications*, Section 5.3.
-/

public section

namespace TauCeti

universe u v w

variable {K : Type w} {V : Type u} [LE K] {N : Network K V}

namespace Network

namespace Ear

variable {S : N.Subnetwork}

private theorem arrows_notMem_of_path_to_vertexSet {y b : V} (hy : y ∉ S.vertexSet)
    (q : ArrowWalk N.Hom y b) (hq : q.IsPath)
    (hint : ∀ z ∈ q.vertices, z ≠ y → z ≠ b → z ∉ S.vertexSet) :
    ∀ a ∈ q.arrows, a ∉ S.arrowSet := by
  intro a ha haS
  obtain ⟨x, z, e⟩ := a
  have hxS : x ∈ S.vertexSet := S.source_mem ⟨x, z, e⟩ haS
  have hxq : x ∈ q.vertices := q.source_mem_vertices_of_mem_arrows ha
  have hxb : x ≠ b := hq.source_ne_target_of_mem_arrows ha
  have hxnot : x ∉ S.vertexSet := by
    by_cases hxy : x = y
    · exact hxy ▸ hy
    · exact hint x hxq hxy hxb
  exact hxnot hxS

private theorem exists_of_arrow_leaves
    (hN : @Quiver.IsStronglyConnected V ⟨N.Hom⟩) {x y : V} (e : N.Hom x y)
    (hx : x ∈ S.vertexSet) (hy : y ∉ S.vertexSet) : ∃ P : N.Ear S, S < P.adjoin := by
  obtain ⟨r⟩ := hN y x
  obtain ⟨a, ha, b, hb, q, hq, -, -, hint⟩ :=
    ArrowWalk.exists_isPath_interior_notMem (Q := N.Hom) r (A := {y}) (B := S.vertexSet)
      (by simp) hx
  have hay : a = y := Set.mem_singleton_iff.1 ha
  subst a
  have hqA : ∀ a ∈ q.arrows, a ∉ S.arrowSet :=
    arrows_notMem_of_path_to_vertexSet hy q hq fun z hz hzy hzb ↦ (hint z hz hzy hzb).2
  have heA : (⟨x, y, e⟩ : Σ x y, N.Hom x y) ∉ S.arrowSet :=
    fun heS ↦ hy (S.target_mem _ heS)
  let p : ArrowWalk N.Hom x b := ((ArrowWalk.nil x).cons e).comp q
  have hp_vertices : p.vertices = x :: q.vertices := by
    simp [p]
  have hp_arrows : p.arrows = ⟨x, y, e⟩ :: q.arrows := by
    simp [p, ArrowWalk.arrows_comp, ArrowWalk.arrows_cons]
  have hpA : ∀ a ∈ p.arrows, a ∉ S.arrowSet := by
    intro a ha'
    rw [hp_arrows, List.mem_cons] at ha'
    rcases ha' with rfl | ha'
    · exact heA
    · exact hqA a ha'
  have hinter : ∀ z ∈ p.vertices, z ≠ x → z ≠ b → z ∉ S.vertexSet := by
    intro z hz hzx hzb
    rw [hp_vertices, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact (hzx rfl).elim
    · by_cases hzy : z = y
      · exact hzy ▸ hy
      · exact (hint z hz hzy hzb).2
  by_cases hxb : x = b
  · subst b
    have hpCycle : p.IsCycle := by
      rw [ArrowWalk.isCycle_def, hp_vertices]
      exact ⟨by simp [p], by simpa [ArrowWalk.isPath_def] using hq⟩
    let P : N.Ear S := .closed
      { base := x
        walk := p
        isCycle := hpCycle
        base_mem := hx
        eq_base_of_mem := fun z hz hzS ↦ by
          by_contra hzx
          exact hinter z hz hzx hzx hzS
        arrows_notMem := hpA }
    refine ⟨P, lt_of_le_of_ne P.le_adjoin ?_⟩
    intro hEq
    have heMem : (⟨x, y, e⟩ : Σ x y, N.Hom x y) ∈ P.adjoin.arrowSet := by
      rw [P.adjoin_arrowSet]
      exact Or.inr (by simp [P, hp_arrows])
    exact heA (hEq ▸ heMem)
  · have hxq : x ∉ q.vertices := by
      intro hxq
      by_cases hxy : x = y
      · exact hy (hxy ▸ hx)
      · exact (hint x hxq hxy hxb).2 hx
    have hpPath : p.IsPath := by
      rw [ArrowWalk.isPath_def, hp_vertices, List.nodup_cons]
      exact ⟨hxq, (ArrowWalk.isPath_def q).1 hq⟩
    let P : N.Ear S := .«open»
      { source := x
        target := b
        walk := p
        isPath := hpPath
        source_mem := hx
        target_mem := hb
        source_ne_target := hxb
        internal_notMem := hinter
        arrows_notMem := hpA }
    refine ⟨P, lt_of_le_of_ne P.le_adjoin ?_⟩
    intro hEq
    have heMem : (⟨x, y, e⟩ : Σ x y, N.Hom x y) ∈ P.adjoin.arrowSet := by
      rw [P.adjoin_arrowSet]
      exact Or.inr (by simp [P, hp_arrows])
    exact heA (hEq ▸ heMem)

end Ear

/-- Every nonempty proper subnetwork of a strongly connected arrow family can be strictly
extended by adjoining one directed open or closed ear. -/
theorem _root_.Quiver.IsStronglyConnected.exists_ear_of_lt_top
    (hN : @Quiver.IsStronglyConnected V ⟨N.Hom⟩) {S : N.Subnetwork}
    (hS : S.vertexSet.Nonempty) (hproper : S < ⊤) : ∃ P : N.Ear S, S < P.adjoin := by
  by_cases hV : S.vertexSet = Set.univ
  · have hA : S.arrowSet ≠ Set.univ := by
      intro hA
      exact hproper.ne (Subnetwork.ext (hV.trans Subnetwork.vertexSet_top.symm)
        (hA.trans Subnetwork.arrowSet_top.symm))
    obtain ⟨⟨x, y, e⟩, he⟩ := (Set.ne_univ_iff_exists_notMem S.arrowSet).1 hA
    have hx : x ∈ S.vertexSet := hV.symm ▸ Set.mem_univ x
    have hy : y ∈ S.vertexSet := hV.symm ▸ Set.mem_univ y
    by_cases hxy : x = y
    · subst y
      let P : N.Ear S := .closed
        { base := x
          walk := (ArrowWalk.nil x).cons e
          isCycle := ArrowWalk.isCycle_loop e
          base_mem := hx
          eq_base_of_mem := by simp
          arrows_notMem := by simpa using he }
      refine ⟨P, lt_of_le_of_ne P.le_adjoin ?_⟩
      intro hEq
      exact he (hEq ▸ (by simp [P]))
    · let P : N.Ear S := .«open»
        { source := x
          target := y
          walk := (ArrowWalk.nil x).cons e
          isPath := by simpa [ArrowWalk.isPath_def] using hxy
          source_mem := hx
          target_mem := hy
          source_ne_target := hxy
          internal_notMem := by simp
          arrows_notMem := by simpa using he }
      refine ⟨P, lt_of_le_of_ne P.le_adjoin ?_⟩
      intro hEq
      exact he (hEq ▸ (by simp [P]))
  · obtain ⟨z, hz⟩ := (Set.ne_univ_iff_exists_notMem S.vertexSet).1 hV
    obtain ⟨s, hs⟩ := hS
    obtain ⟨p⟩ := hN s z
    obtain ⟨x, y, e, -, hx, hy⟩ :=
      ArrowWalk.exists_mem_arrows_source_mem_target_notMem (Q := N.Hom) p hs hz
    exact Ear.exists_of_arrow_leaves hN e hx hy

end Network

end TauCeti

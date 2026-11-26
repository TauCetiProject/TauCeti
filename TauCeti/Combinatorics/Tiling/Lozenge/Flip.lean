/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Tiling
import Mathlib.Tactic.FinCases

/-!
# Flips of lozenge tilings

The six faces round a vertex `v` form a unit hexagon, which has two tilings: the three edges
`(v,3)`, `(v−e₁,1)`, `(v−e₂,2)` (`highFlipEdges v`) and the three edges `(v,1)`, `(v,2)`,
`(v−e₃,3)` (`lowFlipEdges v`). A flip at `v` replaces one of these triples in a set of edges by the
other; on a tiling, replacing the first by the second lowers the height at `v` by one. Each triple
has one edge of each direction, so a flip removes one lozenge of each type and adds one of each
type.

## Main definitions

* `TauCeti.highFlipEdges v`, `TauCeti.lowFlipEdges v`: the two tilings of the hexagon round `v`.
* `TauCeti.IsFlipAt v M M'`: `M'` is obtained from `M` by a flip at `v`.
* `TauCeti.IsFlip M M'`: `M'` is obtained from `M` by a flip at some vertex.

## Main statements

* `TauCeti.isTiling_highFlipEdges`, `TauCeti.isTiling_lowFlipEdges`: both triples tile the six
  faces round `v`.
* `TauCeti.existsUnique_mem_highFlipEdges_k`, `TauCeti.existsUnique_mem_lowFlipEdges_k`: each
  triple has exactly one edge of each direction.
* `TauCeti.IsFlipAt.symm`: if `M` contains at most one edge of each face round `v`, a flip from
  `M` to `M'` at `v` can be undone, `IsFlipAt v M' M`.
* `TauCeti.IsFlipAt.symmDiff_eq`: under the same hypothesis `M` and `M'` differ exactly in the six
  edges at `v` named in the definition.
* `TauCeti.IsFlipAt.isTiling`: a flip of a tiling of a region containing the six faces round `v`
  is a tiling of the region.

## References

* V. Gorin, *Lectures on random lozenge tilings*, Cambridge Stud. Adv. Math. 193 (2021).
-/

public section

namespace TauCeti

/-- The tiling `(v,3)`, `(v−e₁,1)`, `(v−e₂,2)` of the hexagon round `v`, the one with the higher
height at `v`. -/
def highFlipEdges (v : ℤ × ℤ) : Set TriEdge :=
  {⟨v, 2⟩, ⟨v - (1, 0), 0⟩, ⟨v - (0, 1), 1⟩}

/-- The tiling `(v,1)`, `(v,2)`, `(v−e₃,3)` of the hexagon round `v`, the one with the lower height
at `v`. -/
def lowFlipEdges (v : ℤ × ℤ) : Set TriEdge :=
  {⟨v, 0⟩, ⟨v, 1⟩, ⟨v - (1, 1), 2⟩}

/-- `IsFlipAt v M M'`: `M` contains `(v,3)`, `(v−e₁,1)`, `(v−e₂,2)` and `M'` is obtained by
replacing them with `(v,1)`, `(v,2)`, `(v−e₃,3)`, or the reverse. -/
def IsFlipAt (v : ℤ × ℤ) (M M' : Set TriEdge) : Prop :=
  (highFlipEdges v ⊆ M ∧ M' = M \ highFlipEdges v ∪ lowFlipEdges v) ∨
    (lowFlipEdges v ⊆ M ∧ M' = M \ lowFlipEdges v ∪ highFlipEdges v)

/-- `IsFlip M M'`: `M'` is obtained from `M` by a flip at some vertex. -/
def IsFlip (M M' : Set TriEdge) : Prop :=
  ∃ v, IsFlipAt v M M'

variable {v : ℤ × ℤ} {R : Set TriFace} {M M' A B : Set TriEdge} {e : TriEdge} {f : TriFace}

theorem highFlipEdges_def (v : ℤ × ℤ) :
    highFlipEdges v = {⟨v, 2⟩, ⟨v - (1, 0), 0⟩, ⟨v - (0, 1), 1⟩} := (rfl)

theorem lowFlipEdges_def (v : ℤ × ℤ) :
    lowFlipEdges v = {⟨v, 0⟩, ⟨v, 1⟩, ⟨v - (1, 1), 2⟩} := (rfl)

theorem mem_highFlipEdges :
    e ∈ highFlipEdges v ↔ e = ⟨v, 2⟩ ∨ e = ⟨v - (1, 0), 0⟩ ∨ e = ⟨v - (0, 1), 1⟩ := Iff.rfl

theorem mem_lowFlipEdges :
    e ∈ lowFlipEdges v ↔ e = ⟨v, 0⟩ ∨ e = ⟨v, 1⟩ ∨ e = ⟨v - (1, 1), 2⟩ := Iff.rfl

theorem isFlipAt_def : IsFlipAt v M M' ↔
    (highFlipEdges v ⊆ M ∧ M' = M \ highFlipEdges v ∪ lowFlipEdges v) ∨
      (lowFlipEdges v ⊆ M ∧ M' = M \ lowFlipEdges v ∪ highFlipEdges v) := Iff.rfl

theorem isFlip_def : IsFlip M M' ↔ ∃ v, IsFlipAt v M M' := Iff.rfl

/-! ### The two tilings of a hexagon -/

/-- Each of the two triples has exactly one edge of each direction. -/
theorem existsUnique_mem_highFlipEdges_k (v : ℤ × ℤ) (k : Fin 3) :
    ∃! e, e ∈ highFlipEdges v ∧ e.k = k := by
  fin_cases k
  · exact ⟨⟨v - (1, 0), 0⟩, by simp [mem_highFlipEdges], fun e ⟨he, hk⟩ => by
      rcases mem_highFlipEdges.1 he with rfl | rfl | rfl <;> simp_all⟩
  · exact ⟨⟨v - (0, 1), 1⟩, by simp [mem_highFlipEdges], fun e ⟨he, hk⟩ => by
      rcases mem_highFlipEdges.1 he with rfl | rfl | rfl <;> simp_all⟩
  · exact ⟨⟨v, 2⟩, by simp [mem_highFlipEdges], fun e ⟨he, hk⟩ => by
      rcases mem_highFlipEdges.1 he with rfl | rfl | rfl <;> simp_all⟩

theorem existsUnique_mem_lowFlipEdges_k (v : ℤ × ℤ) (k : Fin 3) :
    ∃! e, e ∈ lowFlipEdges v ∧ e.k = k := by
  fin_cases k
  · exact ⟨⟨v, 0⟩, by simp [mem_lowFlipEdges], fun e ⟨he, hk⟩ => by
      rcases mem_lowFlipEdges.1 he with rfl | rfl | rfl <;> simp_all⟩
  · exact ⟨⟨v, 1⟩, by simp [mem_lowFlipEdges], fun e ⟨he, hk⟩ => by
      rcases mem_lowFlipEdges.1 he with rfl | rfl | rfl <;> simp_all⟩
  · exact ⟨⟨v - (1, 1), 2⟩, by simp [mem_lowFlipEdges], fun e ⟨he, hk⟩ => by
      rcases mem_lowFlipEdges.1 he with rfl | rfl | rfl <;> simp_all⟩

theorem disjoint_highFlipEdges_lowFlipEdges (v : ℤ × ℤ) :
    Disjoint (highFlipEdges v) (lowFlipEdges v) := by
  rw [Set.disjoint_left]
  intro e he he'
  rcases mem_highFlipEdges.1 he with rfl | rfl | rfl <;>
    rcases mem_lowFlipEdges.1 he' with h | h | h <;>
    simp [TriEdge.ext_iff, Prod.ext_iff] at h
  omega

/-- Every face containing an edge of `highFlipEdges v` has `v` as a vertex. -/
theorem mem_vertexFaces_of_mem_highFlipEdges (he : e ∈ highFlipEdges v) (hf : e ∈ f.edges) :
    f ∈ vertexFaces v := by
  obtain ⟨x, y⟩ := v
  rcases TriFace.mem_edges_iff.1 hf with rfl | rfl <;>
    rcases mem_highFlipEdges.1 he with rfl | rfl | rfl <;> simp [vertexFaces_def]

/-- Every face containing an edge of `lowFlipEdges v` has `v` as a vertex. -/
theorem mem_vertexFaces_of_mem_lowFlipEdges (he : e ∈ lowFlipEdges v) (hf : e ∈ f.edges) :
    f ∈ vertexFaces v := by
  obtain ⟨x, y⟩ := v
  rcases TriFace.mem_edges_iff.1 hf with rfl | rfl <;>
    rcases mem_lowFlipEdges.1 he with rfl | rfl | rfl <;> simp [vertexFaces_def]

/-- Every face round `v` contains exactly one edge of `highFlipEdges v`. -/
theorem existsUnique_mem_highFlipEdges (hf : f ∈ vertexFaces v) :
    ∃! e, e ∈ highFlipEdges v ∧ e ∈ f.edges := by
  obtain ⟨x, y⟩ := v
  simp only [vertexFaces_def, Finset.mem_insert, Finset.mem_singleton] at hf
  refine existsUnique_of_exists_of_unique ?_ ?_
  · rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [mem_highFlipEdges]
  · rintro e e' ⟨he, hef⟩ ⟨he', he'f⟩
    rcases mem_highFlipEdges.1 he with rfl | rfl | rfl <;>
      rcases mem_highFlipEdges.1 he' with rfl | rfl | rfl <;>
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [TriEdge.ext_iff, Prod.ext_iff] at hef he'f ⊢ <;> omega

/-- Every face round `v` contains exactly one edge of `lowFlipEdges v`. -/
theorem existsUnique_mem_lowFlipEdges (hf : f ∈ vertexFaces v) :
    ∃! e, e ∈ lowFlipEdges v ∧ e ∈ f.edges := by
  obtain ⟨x, y⟩ := v
  simp only [vertexFaces_def, Finset.mem_insert, Finset.mem_singleton] at hf
  refine existsUnique_of_exists_of_unique ?_ ?_
  · rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [mem_lowFlipEdges]
  · rintro e e' ⟨he, hef⟩ ⟨he', he'f⟩
    rcases mem_lowFlipEdges.1 he with rfl | rfl | rfl <;>
      rcases mem_lowFlipEdges.1 he' with rfl | rfl | rfl <;>
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [TriEdge.ext_iff, Prod.ext_iff] at hef he'f ⊢ <;> omega

/-- `highFlipEdges v` tiles the six faces round `v`. -/
theorem isTiling_highFlipEdges (v : ℤ × ℤ) :
    IsTiling (vertexFaces v : Set TriFace) (highFlipEdges v) :=
  isTiling_def.2 ⟨fun _ he _ hf => mem_vertexFaces_of_mem_highFlipEdges he hf,
    fun _ hf => existsUnique_mem_highFlipEdges hf⟩

/-- `lowFlipEdges v` tiles the six faces round `v`. -/
theorem isTiling_lowFlipEdges (v : ℤ × ℤ) :
    IsTiling (vertexFaces v : Set TriFace) (lowFlipEdges v) :=
  isTiling_def.2 ⟨fun _ he _ hf => mem_vertexFaces_of_mem_lowFlipEdges he hf,
    fun _ hf => existsUnique_mem_lowFlipEdges hf⟩

/-! ### Replacing one tiling of a hexagon by the other -/

section Replace

/-- If `M` contains at most one edge of each face round `v` and contains a tiling `A` of the
hexagon round `v`, then it contains no edge of another tiling `B` disjoint from `A`. -/
theorem disjoint_of_tiling_hexagon (hA : IsTiling (vertexFaces v : Set TriFace) A)
    (hB : IsTiling (vertexFaces v : Set TriFace) B) (hAB : Disjoint A B)
    (hM : ∀ f ∈ vertexFaces v, ∀ e ∈ M, ∀ e' ∈ M, e ∈ f.edges → e' ∈ f.edges → e = e')
    (hAM : A ⊆ M) :
    Disjoint M B := by
  rw [Set.disjoint_right]
  intro b hb hbM
  have hf : b.whiteFace ∈ vertexFaces v := hB.whiteFace_mem hb
  obtain ⟨a, ⟨ha, haf⟩, -⟩ := hA.existsUnique hf
  have := hM _ hf a (hAM ha) b hbM haf b.mem_whiteFace_edges
  exact Set.disjoint_left.1 hAB ha (this ▸ hb)

/-- Replacing `A` by `B` in a tiling of a region containing the hexagon gives a tiling. -/
theorem isTiling_replace_tiling_hexagon (hA : IsTiling (vertexFaces v : Set TriFace) A)
    (hB : IsTiling (vertexFaces v : Set TriFace) B) (hM : IsTiling R M) (hAM : A ⊆ M)
    (hR : (vertexFaces v : Set TriFace) ⊆ R) : IsTiling R (M \ A ∪ B) := by
  refine isTiling_def.2 ⟨?_, fun f hf => ?_⟩
  · rintro e (⟨heM, -⟩ | heB) f hef
    · exact hM.mem_of_mem_edges heM hef
    · exact hR (hB.mem_of_mem_edges heB hef)
  by_cases hfv : f ∈ vertexFaces v
  · obtain ⟨b, ⟨hb, hbf⟩, hbu⟩ := hB.existsUnique hfv
    refine ⟨b, ⟨Or.inr hb, hbf⟩, fun e ⟨he, hef⟩ => ?_⟩
    rcases he with ⟨heM, heA⟩ | heB
    · obtain ⟨a, ⟨ha, haf⟩, -⟩ := hA.existsUnique hfv
      exact absurd (hM.eq_of_mem_edges heM (hAM ha) hef haf ▸ ha) heA
    · exact hbu e ⟨heB, hef⟩
  · have hAf : ∀ e ∈ A, e ∉ f.edges := fun e he hef => hfv (hA.mem_of_mem_edges he hef)
    have hBf : ∀ e ∈ B, e ∉ f.edges := fun e he hef => hfv (hB.mem_of_mem_edges he hef)
    obtain ⟨e, ⟨heM, hef⟩, heu⟩ := hM.existsUnique hf
    refine ⟨e, ⟨Or.inl ⟨heM, fun heA => hAf e heA hef⟩, hef⟩, fun e' ⟨he', he'f⟩ => ?_⟩
    rcases he' with ⟨he'M, -⟩ | he'B
    · exact heu e' ⟨he'M, he'f⟩
    · exact absurd he'f (hBf e' he'B)

/-- Replacing `A` by `B` and then `B` by `A` gives back `M`, when `M` contains `A` and no edge of
`B`. -/
theorem replace_replace_tiling_hexagon (hAM : A ⊆ M) (hMB : Disjoint M B) :
    (M \ A ∪ B) \ B ∪ A = M := by
  ext e
  constructor
  · rintro (⟨⟨heM, -⟩ | heB, heB'⟩ | heA)
    · exact heM
    · exact absurd heB heB'
    · exact hAM heA
  · intro heM
    by_cases heA : e ∈ A
    · exact Or.inr heA
    · exact Or.inl ⟨Or.inl ⟨heM, heA⟩, fun heB => Set.disjoint_left.1 hMB heM heB⟩

/-- Replacing `A` by `B` in a set containing `A` and no edge of `B` changes exactly the edges of
`A` and `B`. -/
theorem symmDiff_replace_tiling_hexagon (hAB : Disjoint A B) (hAM : A ⊆ M) (hMB : Disjoint M B) :
    symmDiff M (M \ A ∪ B) = A ∪ B := by
  ext e
  simp only [Set.mem_symmDiff, Set.mem_union, Set.mem_sdiff]
  by_cases heA : e ∈ A
  · have heB : e ∉ B := fun heB => Set.disjoint_left.1 hAB heA heB
    simp [heA, heB, hAM heA]
  · by_cases heB : e ∈ B
    · have heM : e ∉ M := fun heM => Set.disjoint_left.1 hMB heM heB
      simp [heA, heB, heM]
    · simp [heA, heB]

end Replace

/-! ### Flips -/

namespace IsFlipAt

variable (hM : ∀ f ∈ vertexFaces v, ∀ e ∈ M, ∀ e' ∈ M, e ∈ f.edges → e' ∈ f.edges → e = e')

include hM in
/-- **A flip can be undone**: if `M` contains at most one edge of each of the six faces round `v`
and `IsFlipAt v M M'`, then `IsFlipAt v M' M`. -/
theorem symm (h : IsFlipAt v M M') : IsFlipAt v M' M := by
  have hd := disjoint_highFlipEdges_lowFlipEdges v
  rcases h with ⟨hAM, rfl⟩ | ⟨hAM, rfl⟩
  · refine Or.inr ⟨Set.subset_union_right, ?_⟩
    exact (replace_replace_tiling_hexagon
      hAM (disjoint_of_tiling_hexagon (isTiling_highFlipEdges v) (isTiling_lowFlipEdges v) hd hM
        hAM)).symm
  · refine Or.inl ⟨Set.subset_union_right, ?_⟩
    exact (replace_replace_tiling_hexagon
      hAM (disjoint_of_tiling_hexagon (isTiling_lowFlipEdges v) (isTiling_highFlipEdges v)
        hd.symm hM hAM)).symm

include hM in
/-- **A flip changes exactly the six edges at `v`**: if `M` contains at most one edge of each of
the six faces round `v` and `IsFlipAt v M M'`, then `M` and `M'` differ exactly in
`(v,3)`, `(v−e₁,1)`, `(v−e₂,2)`, `(v,1)`, `(v,2)`, `(v−e₃,3)`. -/
theorem symmDiff_eq (h : IsFlipAt v M M') :
    symmDiff M M' = highFlipEdges v ∪ lowFlipEdges v := by
  have hd := disjoint_highFlipEdges_lowFlipEdges v
  rcases h with ⟨hAM, rfl⟩ | ⟨hAM, rfl⟩
  · exact symmDiff_replace_tiling_hexagon hd
      hAM (disjoint_of_tiling_hexagon (isTiling_highFlipEdges v) (isTiling_lowFlipEdges v) hd hM
        hAM)
  · rw [Set.union_comm (highFlipEdges v)]
    exact symmDiff_replace_tiling_hexagon
      hd.symm hAM (disjoint_of_tiling_hexagon (isTiling_lowFlipEdges v) (isTiling_highFlipEdges v)
        hd.symm hM hAM)

omit hM in
/-- **Flips preserve tilings**: a flip at `v` of a tiling of a region containing the six faces
round `v` is a tiling of the region. -/
theorem isTiling (h : IsFlipAt v M M') (hMR : IsTiling R M)
    (hR : (vertexFaces v : Set TriFace) ⊆ R) : IsTiling R M' := by
  rcases h with ⟨hAM, rfl⟩ | ⟨hAM, rfl⟩
  · exact isTiling_replace_tiling_hexagon (isTiling_highFlipEdges v) (isTiling_lowFlipEdges v)
      hMR hAM hR
  · exact isTiling_replace_tiling_hexagon (isTiling_lowFlipEdges v) (isTiling_highFlipEdges v)
      hMR hAM hR

end IsFlipAt

/-- A tiling contains at most one edge of each face of the region, in particular of the six faces
round `v` when they lie in the region. -/
theorem IsTiling.eq_of_mem_vertexFaces (hMR : IsTiling R M) :
    ∀ f ∈ vertexFaces v, ∀ e ∈ M, ∀ e' ∈ M, e ∈ f.edges → e' ∈ f.edges → e = e' :=
  fun _ _ _ he _ he' hef he'f => hMR.eq_of_mem_edges he he' hef he'f

end TauCeti

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
other. Each triple has one edge of each direction, so when `M` is a tiling (more generally, when
`M` has at most one edge in each face round `v`) a flip removes one lozenge of each type and adds
one of each type.

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
  `M` to `M'` at `v` can be undone, `IsFlipAt v M' M`; `TauCeti.IsFlip.symm` for tilings.
* `TauCeti.IsFlipAt.symmDiff_eq`: under the same hypothesis `M` and `M'` differ exactly in the six
  edges at `v` named in the definition.
* `TauCeti.IsFlipAt.isTiling`, `TauCeti.IsFlip.isTiling`: a flip of a tiling of a region is a
  tiling of the region.

## References

* V. Gorin, *Lectures on random lozenge tilings*, Cambridge Stud. Adv. Math. 193 (2021).
-/

public section

namespace TauCeti

/-- The tiling of the hexagon round `v` by the three edges `(v,3)`, `(v−e₁,1)`, `(v−e₂,2)`. -/
def highFlipEdges (v : ℤ × ℤ) : Set TriEdge :=
  {⟨v, 2⟩, ⟨v - (1, 0), 0⟩, ⟨v - (0, 1), 1⟩}

/-- The tiling of the hexagon round `v` by the three edges `(v,1)`, `(v,2)`, `(v−e₃,3)`. -/
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

@[simp] theorem mem_highFlipEdges :
    e ∈ highFlipEdges v ↔ e = ⟨v, 2⟩ ∨ e = ⟨v - (1, 0), 0⟩ ∨ e = ⟨v - (0, 1), 1⟩ := Iff.rfl

@[simp] theorem mem_lowFlipEdges :
    e ∈ lowFlipEdges v ↔ e = ⟨v, 0⟩ ∨ e = ⟨v, 1⟩ ∨ e = ⟨v - (1, 1), 2⟩ := Iff.rfl

theorem isFlipAt_def : IsFlipAt v M M' ↔
    (highFlipEdges v ⊆ M ∧ M' = M \ highFlipEdges v ∪ lowFlipEdges v) ∨
      (lowFlipEdges v ⊆ M ∧ M' = M \ lowFlipEdges v ∪ highFlipEdges v) := Iff.rfl

theorem isFlip_def : IsFlip M M' ↔ ∃ v, IsFlipAt v M M' := Iff.rfl

/-! ### The two tilings of a hexagon -/

/-- `highFlipEdges v` has exactly one edge of each direction. -/
theorem existsUnique_mem_highFlipEdges_k (v : ℤ × ℤ) (k : Fin 3) :
    ∃! e, e ∈ highFlipEdges v ∧ e.k = k := by
  fin_cases k
  · exact ⟨⟨v - (1, 0), 0⟩, by simp, fun e ⟨he, hk⟩ => by
      rcases mem_highFlipEdges.1 he with rfl | rfl | rfl <;> simp_all⟩
  · exact ⟨⟨v - (0, 1), 1⟩, by simp, fun e ⟨he, hk⟩ => by
      rcases mem_highFlipEdges.1 he with rfl | rfl | rfl <;> simp_all⟩
  · exact ⟨⟨v, 2⟩, by simp, fun e ⟨he, hk⟩ => by
      rcases mem_highFlipEdges.1 he with rfl | rfl | rfl <;> simp_all⟩

/-- `lowFlipEdges v` has exactly one edge of each direction. -/
theorem existsUnique_mem_lowFlipEdges_k (v : ℤ × ℤ) (k : Fin 3) :
    ∃! e, e ∈ lowFlipEdges v ∧ e.k = k := by
  fin_cases k
  · exact ⟨⟨v, 0⟩, by simp, fun e ⟨he, hk⟩ => by
      rcases mem_lowFlipEdges.1 he with rfl | rfl | rfl <;> simp_all⟩
  · exact ⟨⟨v, 1⟩, by simp, fun e ⟨he, hk⟩ => by
      rcases mem_lowFlipEdges.1 he with rfl | rfl | rfl <;> simp_all⟩
  · exact ⟨⟨v - (1, 1), 2⟩, by simp, fun e ⟨he, hk⟩ => by
      rcases mem_lowFlipEdges.1 he with rfl | rfl | rfl <;> simp_all⟩

theorem disjoint_highFlipEdges_lowFlipEdges (v : ℤ × ℤ) :
    Disjoint (highFlipEdges v) (lowFlipEdges v) := by
  rw [Set.disjoint_left]
  intro e he he'
  rcases mem_highFlipEdges.1 he with rfl | rfl | rfl <;>
    rcases mem_lowFlipEdges.1 he' with h | h | h <;>
    simp [TriEdge.ext_iff, Prod.ext_iff, eq_sub_iff_add_eq] at h

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

/-- Every edge of `highFlipEdges v` has `v` as an endpoint. -/
theorem mem_endpoints_of_mem_highFlipEdges (he : e ∈ highFlipEdges v) : v ∈ e.endpoints := by
  rcases mem_highFlipEdges.1 he with rfl | rfl | rfl <;> simp [latticeDir_zero, latticeDir_one]

/-- Every edge of `lowFlipEdges v` has `v` as an endpoint. -/
theorem mem_endpoints_of_mem_lowFlipEdges (he : e ∈ lowFlipEdges v) : v ∈ e.endpoints := by
  rcases mem_lowFlipEdges.1 he with rfl | rfl | rfl <;> simp [latticeDir_two]

/-- Every face round `v` contains exactly one edge of `highFlipEdges v`. -/
theorem existsUnique_mem_highFlipEdges (hf : f ∈ vertexFaces v) :
    ∃! e, e ∈ highFlipEdges v ∧ e ∈ f.edges := by
  obtain ⟨x, y⟩ := v
  simp only [vertexFaces_def, Finset.mem_insert, Finset.mem_singleton] at hf
  refine existsUnique_of_exists_of_unique ?_ ?_
  · rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
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
  · rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
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

/-! ### Flips -/

/-- A flip at `v` replaces a triple `A` by a triple `B`, where `(A, B)` is one of the two orders of
`highFlipEdges v` and `lowFlipEdges v`. -/
theorem isFlipAt_iff_exists : IsFlipAt v M M' ↔ ∃ A B,
    (A = highFlipEdges v ∧ B = lowFlipEdges v ∨ A = lowFlipEdges v ∧ B = highFlipEdges v) ∧
      A ⊆ M ∧ M' = M \ A ∪ B := by
  constructor
  · rintro (⟨hAM, rfl⟩ | ⟨hAM, rfl⟩)
    exacts [⟨_, _, Or.inl ⟨rfl, rfl⟩, hAM, rfl⟩, ⟨_, _, Or.inr ⟨rfl, rfl⟩, hAM, rfl⟩]
  · rintro ⟨A, B, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, hAM, rfl⟩
    exacts [Or.inl ⟨hAM, rfl⟩, Or.inr ⟨hAM, rfl⟩]

/-- In either order, the two triples are disjoint tilings of the hexagon round `v` whose union is
the six edges at `v`. -/
private theorem isTiling_and_isTiling_of_flipPair
    (h : A = highFlipEdges v ∧ B = lowFlipEdges v ∨ A = lowFlipEdges v ∧ B = highFlipEdges v) :
    IsTiling (vertexFaces v : Set TriFace) A ∧ IsTiling (vertexFaces v : Set TriFace) B ∧
      Disjoint A B ∧ A ∪ B = highFlipEdges v ∪ lowFlipEdges v := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨isTiling_highFlipEdges v, isTiling_lowFlipEdges v,
      disjoint_highFlipEdges_lowFlipEdges v, rfl⟩
  · exact ⟨isTiling_lowFlipEdges v, isTiling_highFlipEdges v,
      (disjoint_highFlipEdges_lowFlipEdges v).symm, Set.union_comm _ _⟩

namespace IsFlipAt

/-- **A flip can be undone**: if `M` contains at most one edge of each of the six faces round `v`
and `IsFlipAt v M M'`, then `IsFlipAt v M' M`. -/
theorem symm (h : IsFlipAt v M M')
    (hM : ∀ f ∈ vertexFaces v, ∀ e ∈ M, ∀ e' ∈ M, e ∈ f.edges → e' ∈ f.edges → e = e') :
    IsFlipAt v M' M := by
  obtain ⟨A, B, hp, hAM, rfl⟩ := isFlipAt_iff_exists.1 h
  obtain ⟨hA, hB, hAB, -⟩ := isTiling_and_isTiling_of_flipPair hp
  have hMB := disjoint_of_isTiling_of_subset hA hB hAB hM hAM
  refine isFlipAt_iff_exists.2 ⟨B, A, hp.symm.imp And.symm And.symm, Set.subset_union_right, ?_⟩
  rw [Set.union_sdiff_right, sdiff_eq_left.2 (hMB.mono_left Set.sdiff_subset),
    Set.sdiff_union_of_subset hAM]

/-- **A flip changes exactly the six edges at `v`**: if `M` contains at most one edge of each of
the six faces round `v` and `IsFlipAt v M M'`, then `M` and `M'` differ exactly in
`(v,3)`, `(v−e₁,1)`, `(v−e₂,2)`, `(v,1)`, `(v,2)`, `(v−e₃,3)`. -/
theorem symmDiff_eq (h : IsFlipAt v M M')
    (hM : ∀ f ∈ vertexFaces v, ∀ e ∈ M, ∀ e' ∈ M, e ∈ f.edges → e' ∈ f.edges → e = e') :
    symmDiff M M' = highFlipEdges v ∪ lowFlipEdges v := by
  obtain ⟨A, B, hp, hAM, rfl⟩ := isFlipAt_iff_exists.1 h
  obtain ⟨hA, hB, hAB, hAB'⟩ := isTiling_and_isTiling_of_flipPair hp
  have hMB := disjoint_of_isTiling_of_subset hA hB hAB hM hAM
  rw [← hAB']
  ext e
  have hAM : e ∈ A → e ∈ M := @hAM e
  have hMB : e ∈ M → e ∉ B := @Set.disjoint_left.1 hMB e
  have hAB : e ∈ A → e ∉ B := @Set.disjoint_left.1 hAB e
  simp only [Set.mem_symmDiff, Set.mem_union, Set.mem_sdiff]
  tauto

/-- **Flips preserve tilings**: a flip of a tiling of a region is a tiling of the region. -/
theorem isTiling (h : IsFlipAt v M M') (hM : IsTiling R M) : IsTiling R M' := by
  obtain ⟨A, B, hp, hAM, rfl⟩ := isFlipAt_iff_exists.1 h
  obtain ⟨hA, hB, -, -⟩ := isTiling_and_isTiling_of_flipPair hp
  exact hM.sdiff_union hA hB hAM

/-- A flip at `v` is a flip. -/
theorem isFlip (h : IsFlipAt v M M') : IsFlip M M' :=
  ⟨v, h⟩

end IsFlipAt

namespace IsFlip

/-- A flip of a tiling can be undone. -/
theorem symm (h : IsFlip M M') (hM : IsTiling R M) : IsFlip M' M :=
  let ⟨v, hv⟩ := h
  ⟨v, hv.symm fun _ _ _ he _ he' => hM.eq_of_mem_edges he he'⟩

/-- **Flips preserve tilings**: a flip of a tiling of a region is a tiling of the region. -/
theorem isTiling (h : IsFlip M M') (hM : IsTiling R M) : IsTiling R M' :=
  let ⟨_, hv⟩ := h
  hv.isTiling hM

end IsFlip

end TauCeti

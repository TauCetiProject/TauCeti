/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Subpolyad

/-!
# A subpolyad that is not a vertex box

On four vertices with one vertex cell and one pair color, keep only the zero-one pairs
`(0, 1)` and `(1, 2)` while leaving the other two pair graphs unchanged. The triples `(0, 1, 3)`
and `(1, 2, 3)` survive, but `(0, 2, 3)` does not. No restriction of the three vertex cells can
have this support: keeping the first two triples forces the third into any vertex box.
-/

open Finset

namespace TauCeti

private def oneCell : PairSkeleton3 Unit (Fin 4) where
  vertexPart := Finpartition.indiscrete univ_nonempty.ne_empty
  pairColors :=
    { color := fun _ ↦ ()
      rev := id
      rev_involutive := fun _ ↦ rfl
      color_rev := fun _ ↦ rfl }

private def fullPolyad : Polyad3 oneCell where
  c₀ := univ
  c₁ := univ
  c₂ := univ
  hc₀ := by simp [oneCell]
  hc₁ := by simp [oneCell]
  hc₂ := by simp [oneCell]
  color₀₁ := ()
  color₀₂ := ()
  color₁₂ := ()

private noncomputable def pruned : Subpolyad3 fullPolyad where
  pair₀₁ := fullPolyad.pairSupport₀₁.filter fun p ↦ p.1 = (0, 1) ∨ p.1 = (1, 2)
  pair₀₂ := fullPolyad.pairSupport₀₂
  pair₁₂ := fullPolyad.pairSupport₁₂
  pair₀₁_sub := filter_subset _ _
  pair₀₂_sub := Subset.rfl
  pair₁₂_sub := Subset.rfl

private def triple013 : {x : Fin 3 → Fin 4 // Function.Injective x} :=
  ⟨![0, 1, 3], by decide⟩

private def triple123 : {x : Fin 3 → Fin 4 // Function.Injective x} :=
  ⟨![1, 2, 3], by decide⟩

private def triple023 : {x : Fin 3 → Fin 4 // Function.Injective x} :=
  ⟨![0, 2, 3], by decide⟩

private theorem triple013_mem : triple013 ∈ pruned.support := by
  rw [Subpolyad3.mem_support_iff_coordPair_mem]
  simp [pruned, fullPolyad, oneCell, triple013, coe_coordPair]

private theorem triple123_mem : triple123 ∈ pruned.support := by
  rw [Subpolyad3.mem_support_iff_coordPair_mem]
  simp [pruned, fullPolyad, oneCell, triple123, coe_coordPair]

private theorem triple023_notMem : triple023 ∉ pruned.support := by
  rw [Subpolyad3.mem_support_iff_coordPair_mem]
  simp [pruned, triple023, coe_coordPair]

/-- Subpolyad supports cannot in general be obtained by restricting the vertex cells. -/
public theorem exists_subpolyad_not_vertex_box :
    ∃ (S : PairSkeleton3 Unit (Fin 4)) (P : Polyad3 S) (Q : Subpolyad3 P),
      ∀ a₀ a₁ a₂ : Finset (Fin 4),
        Q.support ≠ (Subpolyad3.ofSubcells P a₀ a₁ a₂).support := by
  refine ⟨oneCell, fullPolyad, pruned, ?_⟩
  intro a₀ a₁ a₂ h
  have h013 := triple013_mem
  have h123 := triple123_mem
  rw [h, Subpolyad3.mem_ofSubcells_support] at h013 h123
  apply triple023_notMem
  rw [h, Subpolyad3.mem_ofSubcells_support]
  refine ⟨?_, h013.2.1, h123.2.2.1, h013.2.2.2⟩
  simp [fullPolyad, oneCell, triple023, PairColorSystem.colorOfPair_of_ne]

example : (Subpolyad3.ofSubcells fullPolyad {0} {1} {3}).support = {triple013} := by
  ext x
  simp only [Subpolyad3.mem_ofSubcells_support, mem_singleton]
  constructor
  · rintro ⟨_, h₀, h₁, h₂⟩
    apply Subtype.ext
    funext i
    fin_cases i <;> simp_all [triple013]
  · rintro rfl
    exact ⟨pruned.support_subset triple013_mem, by decide, by decide, by decide⟩

end TauCeti

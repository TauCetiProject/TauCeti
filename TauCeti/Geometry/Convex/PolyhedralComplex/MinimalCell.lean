/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Convex.PolyhedralComplex.Basic

/-! # Minimal containing cells

Every nonempty set contained in a cell of a finite polyhedral complex has a
unique smallest containing cell. Nonemptiness guarantees that intersections
of containing cells remain cells.

Adapted from `Mei/Geometry/Convex/PolyhedralComplex/MinimalCell.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `7f1e4c7714fb020473694755ad8748c8f15d0e7f` (Apache 2.0).
-/

public section

namespace TauCeti.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- Every nonempty set contained in a cell has a unique smallest containing cell. -/
theorem exists_unique_minimalContainingCell (C : FinitePolyhedralComplex h) {A : Set V}
    (hne : A.Nonempty) (hcontained : ∃ P ∈ C.cells, A ⊆ P) :
    ∃! P : Set V, P ∈ C.cells ∧ A ⊆ P ∧ ∀ Q ∈ C.cells, A ⊆ Q → P ⊆ Q := by
  classical
  let S := C.cells.filter (fun P => A ⊆ P)
  have hS : S.Nonempty := by
    obtain ⟨P, hP, hAP⟩ := hcontained
    exact ⟨P, Finset.mem_filter.mpr ⟨hP, hAP⟩⟩
  obtain ⟨P, hP, hmin⟩ := S.exists_minimal hS
  obtain ⟨hPC, hAP⟩ := Finset.mem_filter.mp hP
  have hleast : ∀ Q ∈ C.cells, A ⊆ Q → P ⊆ Q := by
    intro Q hQ hAQ
    have hAPQ : A ⊆ P ∩ Q := fun x hx => ⟨hAP hx, hAQ hx⟩
    have hPQ : (P ∩ Q).Nonempty := hne.mono hAPQ
    have hmem : P ∩ Q ∈ S :=
      Finset.mem_filter.mpr ⟨C.inter_mem_cells hPC hQ hPQ, hAPQ⟩
    exact (hmin hmem Set.inter_subset_left).trans Set.inter_subset_right
  refine ⟨P, ⟨hPC, hAP, hleast⟩, ?_⟩
  intro Q hQ
  exact Set.Subset.antisymm (hQ.2.2 P hPC hAP) (hleast Q hQ.1 hQ.2.1)

/-- The actual smallest cell containing a nonempty set already contained in some cell. -/
noncomputable def minimalContainingCell (C : FinitePolyhedralComplex h) (A : Set V)
    (hne : A.Nonempty) (hcontained : ∃ P ∈ C.cells, A ⊆ P) : Set V :=
  (C.exists_unique_minimalContainingCell hne hcontained).choose

/-- The selected smallest containing cell belongs to the complex. -/
theorem minimalContainingCell_mem (C : FinitePolyhedralComplex h) (A : Set V)
    (hne : A.Nonempty) (hcontained : ∃ P ∈ C.cells, A ⊆ P) :
    C.minimalContainingCell A hne hcontained ∈ C.cells :=
  (C.exists_unique_minimalContainingCell hne hcontained).choose_spec.1.1

/-- The selected cell contains the prescribed set. -/
theorem subset_minimalContainingCell (C : FinitePolyhedralComplex h) (A : Set V)
    (hne : A.Nonempty) (hcontained : ∃ P ∈ C.cells, A ⊆ P) :
    A ⊆ C.minimalContainingCell A hne hcontained :=
  (C.exists_unique_minimalContainingCell hne hcontained).choose_spec.1.2.1

/-- The selected cell is contained in every other containing cell. -/
theorem minimalContainingCell_subset (C : FinitePolyhedralComplex h) (A : Set V)
    (hne : A.Nonempty) (hcontained : ∃ P ∈ C.cells, A ⊆ P) {Q : Set V}
    (hQ : Q ∈ C.cells) (hAQ : A ⊆ Q) :
    C.minimalContainingCell A hne hcontained ⊆ Q :=
  (C.exists_unique_minimalContainingCell hne hcontained).choose_spec.1.2.2 Q hQ hAQ

/-- The minimal cell lies in a cell `Q` exactly when the original set does. -/
@[simp]
theorem minimalContainingCell_subset_iff (C : FinitePolyhedralComplex h) (A : Set V)
    (hne : A.Nonempty) (hcontained : ∃ P ∈ C.cells, A ⊆ P) {Q : Set V}
    (hQ : Q ∈ C.cells) :
    C.minimalContainingCell A hne hcontained ⊆ Q ↔ A ⊆ Q :=
  ⟨(C.subset_minimalContainingCell A hne hcontained).trans,
    C.minimalContainingCell_subset A hne hcontained hQ⟩

/-- The smallest cell containing a cell is the cell itself. -/
@[simp]
theorem minimalContainingCell_of_mem (C : FinitePolyhedralComplex h) {P : Set V}
    (hP : P ∈ C.cells) :
    C.minimalContainingCell P (C.nonempty P hP) ⟨P, hP, Set.Subset.rfl⟩ = P :=
  Set.Subset.antisymm (C.minimalContainingCell_subset _ _ _ hP Set.Subset.rfl)
    (C.subset_minimalContainingCell _ _ _)

/-- Inclusion of nonempty sets gives inclusion of their smallest containing cells. -/
theorem minimalContainingCell_mono (C : FinitePolyhedralComplex h) {A B : Set V}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hCA : ∃ P ∈ C.cells, A ⊆ P) (hCB : ∃ P ∈ C.cells, B ⊆ P) (hAB : A ⊆ B) :
    C.minimalContainingCell A hA hCA ⊆ C.minimalContainingCell B hB hCB :=
  C.minimalContainingCell_subset A hA hCA (C.minimalContainingCell_mem B hB hCB)
    (hAB.trans (C.subset_minimalContainingCell B hB hCB))

end TauCeti.FinitePolyhedralComplex

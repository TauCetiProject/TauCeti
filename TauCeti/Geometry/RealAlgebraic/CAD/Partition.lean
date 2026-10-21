/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.CAD.Basic
public import TauCeti.Geometry.RealAlgebraic.Stack.Partition

/-!
# Cylindrical algebraic decompositions as finite partitions

`TauCeti.IsCAD` defines a cylindrical algebraic decomposition recursively: a CAD of `ℝ ^ (n + 1)`
is made by choosing a semialgebraic stack over each cell of a CAD of `ℝ ^ n` and taking all of
their cells. This file proves that this is equivalent to the cell-wise definition of
Basu–Pollack–Roy. A set `𝒞` of subsets of `ℝ ^ (n + 1)` is a CAD exactly when:

* it is a finite partition of `ℝ ^ (n + 1)` into semialgebraic sets;
* the projections of its cells, forgetting coordinate `0`, form a CAD of `ℝ ^ n`;
* each cell is the graph of a continuous function on its projection, or a band between two such
  graphs (either of which may be absent). We express this as being a section or a sector of a
  continuous, strictly ordered stack over the projection, possibly a different stack for each
  cell.

The stacks are not assumed to fit together. That the cells over each base cell are nonetheless
the cells of one semialgebraic stack is the content of
`TauCeti.exists_eq_range_sectionSet_union_range_sectorSet`, which applies because the base cells
of a CAD are connected. An intermediate form identifies the stack over a base cell `C` with the
set of cells of `𝒞` whose projection is `C`.

## Main results

* `TauCeti.isCAD_zero_iff`: the only CAD of `ℝ ^ 0` is the single cell.
* `TauCeti.isCAD_succ_iff_exists_isSemialgebraicStack`: a CAD of `ℝ ^ (n + 1)` is a set of cells
  whose projections form a CAD of `ℝ ^ n` and whose cells over each projected cell are the cells
  of a semialgebraic stack over it.
* `TauCeti.isCAD_succ_iff`: the finite-partition characterization of a CAD of `ℝ ^ (n + 1)`.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Definition 5.1.
-/

public section

open Function Set

namespace TauCeti

variable {n : ℕ}

/-- The only cylindrical algebraic decomposition of `ℝ ^ 0` consists of the single cell. -/
theorem isCAD_zero_iff {𝒞 : Set (Set (Fin 0 → ℝ))} : IsCAD 0 𝒞 ↔ 𝒞 = {univ} :=
  ⟨fun h ↦ by cases h; rfl, fun h ↦ h ▸ .zero⟩

/-- A set `𝒞` of subsets of `ℝ ^ (n + 1)` is a cylindrical algebraic decomposition exactly when
the projections of its cells, forgetting coordinate `0`, form a cylindrical algebraic
decomposition of `ℝ ^ n`, and over each projected cell `C` the cells of `𝒞` lying over `C` are
the cells of a semialgebraic stack over `C`. -/
theorem isCAD_succ_iff_exists_isSemialgebraicStack {𝒞 : Set (Set (Fin (n + 1) → ℝ))} :
    IsCAD (n + 1) 𝒞 ↔ IsCAD n (image Fin.tail '' 𝒞) ∧
      ∀ C ∈ image Fin.tail '' 𝒞, ∃ k, ∃ θ : Fin k → C → ℝ, IsSemialgebraicStack C θ ∧
        {E ∈ 𝒞 | Fin.tail '' E = C} = stackCells C θ := by
  constructor
  · intro h
    refine ⟨h.image_tail, ?_⟩
    cases h with
    | succ k θ h𝒟 hθ =>
      rw [image_image_tail_iUnion_stackCells fun C hC ↦ (hθ C hC).strictMono]
      intro C hC
      refine ⟨k C, θ C, hθ C hC, ?_⟩
      ext E
      simp only [mem_iUnion₂]
      refine ⟨?_, fun hE ↦ ⟨⟨C, hC, hE⟩, image_tail_of_mem_stackCells (hθ C hC).strictMono hE⟩⟩
      rintro ⟨⟨C', hC', hE⟩, hEC⟩
      rw [image_tail_of_mem_stackCells (hθ C' hC').strictMono hE] at hEC
      exact hEC ▸ hE
  · rintro ⟨h𝒟, hstack⟩
    have hstack' (C : Set (Fin n → ℝ)) : ∃ k, ∃ θ : Fin k → C → ℝ, C ∈ image Fin.tail '' 𝒞 →
        IsSemialgebraicStack C θ ∧ {E ∈ 𝒞 | Fin.tail '' E = C} = stackCells C θ := by
      by_cases hC : C ∈ image Fin.tail '' 𝒞
      · obtain ⟨k, θ, hθ⟩ := hstack C hC
        exact ⟨k, θ, fun _ ↦ hθ⟩
      · exact ⟨0, Fin.elim0, fun h ↦ (hC h).elim⟩
    choose k θ hθ using hstack'
    convert IsCAD.succ k θ h𝒟 fun C hC ↦ (hθ C hC).1
    ext E
    simp only [mem_iUnion₂]
    refine ⟨fun hE ↦ ⟨_, mem_image_of_mem _ hE, ?_⟩, fun ⟨C, hC, hE⟩ ↦ ?_⟩
    · rw [← (hθ _ (mem_image_of_mem _ hE)).2]
      exact ⟨hE, rfl⟩
    · rw [← (hθ C hC).2] at hE
      exact hE.1

/-- **The finite-partition characterization of a CAD.** A set `𝒞` of subsets of `ℝ ^ (n + 1)` is
a cylindrical algebraic decomposition exactly when it is a finite partition of `ℝ ^ (n + 1)` into
semialgebraic sets, the projections of its cells forgetting coordinate `0` form a cylindrical
algebraic decomposition of `ℝ ^ n`, and each cell `E` is a section or a sector of some stack of
continuous, pointwise strictly ordered functions on its projection `Fin.tail '' E`. The stacks
may differ from cell to cell. -/
theorem isCAD_succ_iff {𝒞 : Set (Set (Fin (n + 1) → ℝ))} :
    IsCAD (n + 1) 𝒞 ↔ 𝒞.Finite ∧ Setoid.IsPartition 𝒞 ∧ (∀ E ∈ 𝒞, IsSemialgebraic E) ∧
      IsCAD n (image Fin.tail '' 𝒞) ∧
      ∀ E ∈ 𝒞, ∃ k, ∃ θ : Fin k → Fin.tail '' E → ℝ, (∀ i, Continuous (θ i)) ∧
        (∀ x, StrictMono fun i ↦ θ i x) ∧ E ∈ stackCells (Fin.tail '' E) θ := by
  refine ⟨fun h ↦ ⟨h.finite, h.isPartition, fun E hE ↦ h.isSemialgebraic hE, h.image_tail,
    fun E hE ↦ ?_⟩, fun ⟨hfin, hpart, hsemi, h𝒟, hcell⟩ ↦ ?_⟩
  · obtain ⟨k, θ, hθ, hθ𝒞⟩ :=
      (isCAD_succ_iff_exists_isSemialgebraicStack.1 h).2 _ (mem_image_of_mem _ hE)
    exact ⟨k, θ, hθ.continuous, hθ.strictMono, hθ𝒞 ▸ ⟨hE, rfl⟩⟩
  refine isCAD_succ_iff_exists_isSemialgebraicStack.2 ⟨h𝒟, fun C hC ↦ ?_⟩
  have hCc := h𝒟.isConnected hC
  have : PreconnectedSpace C := isPreconnected_iff_preconnectedSpace.1 hCc.isPreconnected
  have : Nonempty C := hCc.nonempty.to_subtype
  -- The cells over `C` lie in the image of the cylinder over `C`.
  have himage {E : Set (Fin (n + 1) → ℝ)} (hEC : Fin.tail '' E = C) :
      cylinder C '' (cylinder C ⁻¹' E) = E := by
    refine image_preimage_eq_of_subset fun y hy ↦ ?_
    rw [range_cylinder, mem_ofPred_eq, ← hEC]
    exact mem_image_of_mem _ hy
  -- Pulled back to `C × ℝ`, the cells over `C` partition the cylinder into stack cells.
  set 𝒜 := (cylinder C ⁻¹' ·) '' {E ∈ 𝒞 | Fin.tail '' E = C}
  obtain ⟨k, θ, hc, hθ, hθ𝒜⟩ := exists_eq_range_sectionSet_union_range_sectorSet (𝒜 := 𝒜)
    ((hfin.subset (sep_subset _ _)).image _)
    (by
      rintro _ ⟨E, hE, rfl⟩ _ ⟨E', hE', rfl⟩ hne
      exact (hpart.pairwiseDisjoint hE.1 hE'.1 fun h ↦ hne (h ▸ rfl)).preimage _)
    (by
      refine eq_univ_of_forall fun z ↦ ?_
      obtain ⟨E, ⟨hE, hzE⟩, -⟩ := hpart.2 (cylinder C z)
      -- The projections of the cells of `𝒞` partition `ℝ ^ n`, so `E` lies over `C`.
      have hEC : Fin.tail '' E = C := h𝒟.isPartition.pairwiseDisjoint.elim
        (mem_image_of_mem _ hE) hC (not_disjoint_iff.2
          ⟨_, mem_image_of_mem _ hzE, by rw [tail_cylinder]; exact z.1.2⟩)
      exact mem_sUnion.2 ⟨_, mem_image_of_mem _ ⟨hE, hEC⟩, hzE⟩)
    (by
      rintro _ ⟨E, ⟨hE, rfl⟩, rfl⟩
      obtain ⟨k, θ, hc, hθ, hEθ⟩ := hcell E hE
      refine ⟨k, θ, hc, hθ, ?_⟩
      rcases mem_stackCells.1 hEθ with ⟨i, hi⟩ | ⟨j, hj⟩
      · exact Or.inl ⟨i, (preimage_image_eq _ cylinder_injective).symm.trans
          (congrArg (cylinder _ ⁻¹' ·) hi)⟩
      · exact Or.inr ⟨j, (preimage_image_eq _ cylinder_injective).symm.trans
          (congrArg (cylinder _ ⁻¹' ·) hj)⟩)
  -- Pushing forward the common stack gives the cells of `𝒞` over `C`.
  have hstack : {E ∈ 𝒞 | Fin.tail '' E = C} = stackCells C θ := by
    ext E
    refine ⟨fun hE ↦ ?_, fun hE ↦ ?_⟩
    · have hA : cylinder C ⁻¹' E ∈ 𝒜 := mem_image_of_mem _ hE
      rw [hθ𝒜] at hA
      rw [← himage hE.2]
      rcases hA with ⟨i, hi⟩ | ⟨j, hj⟩
      · exact hi ▸ image_cylinder_sectionSet_mem_stackCells i
      · exact hj ▸ image_cylinder_sectorSet_mem_stackCells j
    · have hA : ∃ A ∈ 𝒜, cylinder C '' A = E := by
        rcases mem_stackCells.1 hE with ⟨i, rfl⟩ | ⟨j, rfl⟩
        · exact ⟨_, hθ𝒜 ▸ Or.inl (mem_range_self i), rfl⟩
        · exact ⟨_, hθ𝒜 ▸ Or.inr (mem_range_self j), rfl⟩
      obtain ⟨_, ⟨E', hE', rfl⟩, rfl⟩ := hA
      rwa [himage hE'.2]
  refine ⟨k, θ, ⟨hc, hθ, fun i ↦ ?_, fun j ↦ ?_⟩, hstack⟩
  · exact hsemi _ (hstack ▸ image_cylinder_sectionSet_mem_stackCells i).1
  · exact hsemi _ (hstack ▸ image_cylinder_sectorSet_mem_stackCells j).1

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity (Gemini 4 Carbon)
-/
module

public import TauCeti.Geometry.Convex.PolyhedralComplex.Basic
import TauCeti.Analysis.Normed.Affine.Generic

/-!
# Cell covering in subdivisions of finite polyhedral complexes

In a subdivision `C` of a finite rational-normal polyhedral complex `D`, every cell `P` of `D` is
already covered by the cells of `C` contained in `P` (`IsSubdivision.exists_mem_cells_subset`).
This file strengthens that covering to retain the dimension of `P`: every cell `P` of `D` is the
union of those cells `Q` of `C` contained in `P` that have the same affine span as `P`
(`IsSubdivision.cell_eq_biUnion_affineSpan_eq`). Indeed, the cells of `C` inside `P` with strictly
smaller affine span lie in finitely many proper affine subspaces of `affineSpan ℝ P`, so by
`AffineSubspace.exists_direction_le_of_forall_mem` they cannot cover any neighbourhood of an
intrinsic interior point of `P`; closedness of the top-dimensional pieces inside `P` together with
density of `intrinsicInterior ℝ P` in `P` then yields `P`.

Specializing to cells of ambient codimension `k`, each `P ∈ D.cellsOfCodimension k` is the union of
the cells `Q ∈ C.cellsOfCodimension k` contained in `P`
(`IsSubdivision.cell_eq_biUnion_cellsOfCodimension`), so the union of the codimension-`k` cells of
`D` lies in the union of the codimension-`k` cells of `C`
(`IsSubdivision.biUnion_cellsOfCodimension_subset`). For `k = 1`, every point on a wall of `D` lies
on a wall of `C`, while `C` may introduce additional walls inside higher-dimensional cells of `D`.

Independently of subdivision, a set `Q` is contained in at most one cell of `C` sharing its affine
span (`eq_of_subset_of_affineSpan_eq`), and a nonempty set of ambient codimension `k` is contained
in at most one cell of `C.cellsOfCodimension k` (`eq_of_subset_of_mem_cellsOfCodimension`).

## References

* G. M. Ziegler, *Lectures on Polytopes*, §5.1.
* T. Bridgeland, *Scattering diagrams, Hall algebras and stability conditions*, §2.2.
-/

public section

namespace TauCeti.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- A subset `Q` is contained in at most one cell of `C` having the same affine span as `Q`:
the intersection of two such cells is again a cell of `C` with the same affine dimension. -/
theorem eq_of_subset_of_affineSpan_eq (C : FinitePolyhedralComplex h)
    {Q P₁ P₂ : Set V} (hP₁ : P₁ ∈ C.cells) (hP₂ : P₂ ∈ C.cells)
    (hQP₁ : Q ⊆ P₁) (hQP₂ : Q ⊆ P₂)
    (hspan₁ : affineSpan ℝ Q = affineSpan ℝ P₁)
    (hspan₂ : affineSpan ℝ Q = affineSpan ℝ P₂) : P₁ = P₂ := by
  have hQne : Q.Nonempty :=
    (affineSpan_nonempty ℝ).mp (hspan₁.symm ▸ (C.nonempty P₁ hP₁).affineSpan ℝ)
  have hI : P₁ ∩ P₂ ∈ C.cells :=
    C.inter_mem_cells hP₁ hP₂ (hQne.mono (Set.subset_inter hQP₁ hQP₂))
  have hspanI₁ : affineSpan ℝ (P₁ ∩ P₂) = affineSpan ℝ P₁ :=
    le_antisymm (affineSpan_mono ℝ Set.inter_subset_left)
      (hspan₁ ▸ affineSpan_mono ℝ (Set.subset_inter hQP₁ hQP₂))
  have hspanI₂ : affineSpan ℝ (P₁ ∩ P₂) = affineSpan ℝ P₂ :=
    le_antisymm (affineSpan_mono ℝ Set.inter_subset_right)
      (hspan₂ ▸ affineSpan_mono ℝ (Set.subset_inter hQP₁ hQP₂))
  have heq₁ := C.eq_of_subset_of_finrank_direction_le hI hP₁ Set.inter_subset_left
    (by rw [hspanI₁])
  have heq₂ := C.eq_of_subset_of_finrank_direction_le hI hP₂ Set.inter_subset_right
    (by rw [hspanI₂])
  exact heq₁.symm.trans heq₂

/-- A nonempty subset of ambient codimension `k` lies in at most one codimension-`k` cell of `C`. -/
theorem eq_of_subset_of_mem_cellsOfCodimension (C : FinitePolyhedralComplex h) {k : ℕ}
    {Q P₁ P₂ : Set V} (hne : Q.Nonempty)
    (hdim : Module.finrank ℝ (affineSpan ℝ Q).direction + k = Module.finrank ℝ V)
    (hP₁ : P₁ ∈ C.cellsOfCodimension k) (hP₂ : P₂ ∈ C.cellsOfCodimension k)
    (hQP₁ : Q ⊆ P₁) (hQP₂ : Q ⊆ P₂) : P₁ = P₂ := by
  have := h.finiteDimensional
  obtain ⟨hP₁C, hd₁⟩ := mem_cellsOfCodimension.mp hP₁
  obtain ⟨hP₂C, hd₂⟩ := mem_cellsOfCodimension.mp hP₂
  obtain ⟨x, hx⟩ := hne
  have hspan₁ : affineSpan ℝ Q = affineSpan ℝ P₁ := by
    refine AffineSubspace.ext_of_direction_eq ?_
      ⟨x, subset_affineSpan ℝ Q hx, subset_affineSpan ℝ P₁ (hQP₁ hx)⟩
    exact Submodule.eq_of_le_of_finrank_eq
      (AffineSubspace.direction_le (affineSpan_mono ℝ hQP₁)) (by omega)
  have hspan₂ : affineSpan ℝ Q = affineSpan ℝ P₂ := by
    refine AffineSubspace.ext_of_direction_eq ?_
      ⟨x, subset_affineSpan ℝ Q hx, subset_affineSpan ℝ P₂ (hQP₂ hx)⟩
    exact Submodule.eq_of_le_of_finrank_eq
      (AffineSubspace.direction_le (affineSpan_mono ℝ hQP₂)) (by omega)
  exact C.eq_of_subset_of_affineSpan_eq hP₁C hP₂C hQP₁ hQP₂ hspan₁ hspan₂

namespace IsSubdivision

variable {C D : FinitePolyhedralComplex h}

/-- In a subdivision `C` of `D`, every cell `P` of `D` equals the union of the cells `Q` of `C`
contained in `P` that have the same affine span as `P`. -/
theorem cell_eq_biUnion_affineSpan_eq (hCD : C.IsSubdivision D) {P : Set V} (hP : P ∈ D.cells) :
    P = ⋃ Q ∈ C.cells, ⋃ (_ : Q ⊆ P ∧ affineSpan ℝ Q = affineSpan ℝ P), Q := by
  classical
  have := h.finiteDimensional
  let topCells := C.cells.filter fun Q => Q ⊆ P ∧ affineSpan ℝ Q = affineSpan ℝ P
  let lowCells := C.cells.filter fun Q => Q ⊆ P ∧ affineSpan ℝ Q ≠ affineSpan ℝ P
  have hUcl : IsClosed (⋃ Q ∈ topCells, Q) :=
    topCells.finite_toSet.isClosed_biUnion fun Q hQ =>
      (C.isConvexPolyhedron (Finset.mem_filter.mp hQ).1).isClosed
  have hint : intrinsicInterior ℝ P ⊆ ⋃ Q ∈ topCells, Q := by
    intro x hx
    by_contra hxnot
    obtain ⟨hxA, hnhdsP⟩ := TauCeti.mem_intrinsicInterior_iff_eventually.mp hx
    have hnhds : (⋃ Q ∈ topCells, Q)ᶜ ∩ {y | y ∈ affineSpan ℝ P → y ∈ P} ∈ nhds x :=
      Filter.inter_mem (hUcl.isOpen_compl.mem_nhds hxnot) hnhdsP
    have hcov : ∀ y ∈ affineSpan ℝ P,
        y ∈ (⋃ Q ∈ topCells, Q)ᶜ ∩ {y | y ∈ affineSpan ℝ P → y ∈ P} →
        ∃ Q : lowCells, y ∈ affineSpan ℝ Q.val := by
      intro y hyA ⟨hyU, hyP⟩
      obtain ⟨Q, hQC, hQP, hyQ⟩ := hCD.exists_mem_cells_subset hP (hyP hyA)
      have hne : affineSpan ℝ Q ≠ affineSpan ℝ P := fun hspan =>
        hyU (Set.mem_iUnion₂.mpr ⟨Q, Finset.mem_filter.mpr ⟨hQC, hQP, hspan⟩, hyQ⟩)
      exact ⟨⟨Q, Finset.mem_filter.mpr ⟨hQC, hQP, hne⟩⟩, subset_affineSpan ℝ Q hyQ⟩
    obtain ⟨⟨Q, hQlow⟩, hdir⟩ :=
      (affineSpan ℝ P).exists_direction_le_of_forall_mem
        (fun Q : lowCells => affineSpan ℝ Q.val) hxA hnhds hcov
    obtain ⟨hQC, hQP, hne⟩ := Finset.mem_filter.mp hQlow
    obtain ⟨q, hq⟩ := C.nonempty Q hQC
    refine hne (AffineSubspace.ext_of_direction_eq ?_
      ⟨q, subset_affineSpan ℝ Q hq, subset_affineSpan ℝ P (hQP hq)⟩)
    exact le_antisymm (AffineSubspace.direction_le (affineSpan_mono ℝ hQP)) hdir
  have hconv := (D.isConvexPolyhedron hP).convex
  obtain ⟨c, hc⟩ := (D.nonempty P hP).intrinsicInterior hconv
  have hPsub : P ⊆ ⋃ Q ∈ topCells, Q := fun x hx =>
    closure_minimal hint hUcl (closure_mono
      (hconv.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
        hc (subset_intrinsicClosure hx))
      (segment_subset_closure_openSegment (right_mem_segment ℝ c x)))
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    obtain ⟨Q, hQ, hxQ⟩ := Set.mem_iUnion₂.mp (hPsub hx)
    obtain ⟨hQC, hQP⟩ := Finset.mem_filter.mp hQ
    exact Set.mem_iUnion₂.mpr ⟨Q, hQC, Set.mem_iUnion.mpr ⟨hQP, hxQ⟩⟩
  · intro x hx
    obtain ⟨Q, _, hQP, hxQ⟩ := by simpa only [Set.mem_iUnion, exists_prop] using hx
    exact hQP.1 hxQ

/-- Every point of a cell `P` of `D` belongs to a cell `Q` of `C` contained in `P` with the same
affine span as `P`. -/
theorem exists_mem_cells_subset_affineSpan_eq (hCD : C.IsSubdivision D) {P : Set V}
    (hP : P ∈ D.cells) {x : V} (hx : x ∈ P) :
    ∃ Q ∈ C.cells, Q ⊆ P ∧ affineSpan ℝ Q = affineSpan ℝ P ∧ x ∈ Q := by
  have hx' := hx
  rw [hCD.cell_eq_biUnion_affineSpan_eq hP] at hx'
  obtain ⟨Q, hQC, ⟨hQP, hspan⟩, hxQ⟩ := by simpa only [Set.mem_iUnion, exists_prop] using hx'
  exact ⟨Q, hQC, hQP, hspan, hxQ⟩

/-- In a subdivision `C` of `D`, every codimension-`k` cell `P` of `D` equals the union of the
codimension-`k` cells `Q` of `C` contained in `P`. -/
theorem cell_eq_biUnion_cellsOfCodimension (hCD : C.IsSubdivision D) {k : ℕ} {P : Set V}
    (hP : P ∈ D.cellsOfCodimension k) :
    P = ⋃ Q ∈ C.cellsOfCodimension k, ⋃ (_ : Q ⊆ P), Q := by
  have := h.finiteDimensional
  obtain ⟨hPD, hdimP⟩ := mem_cellsOfCodimension.mp hP
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    obtain ⟨Q, hQC, hQP, hspan, hxQ⟩ := hCD.exists_mem_cells_subset_affineSpan_eq hPD hx
    have hQk : Q ∈ C.cellsOfCodimension k :=
      mem_cellsOfCodimension.mpr ⟨hQC, by rwa [hspan]⟩
    exact Set.mem_iUnion₂.mpr ⟨Q, hQk, Set.mem_iUnion.mpr ⟨hQP, hxQ⟩⟩
  · intro x hx
    obtain ⟨Q, _, hQP, hxQ⟩ := by simpa only [Set.mem_iUnion, exists_prop] using hx
    exact hQP hxQ

/-- Every point of a codimension-`k` cell `P` of `D` belongs to a codimension-`k` cell `Q` of `C`
contained in `P`, with the same affine span. -/
theorem exists_mem_cellsOfCodimension_subset (hCD : C.IsSubdivision D) {k : ℕ} {P : Set V}
    (hP : P ∈ D.cellsOfCodimension k) {x : V} (hx : x ∈ P) :
    ∃ Q ∈ C.cellsOfCodimension k, Q ⊆ P ∧ affineSpan ℝ Q = affineSpan ℝ P ∧ x ∈ Q := by
  obtain ⟨hPD, hdimP⟩ := mem_cellsOfCodimension.mp hP
  obtain ⟨Q, hQC, hQP, hspan, hxQ⟩ := hCD.exists_mem_cells_subset_affineSpan_eq hPD hx
  exact ⟨Q, mem_cellsOfCodimension.mpr ⟨hQC, by rwa [hspan]⟩, hQP, hspan, hxQ⟩

/-- Subdividing a complex can only enlarge the union of its cells of a given codimension. -/
theorem biUnion_cellsOfCodimension_subset (hCD : C.IsSubdivision D) (k : ℕ) :
    (⋃ P ∈ D.cellsOfCodimension k, P) ⊆ ⋃ Q ∈ C.cellsOfCodimension k, Q := by
  intro x hx
  obtain ⟨P, hP, hxP⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨Q, hQ, -, -, hxQ⟩ := hCD.exists_mem_cellsOfCodimension_subset hP hxP
  exact Set.mem_iUnion₂.mpr ⟨Q, hQ, hxQ⟩

/-- Subdividing a complex can only enlarge the union of its walls. -/
theorem biUnion_walls_subset (hCD : C.IsSubdivision D) :
    (⋃ P ∈ D.walls, P) ⊆ ⋃ Q ∈ C.walls, Q :=
  hCD.biUnion_cellsOfCodimension_subset 1

end IsSubdivision

end TauCeti.FinitePolyhedralComplex

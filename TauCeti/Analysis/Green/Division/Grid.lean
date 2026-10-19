/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Division.Rectangle

/-!
# Finite square-grid divisions

Every finite selection of integer unit squares has independent vertical and horizontal graph-cell
divisions. Their common boundary is the sum of their actual four-edge boundaries; shared edges
cancel as integer-weighted paths. No connectedness or absence of holes is required.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green

/-- The closed unit square based at an integer lattice point. -/
def latticeSquare (k : ℤ × ℤ) : Set ℂ :=
  verticalRegion k.1 (k.1 + 1) (fun _ ↦ k.2) (fun _ ↦ k.2 + 1)

/-- Membership in a lattice square is given by its two actual coordinate intervals. -/
@[simp]
theorem mem_latticeSquare {k : ℤ × ℤ} {z : ℂ} : z ∈ latticeSquare k ↔
    z.re ∈ Icc (k.1 : ℝ) (k.1 + 1) ∧ z.im ∈ Icc (k.2 : ℝ) (k.2 + 1) := by
  rw [latticeSquare, mem_verticalRegion]

/-- The region of a finite selection of lattice squares, allowing any number of components
and omitted interior squares. -/
def latticeRegion (s : Finset (ℤ × ℤ)) : Set ℂ := ⋃ k ∈ s, latticeSquare k

/-- A point lies in the finite grid region exactly when it lies in one of its selected squares. -/
@[simp]
theorem mem_latticeRegion {s : Finset (ℤ × ℤ)} {z : ℂ} :
    z ∈ latticeRegion s ↔ ∃ k ∈ s, z ∈ latticeSquare k := by
  simp only [latticeRegion, mem_iUnion, exists_prop]

namespace GraphCell

/-- The actual graph cell for an integer unit square, in either coordinate direction. -/
def lattice (d : Coordinate) (k : ℤ × ℤ) : GraphCell :=
  match d with
  | .re => rectangle k.1 (k.1 + 1) k.2 (k.2 + 1) (lt_add_one _) (le_add_of_nonneg_right zero_le_one)
  | .im => rectangle k.2 (k.2 + 1) k.1 (k.1 + 1) (lt_add_one _) (le_add_of_nonneg_right zero_le_one)

/-- Both coordinate presentations have exactly the same geometric square. -/
@[simp]
theorem region_lattice (d : Coordinate) (k : ℤ × ℤ) : (lattice d k).region d = latticeSquare k := by
  cases d <;> ext z <;>
    simp [lattice, mem_latticeSquare, mem_verticalRegion, mem_horizontalRegion, and_comm]

/-- Distinct lattice points give distinct graph cells, in either coordinate direction. -/
theorem lattice_injective (d : Coordinate) : Function.Injective (lattice d) := by
  intro k l h
  have ha := congrArg GraphCell.a h
  have hl := congrArg (fun K : GraphCell ↦ K.lowerFun 0) h
  cases d <;> simp only [lattice, rectangle_a, rectangle_lowerFun] at ha hl
  · exact Prod.ext (Int.cast_injective ha) (Int.cast_injective hl)
  · exact Prod.ext (Int.cast_injective hl) (Int.cast_injective ha)

/-- The type-I and type-II square cells have the same actual chain of paths. -/
theorem boundary_lattice_re_eq_im (k : ℤ × ℤ) :
    (lattice .re k).boundary .re = (lattice .im k).boundary .im := by
  simp only [lattice, boundary_def, rectangle_a, rectangle_b, rectangle_lowerFun,
    rectangle_upperFun]
  exact BoundaryChain.cellBoundary_rectangle_re_eq_im _ _ _ _

/-- A lattice-cell boundary is exactly its four directed segment generators. This formula
makes cancellation of shared grid edges an equality of actual integer-weighted chains. -/
theorem boundary_lattice (k : ℤ × ℤ) : (lattice .re k).boundary .re =
    BoundaryChain.ofPath (Path.segment (⟨k.1, k.2⟩ : ℂ) ⟨k.1 + 1, k.2⟩) +
      BoundaryChain.ofPath (Path.segment (⟨k.1 + 1, k.2⟩ : ℂ) ⟨k.1 + 1, k.2 + 1⟩) -
      BoundaryChain.ofPath (Path.segment (⟨k.1, k.2 + 1⟩ : ℂ) ⟨k.1 + 1, k.2 + 1⟩) -
      BoundaryChain.ofPath (Path.segment (⟨k.1, k.2⟩ : ℂ) ⟨k.1, k.2 + 1⟩) := by
  simp only [lattice, boundary_def, rectangle_a, rectangle_b, rectangle_lowerFun,
    rectangle_upperFun, BoundaryChain.cellBoundary_def, BoundaryChain.graphPath_const,
    Coordinate.orientation_re, one_smul, BoundaryChain.quadrilateral_def]
  have hre (g : ℝ → ℝ) : Coordinate.re.graph g = fun x ↦ (⟨x, g x⟩ : ℂ) :=
    funext (Coordinate.graph_re_apply g)
  rw [hre (fun _ ↦ (k.2 : ℝ)), hre (fun _ ↦ (k.2 : ℝ) + 1)]

end GraphCell

private theorem latticeSquare_aedisjoint {k l : ℤ × ℤ} (hkl : k ≠ l) :
    AEDisjoint volume (latticeSquare k) (latticeSquare l) := by
  have hre (k l : ℤ × ℤ) (hlt : k.1 < l.1) :
      AEDisjoint volume (latticeSquare k) (latticeSquare l) := by
    have hsep : (k.1 : ℝ) + 1 ≤ l.1 := by exact_mod_cast Int.add_one_le_iff.mpr hlt
    apply measure_mono_null (t := {z : ℂ | z.re = l.1})
    · intro z hz
      have hk := mem_latticeSquare.mp hz.1
      have hl := mem_latticeSquare.mp hz.2
      exact le_antisymm (hk.1.2.trans hsep) hl.1.1
    · exact Complex.volume_setOf_re_eq _
  have him (k l : ℤ × ℤ) (hlt : k.2 < l.2) :
      AEDisjoint volume (latticeSquare k) (latticeSquare l) := by
    have hsep : (k.2 : ℝ) + 1 ≤ l.2 := by exact_mod_cast Int.add_one_le_iff.mpr hlt
    apply measure_mono_null (t := {z : ℂ | z.re ∈ Icc (k.1 : ℝ) (k.1 + 1) ∧ z.im = l.2})
    · intro z hz
      have hk := mem_latticeSquare.mp hz.1
      have hl := mem_latticeSquare.mp hz.2
      exact ⟨hk.1, le_antisymm (hk.2.2.trans hsep) hl.2.1⟩
    · exact Complex.volume_setOf_re_mem_Icc_im_eq continuousOn_const
  rcases lt_trichotomy k.1 l.1 with hx | hx | hx
  · exact hre k l hx
  · have hy : k.2 ≠ l.2 := fun hy ↦ hkl (Prod.ext hx hy)
    rcases lt_or_gt_of_ne hy with hy | hy
    · exact him k l hy
    · exact (him l k hy).symm
  · exact (hre l k hx).symm

namespace Division

open scoped Classical in
/-- The finite graph-cell division of any selected lattice squares. Vertical and horizontal
presentations use their respective graph coordinates and share only the geometric region. -/
def lattice (d : Coordinate) (s : Finset (ℤ × ℤ)) : Division d (latticeRegion s) where
  cells := s.image (GraphCell.lattice d)
  covers := by
    ext z
    simp only [Finset.mem_image, exists_prop, iUnion_exists, mem_iUnion, mem_latticeRegion]
    aesop
  aedisjoint := by
    intro K hK L hL hKL
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hL
    simpa only [GraphCell.region_lattice] using
      latticeSquare_aedisjoint (fun h ↦ hKL (congrArg (GraphCell.lattice d) h))

open scoped Classical in
/-- The grid division consists of precisely the selected square cells. -/
@[simp]
theorem lattice_cells (d : Coordinate) (s : Finset (ℤ × ℤ)) :
    (lattice d s).cells = s.image (GraphCell.lattice d) := (rfl)

/-- Its actual boundary is the sum of the selected square-boundary chains. -/
theorem boundary_lattice (d : Coordinate) (s : Finset (ℤ × ℤ)) :
    (lattice d s).boundary = ∑ k ∈ s, (GraphCell.lattice .re k).boundary .re := by
  classical
  rw [boundary_def, lattice_cells, Finset.sum_image (fun k _ l _ h ↦
    GraphCell.lattice_injective d h)]
  apply Finset.sum_congr rfl
  intro k _
  cases d
  · rfl
  · exact (GraphCell.boundary_lattice_re_eq_im k).symm

/-- Every finite square-grid region, including those with holes or several components, has
an actual common boundary cycle and geometric certificates for both directional divisions. -/
theorem exists_lattice_common_boundary (s : Finset (ℤ × ℤ)) (U : Set ℂ) :
    ∃ C : BoundaryChain, BoundaryChain.boundary C = 0 ∧
      BoundaryChain.NullChain .re U ((lattice .re s).boundary - C) ∧
      BoundaryChain.NullChain .im U ((lattice .im s).boundary - C) := by
  refine ⟨(lattice .re s).boundary, boundary_boundary _, ?_, ?_⟩
  · simpa only [sub_self] using (BoundaryChain.NullChain.zero : BoundaryChain.NullChain .re U 0)
  · rw [boundary_lattice, boundary_lattice, sub_self]
    exact .zero

end Division
end TauCeti.Green

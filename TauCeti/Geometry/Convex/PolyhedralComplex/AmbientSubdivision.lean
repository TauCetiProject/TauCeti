/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Convex.PolyhedralComplex.Basic
public import TauCeti.Analysis.Convex.Polyhedron.SignCell.Face
public import TauCeti.Analysis.Convex.Polyhedron.SignCell.Rational

/-!
# Ambient subdivisions by affine arrangements

The closures of realized sign cells of a finite rational-normal affine
arrangement form a finite polyhedral complex covering the ambient space.
Applying this construction to all defining rows of a finite family of presented
polyhedra expresses every input carrier as a union of cells of one complex.
Redundant and constant rows, empty inputs, unbounded cells and lineality are allowed.
Restricting rows or input presentations coarsens this subdivision, including repeated rows,
and the zero locus of each defining row is itself a union of cells.

The construction uses the existing realized sign-cell closure family and its
closure under faces. It is therefore extensional in the actual closed cell
carriers rather than retaining duplicate sign assignments as cells.

Adapted from `Mei/Geometry/Convex/PolyhedralComplex/AmbientSubdivision.lean` at commit
`bf3986029ff4d3eb4025d4067489511b0724374e` of
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei) (Apache 2.0).
-/

public section

open TauCeti (FinitePolyhedralComplex)

open TauCeti (RationalAffinePolyhedron)
open TauCeti.Convex (closure_signCell finite_realizedSignCellClosures
  isConvexPolyhedron_of_mem_realizedSignCellClosures
  isExtreme_inter_of_mem_realizedSignCellClosures
  isRationalNormalPolyhedron_of_mem_realizedSignCellClosures mem_realizedSignCellClosures
  mem_signCell_sign nonempty_of_mem_realizedSignCellClosures realizedSignCellClosures
  sUnion_realizedSignCellClosures signCell)

namespace TauCeti.FinitePolyhedralComplex

open Set

variable {N V ι : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} [Finite ι]

/-- The finite complex of closures of the realized sign cells of a rational-normal
affine arrangement. Its support is the entire ambient space. -/
noncomputable def ofArrangement (g : ι → (V →ᴬ[ℝ] ℝ))
    (hg : ∀ j, TauCeti.Toric.IsRationalFunctional h (g j).toAffineMap.linear) :
    FinitePolyhedralComplex h where
  cells := (finite_realizedSignCellClosures g).toFinset
  nonempty P hP := nonempty_of_mem_realizedSignCellClosures (by simpa using hP)
  rational P hP := isRationalNormalPolyhedron_of_mem_realizedSignCellClosures hg
    (by simpa using hP)
  face_closed P hP F hF := by
    have hPF := hF.isExposed.isExtreme.mem_realizedSignCellClosures (by simpa using hP)
      (hF.isExposed.convex (isConvexPolyhedron_of_mem_realizedSignCellClosures
        (by simpa using hP)).convex) hF.nonempty
    simpa using hPF
  inter_face P hP Q hQ _ := by
    have hP' : P ∈ realizedSignCellClosures g := by simpa using hP
    have hQ' : Q ∈ realizedSignCellClosures g := by simpa using hQ
    exact (isExtreme_inter_of_mem_realizedSignCellClosures hP' hQ').isExposed_of_isConvexPolyhedron
      (isConvexPolyhedron_of_mem_realizedSignCellClosures hP')
      ((isConvexPolyhedron_of_mem_realizedSignCellClosures hP').convex.inter
        (isConvexPolyhedron_of_mem_realizedSignCellClosures hQ').convex)

/-- The cells are exactly the actual closures of nonempty strict sign cells. -/
@[simp]
theorem mem_cells_ofArrangement {g : ι → (V →ᴬ[ℝ] ℝ)}
    {hg : ∀ j, TauCeti.Toric.IsRationalFunctional h (g j).toAffineMap.linear} {P : Set V} :
    P ∈ (ofArrangement g hg).cells ↔
      ∃ σ, (signCell g σ).Nonempty ∧ P = closure (signCell g σ) := by
  simp [ofArrangement]

/-- A finite affine arrangement subdivides all of the ambient space. -/
@[simp]
theorem support_ofArrangement (g : ι → (V →ᴬ[ℝ] ℝ))
    (hg : ∀ j, TauCeti.Toric.IsRationalFunctional h (g j).toAffineMap.linear) :
    (ofArrangement g hg).support = Set.univ := by
  ext x
  simp only [mem_support, mem_cells_ofArrangement]
  simpa only [Set.mem_sUnion, mem_realizedSignCellClosures]
    using Set.ext_iff.mp (sUnion_realizedSignCellClosures g) x

/-- The ambient subdivision obtained from every defining row of a finite family
of presented rational-normal polyhedra. The family may be empty. -/
noncomputable def ambientSubdivision (P : ι → RationalAffinePolyhedron h) :
    FinitePolyhedralComplex h :=
  ofArrangement (fun j : Σ a, Fin (P a).numConstraints => (P j.1).inequality j.2)
    (fun j => (P j.1).rational_linear j.2)

/-- Ambient subdivision cells are closures of realized sign cells of the combined
family of all the input inequalities. -/
@[simp]
theorem mem_cells_ambientSubdivision {P : ι → RationalAffinePolyhedron h} {Q : Set V} :
    Q ∈ (ambientSubdivision P).cells ↔
      ∃ σ, (signCell (fun j : Σ a, Fin (P a).numConstraints =>
        (P j.1).inequality j.2) σ).Nonempty ∧
        Q = closure (signCell (fun j : Σ a, Fin (P a).numConstraints =>
          (P j.1).inequality j.2) σ) := by
  exact mem_cells_ofArrangement

/-- The ambient subdivision covers the entire ambient space, even for empty or
inconsistent input presentations. -/
@[simp]
theorem support_ambientSubdivision (P : ι → RationalAffinePolyhedron h) :
    (ambientSubdivision P).support = Set.univ :=
  support_ofArrangement _ _

/-- Each point of an input polyhedron lies in a subdivision cell entirely
contained in that polyhedron. -/
theorem exists_mem_cells_ambientSubdivision_subset
    (P : ι → RationalAffinePolyhedron h) (a : ι) {x : V} (hx : x ∈ (P a).carrier) :
    ∃ Q ∈ (ambientSubdivision P).cells, x ∈ Q ∧ Q ⊆ (P a).carrier := by
  let g := fun j : Σ a, Fin (P a).numConstraints => (P j.1).inequality j.2
  let σ := fun j => SignType.sign (g j x)
  have hsign : x ∈ signCell g σ := mem_signCell_sign g x
  refine ⟨closure (signCell g σ),
    mem_cells_ambientSubdivision.mpr ⟨σ, ⟨x, hsign⟩, rfl⟩, subset_closure hsign, ?_⟩
  apply closure_minimal ?_ (P a).isClosed
  intro y hy
  apply RationalAffinePolyhedron.mem_carrier.mpr
  intro j
  apply sign_nonpos_iff.mp
  rw [TauCeti.Convex.mem_signCell.mp hy ⟨a, j⟩]
  exact sign_nonpos_iff.mpr (RationalAffinePolyhedron.mem_carrier.mp hx j)

/-- Every input carrier is exactly the union of subdivision cells contained in it. -/
theorem carrier_eq_iUnion_ambientSubdivision_cells
    (P : ι → RationalAffinePolyhedron h) (a : ι) :
    (P a).carrier = ⋃ (Q : Set V) (_ : Q ∈ (ambientSubdivision P).cells)
      (_ : Q ⊆ (P a).carrier), Q := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · intro hx
    obtain ⟨Q, hQ, hxQ, hsub⟩ := exists_mem_cells_ambientSubdivision_subset P a hx
    exact ⟨Q, hQ, hsub, hxQ⟩
  · rintro ⟨Q, _, hsub, hxQ⟩
    exact hsub hxQ

/-- Restricting the rows of an arrangement coarsens its complex. The row map
need not be injective: repeated inequalities do not change the conclusion. -/
theorem ofArrangement_isSubdivision_comp {κ : Type*} [Finite κ]
    (g : ι → (V →ᴬ[ℝ] ℝ))
    (hg : ∀ j, TauCeti.Toric.IsRationalFunctional h (g j).toAffineMap.linear) (f : κ → ι) :
    (ofArrangement g hg).IsSubdivision
      (ofArrangement (g ∘ f) (fun j => hg (f j))) := by
  apply isSubdivision_iff.mpr
  refine ⟨?_, by simp⟩
  apply isWeakRefinement_iff.mpr
  intro P hP
  obtain ⟨σ, ⟨x, hx⟩, rfl⟩ := mem_cells_ofArrangement.mp hP
  have hsub : signCell g σ ⊆ signCell (g ∘ f) (σ ∘ f) :=
    fun y hy => TauCeti.Convex.mem_signCell.mpr (fun j => TauCeti.Convex.mem_signCell.mp hy (f j))
  exact ⟨closure (signCell (g ∘ f) (σ ∘ f)),
    mem_cells_ofArrangement.mpr ⟨σ ∘ f, ⟨x, hsub hx⟩, rfl⟩, closure_mono hsub⟩

/-- Restricting a finite input family coarsens its ambient subdivision. Repetitions
in the original or restricted family are allowed. -/
theorem ambientSubdivision_isSubdivision_comp {κ : Type*} [Finite κ]
    (P : ι → RationalAffinePolyhedron h) (f : κ → ι) :
    (ambientSubdivision P).IsSubdivision (ambientSubdivision (P ∘ f)) :=
  ofArrangement_isSubdivision_comp
    (fun j : Σ a, Fin (P a).numConstraints => (P j.1).inequality j.2)
    (fun j => (P j.1).rational_linear j.2)
    (fun j : Σ a, Fin (P (f a)).numConstraints => ⟨f j.1, j.2⟩)

/-- The zero locus of each row is a union of cells of the arrangement, including constant rows. -/
theorem zeroLocus_eq_iUnion_ofArrangement_cells (g : ι → (V →ᴬ[ℝ] ℝ))
    (hg : ∀ j, TauCeti.Toric.IsRationalFunctional h (g j).toAffineMap.linear) (j : ι) :
    {x | g j x = 0} = ⋃ (P : Set V) (_ : P ∈ (ofArrangement g hg).cells)
      (_ : P ⊆ {x | g j x = 0}), P := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · intro hx
    let σ := fun a => SignType.sign (g a x)
    have hσ : x ∈ signCell g σ := mem_signCell_sign g x
    refine ⟨closure (signCell g σ),
      mem_cells_ofArrangement.mpr ⟨σ, ⟨x, hσ⟩, rfl⟩, ?_, subset_closure hσ⟩
    rw [closure_signCell ⟨x, hσ⟩]
    intro y hy
    exact (TauCeti.Convex.mem_weakSignCell.mp hy j).1 (by simp [σ, hx])
  · rintro ⟨P, _, hP, hxP⟩
    exact hP hxP

end TauCeti.FinitePolyhedralComplex

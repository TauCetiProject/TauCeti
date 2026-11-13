/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import Mathlib.Geometry.Convex.Cone.Pointed
public import TauCeti.Analysis.Convex.Exposed
public import TauCeti.Analysis.Convex.Polyhedron.Rational.Basic

/-!
# Finite rational-normal polyhedral complexes

A `TauCeti.FinitePolyhedralComplex` in a finite-dimensional real normed space with an integral
lattice is a finite set of nonempty closed rational-normal polyhedra (its cells) which is closed
under taking nonempty faces and in which any two cells meet in a common face. Cells may be
unbounded and may have nonzero lineality, and no full-dimensionality condition is imposed.

A face of a cell `P` is a nonempty exposed subset (`TauCeti.IsPolyhedralFace`): the set where a
continuous linear functional attains its maximum on `P`. For a cell this is the same as
`P ∩ {ℓ = c}` for a functional `ℓ` bounded above by `c` on `P`.

The support of a complex is the union of its cells. Distinct cells have disjoint intrinsic
interiors (`TauCeti.FinitePolyhedralComplex.disjoint_intrinsicInterior`), and a cell containing a
point of the intrinsic interior of another cell contains it entirely. The cells of codimension one
and two are its walls and joints. A complex `C` is a weak
refinement of `D` when each cell of `C` lies in a cell of `D`, and a subdivision when moreover the
supports agree. Both relations are reflexive, transitive and antisymmetric. A subcomplex is a
complex whose cells are among the cells of another. A conical complex
(`TauCeti.FinitePolyhedralComplex.IsConical`) has cone carriers as cells, and each subcomplex
of a conical complex is conical. The simplest example is
`TauCeti.FinitePolyhedralComplex.univ`, whose only cell is the whole space.

Adapted from `Mei/Geometry/Convex/PolyhedralComplex/Basic.lean` and `Subcomplex.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0). The conicality predicate
is adapted from `Mei/Geometry/Convex/PolyhedralComplex/Basic.lean` at commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f` in the same repository.
-/

public section

namespace TauCeti

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V}

/-- `F` is a (nonempty) face of the polyhedron `P`: a nonempty subset of `P` on which some
continuous linear functional attains its maximum over `P`. -/
structure IsPolyhedralFace (P F : Set V) : Prop where
  /-- Faces are nonempty. -/
  nonempty : F.Nonempty
  /-- A face is the set of maximizers on `P` of a continuous linear functional. -/
  isExposed : IsExposed ℝ P F

variable (h : TauCeti.Toric.IsIntegralLattice i)

/-- A finite complex of rational-normal polyhedra, allowing unbounded cells and lineality. -/
@[ext]
structure FinitePolyhedralComplex where
  /-- The finite collection of closed cell carriers. -/
  cells : Finset (Set V)
  /-- Empty cells are excluded. -/
  nonempty : ∀ P ∈ cells, P.Nonempty
  /-- Every cell admits a rational-normal finite affine presentation. -/
  rational : ∀ P ∈ cells, IsRationalNormalPolyhedron h P
  /-- Every nonempty face of a cell is a cell. -/
  face_closed : ∀ P ∈ cells, ∀ F, IsPolyhedralFace P F → F ∈ cells
  /-- Two cells that meet intersect in a face of the first; swapping the cells gives the other. -/
  inter_face : ∀ P ∈ cells, ∀ Q ∈ cells, (P ∩ Q).Nonempty → IsExposed ℝ P (P ∩ Q)

namespace FinitePolyhedralComplex

variable {h}

/-- The support of a complex is the union of its cells. -/
def support (C : FinitePolyhedralComplex h) : Set V := ⋃ P ∈ C.cells, P

@[simp]
theorem mem_support {C : FinitePolyhedralComplex h} {x : V} :
    x ∈ C.support ↔ ∃ P ∈ C.cells, x ∈ P := by simp [support]

theorem subset_support {C : FinitePolyhedralComplex h} {P : Set V} (hP : P ∈ C.cells) :
    P ⊆ C.support :=
  fun _ hx => mem_support.mpr ⟨P, hP, hx⟩

/-- Each cell is a convex polyhedron. -/
theorem isConvexPolyhedron (C : FinitePolyhedralComplex h) {P : Set V} (hP : P ∈ C.cells) :
    TauCeti.IsConvexPolyhedron P :=
  (C.rational P hP).isConvexPolyhedron

/-- A nonempty intersection of two cells is again a cell. -/
theorem inter_mem_cells (C : FinitePolyhedralComplex h) {P Q : Set V}
    (hP : P ∈ C.cells) (hQ : Q ∈ C.cells) (hne : (P ∩ Q).Nonempty) : P ∩ Q ∈ C.cells :=
  C.face_closed P hP (P ∩ Q) ⟨hne, C.inter_face P hP Q hQ hne⟩

/-- A cell containing a point of the intrinsic interior of another cell contains that whole
cell. -/
theorem subset_of_mem_intrinsicInterior (C : FinitePolyhedralComplex h) {P Q : Set V}
    (hP : P ∈ C.cells) (hQ : Q ∈ C.cells) {x : V}
    (hxP : x ∈ intrinsicInterior ℝ P) (hxQ : x ∈ Q) : P ⊆ Q := by
  have hx : x ∈ P ∩ Q := ⟨intrinsicInterior_subset hxP, hxQ⟩
  exact Set.inter_eq_left.mp
    ((C.inter_face P hP Q hQ ⟨x, hx⟩).eq_of_mem_intrinsicInterior hx hxP)

/-- Cells with a common point in their intrinsic interiors are equal. -/
theorem eq_of_mem_intrinsicInterior (C : FinitePolyhedralComplex h) {P Q : Set V}
    (hP : P ∈ C.cells) (hQ : Q ∈ C.cells) {x : V}
    (hxP : x ∈ intrinsicInterior ℝ P) (hxQ : x ∈ intrinsicInterior ℝ Q) : P = Q :=
  Set.Subset.antisymm
    (C.subset_of_mem_intrinsicInterior hP hQ hxP (intrinsicInterior_subset hxQ))
    (C.subset_of_mem_intrinsicInterior hQ hP hxQ (intrinsicInterior_subset hxP))

/-- The intrinsic interiors of distinct cells are disjoint. -/
theorem disjoint_intrinsicInterior (C : FinitePolyhedralComplex h) {P Q : Set V}
    (hP : P ∈ C.cells) (hQ : Q ∈ C.cells) (hne : P ≠ Q) :
    Disjoint (intrinsicInterior ℝ P) (intrinsicInterior ℝ Q) :=
  Set.disjoint_left.mpr fun _ hxP hxQ => hne (C.eq_of_mem_intrinsicInterior hP hQ hxP hxQ)

/-- A cell contained in another cell is a face of it. -/
theorem isPolyhedralFace_of_subset (C : FinitePolyhedralComplex h) {P Q : Set V}
    (hP : P ∈ C.cells) (hQ : Q ∈ C.cells) (hPQ : P ⊆ Q) : IsPolyhedralFace Q P := by
  have heq : Q ∩ P = P := Set.inter_eq_right.mpr hPQ
  have hne : (Q ∩ P).Nonempty := by rw [heq]; exact C.nonempty P hP
  exact ⟨C.nonempty P hP, heq ▸ C.inter_face Q hQ P hP hne⟩

/-- A complex `C` weakly refines `D` when every cell of `C` lies in a cell of `D`. -/
def IsWeakRefinement (C D : FinitePolyhedralComplex h) : Prop :=
  ∀ P ∈ C.cells, ∃ Q ∈ D.cells, P ⊆ Q

theorem isWeakRefinement_iff {C D : FinitePolyhedralComplex h} :
    C.IsWeakRefinement D ↔ ∀ P ∈ C.cells, ∃ Q ∈ D.cells, P ⊆ Q := Iff.rfl

/-- A complex `C` subdivides `D` when it weakly refines `D` and has the same support. -/
def IsSubdivision (C D : FinitePolyhedralComplex h) : Prop :=
  C.IsWeakRefinement D ∧ C.support = D.support

theorem isSubdivision_iff {C D : FinitePolyhedralComplex h} :
    C.IsSubdivision D ↔ C.IsWeakRefinement D ∧ C.support = D.support := Iff.rfl

@[refl]
theorem IsWeakRefinement.refl (C : FinitePolyhedralComplex h) : C.IsWeakRefinement C :=
  fun P hP => ⟨P, hP, Set.Subset.rfl⟩

@[trans]
theorem IsWeakRefinement.trans {C D E : FinitePolyhedralComplex h}
    (hCD : C.IsWeakRefinement D) (hDE : D.IsWeakRefinement E) : C.IsWeakRefinement E := by
  intro P hP
  obtain ⟨Q, hQ, hPQ⟩ := hCD P hP
  obtain ⟨R, hR, hQR⟩ := hDE Q hQ
  exact ⟨R, hR, hPQ.trans hQR⟩

/-- The support of a weak refinement lies in the support of the complex it refines. -/
theorem IsWeakRefinement.support_subset {C D : FinitePolyhedralComplex h}
    (hCD : C.IsWeakRefinement D) : C.support ⊆ D.support := by
  intro x hx
  obtain ⟨P, hP, hxP⟩ := mem_support.mp hx
  obtain ⟨Q, hQ, hPQ⟩ := hCD P hP
  exact mem_support.mpr ⟨Q, hQ, hPQ hxP⟩

/-- Complexes which weakly refine each other are equal, since both contain all faces of their
cells. -/
theorem IsWeakRefinement.antisymm {C D : FinitePolyhedralComplex h}
    (hCD : C.IsWeakRefinement D) (hDC : D.IsWeakRefinement C) : C = D := by
  have hsubset {C D : FinitePolyhedralComplex h}
      (hCD : C.IsWeakRefinement D) (hDC : D.IsWeakRefinement C) : C.cells ⊆ D.cells := by
    intro P hP
    obtain ⟨Q, hQ, hPQ⟩ := hCD P hP
    obtain ⟨R, hR, hQR⟩ := hDC Q hQ
    have hface := C.isPolyhedralFace_of_subset hP hR (hPQ.trans hQR)
    have hexposed : IsExposed ℝ Q P := by
      simpa only [Set.inter_eq_right.mpr hQR] using hface.isExposed.inter_left hPQ
    exact D.face_closed Q hQ P ⟨hface.nonempty, hexposed⟩
  exact FinitePolyhedralComplex.ext (Finset.Subset.antisymm (hsubset hCD hDC) (hsubset hDC hCD))

@[refl]
theorem IsSubdivision.refl (C : FinitePolyhedralComplex h) : C.IsSubdivision C :=
  ⟨.refl C, rfl⟩

@[trans]
theorem IsSubdivision.trans {C D E : FinitePolyhedralComplex h}
    (hCD : C.IsSubdivision D) (hDE : D.IsSubdivision E) : C.IsSubdivision E :=
  ⟨hCD.1.trans hDE.1, hCD.2.trans hDE.2⟩

theorem IsSubdivision.antisymm {C D : FinitePolyhedralComplex h}
    (hCD : C.IsSubdivision D) (hDC : D.IsSubdivision C) : C = D :=
  hCD.1.antisymm hDC.1

/-- In a subdivision `C` of `D`, every point of a cell of `D` lies in a cell of `C` contained in
that cell. -/
theorem IsSubdivision.exists_mem_cells_subset {C D : FinitePolyhedralComplex h}
    (hCD : C.IsSubdivision D) {P : Set V} (hP : P ∈ D.cells) {x : V} (hx : x ∈ P) :
    ∃ Q ∈ C.cells, Q ⊆ P ∧ x ∈ Q := by
  obtain ⟨hrefine, hsupport⟩ := hCD
  obtain ⟨Q, hQ, hxQ⟩ := mem_support.mp (hsupport ▸ subset_support hP hx)
  obtain ⟨R, hR, hQR⟩ := hrefine Q hQ
  have hF : IsExposed ℝ Q ((R ∩ P) ∩ Q) :=
    (D.inter_face R hR P hP ⟨x, hQR hxQ, hx⟩).inter_of_subset hQR
  exact ⟨(R ∩ P) ∩ Q, C.face_closed Q hQ _ ⟨⟨x, ⟨hQR hxQ, hx⟩, hxQ⟩, hF⟩,
    fun _ hy => hy.1.2, ⟨hQR hxQ, hx⟩, hxQ⟩

/-- Every cell is the carrier of a pointed cone with apex zero. -/
def IsConical (C : FinitePolyhedralComplex h) : Prop :=
  ∀ P ∈ C.cells, ∃ σ : PointedCone ℝ V, (σ : Set V) = P

/-- Conicality means that each actual cell carrier is a cone. -/
theorem isConical_iff {C : FinitePolyhedralComplex h} :
    C.IsConical ↔ ∀ P ∈ C.cells, ∃ σ : PointedCone ℝ V, (σ : Set V) = P := Iff.rfl

/-- `C` is a subcomplex of `D` when every cell of `C` is a cell of `D`. -/
def IsSubcomplex (C D : FinitePolyhedralComplex h) : Prop := C.cells ⊆ D.cells

theorem isSubcomplex_iff {C D : FinitePolyhedralComplex h} :
    C.IsSubcomplex D ↔ C.cells ⊆ D.cells := Iff.rfl

@[refl]
theorem IsSubcomplex.refl (C : FinitePolyhedralComplex h) : C.IsSubcomplex C :=
  Finset.Subset.refl _

@[trans]
theorem IsSubcomplex.trans {C D E : FinitePolyhedralComplex h}
    (hCD : C.IsSubcomplex D) (hDE : D.IsSubcomplex E) : C.IsSubcomplex E :=
  Finset.Subset.trans hCD hDE

theorem IsSubcomplex.antisymm {C D : FinitePolyhedralComplex h}
    (hCD : C.IsSubcomplex D) (hDC : D.IsSubcomplex C) : C = D :=
  FinitePolyhedralComplex.ext (Finset.Subset.antisymm hCD hDC)

/-- A subcomplex inherits conicality from its ambient complex. -/
theorem IsSubcomplex.isConical {C D : FinitePolyhedralComplex h}
    (hCD : C.IsSubcomplex D) (hD : D.IsConical) : C.IsConical :=
  isConical_iff.mpr fun P hP => isConical_iff.mp hD P (isSubcomplex_iff.mp hCD hP)

/-- A subcomplex is a weak refinement of its ambient complex. -/
theorem IsSubcomplex.isWeakRefinement {C D : FinitePolyhedralComplex h}
    (hCD : C.IsSubcomplex D) : C.IsWeakRefinement D :=
  fun P hP => ⟨P, hCD hP, Set.Subset.rfl⟩

variable (h) in
/-- The complex whose only cell is the whole space. -/
def univ : FinitePolyhedralComplex h where
  cells := {Set.univ}
  nonempty P hP := by
    obtain rfl := Finset.mem_singleton.mp hP
    exact Set.univ_nonempty
  rational P hP := by
    obtain rfl := Finset.mem_singleton.mp hP
    exact .univ h
  face_closed P hP F hF := by
    obtain rfl := Finset.mem_singleton.mp hP
    obtain ⟨x, hx⟩ := hF.nonempty
    obtain ⟨l, rfl⟩ := hF.isExposed ⟨x, hx⟩
    refine Finset.mem_singleton.mpr (Set.eq_univ_of_forall fun z => ⟨trivial, fun y _ => ?_⟩)
    simpa using hx.2 (y - z + x) trivial
  inter_face P hP Q hQ _ := by
    obtain rfl := Finset.mem_singleton.mp hP
    obtain rfl := Finset.mem_singleton.mp hQ
    simpa using IsExposed.refl Set.univ

@[simp]
theorem cells_univ : (univ h).cells = {Set.univ} := by
  simp [univ]

theorem mem_cells_univ {P : Set V} : P ∈ (univ h).cells ↔ P = Set.univ := by
  simp

/-- The only cell of the whole-space complex is the carrier of the top cone. -/
@[simp]
theorem isConical_univ : (univ h).IsConical := by
  refine isConical_iff.mpr fun P hP => ?_
  exact ⟨⊤, (mem_cells_univ.mp hP).symm⟩

@[simp]
theorem support_univ : (univ h).support = Set.univ := by
  simp [support, univ]

/-- The cells of ambient codimension exactly `k`: those for which the dimension of the affine
direction plus `k` equals `finrank V`. In particular, there are no such cells when `k` exceeds the
ambient dimension. -/
noncomputable def cellsOfCodimension (C : FinitePolyhedralComplex h) (k : ℕ) : Finset (Set V) :=
  open scoped Classical in
  C.cells.filter fun P => Module.finrank ℝ (affineSpan ℝ P).direction + k = Module.finrank ℝ V

@[simp]
theorem mem_cellsOfCodimension {C : FinitePolyhedralComplex h} {k : ℕ} {P : Set V} :
    P ∈ C.cellsOfCodimension k ↔
      P ∈ C.cells ∧ Module.finrank ℝ (affineSpan ℝ P).direction + k = Module.finrank ℝ V := by
  simp [cellsOfCodimension]

/-- The walls of a complex are its cells of codimension one. -/
noncomputable abbrev walls (C : FinitePolyhedralComplex h) : Finset (Set V) :=
  C.cellsOfCodimension 1

/-- The joints of a complex are its cells of codimension two. -/
noncomputable abbrev joints (C : FinitePolyhedralComplex h) : Finset (Set V) :=
  C.cellsOfCodimension 2

end FinitePolyhedralComplex

end TauCeti

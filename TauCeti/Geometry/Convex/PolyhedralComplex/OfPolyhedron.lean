/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import TauCeti.Geometry.Convex.PolyhedralComplex.Basic
public import TauCeti.Analysis.Convex.Polyhedron.Rational.Face

/-!
# The complex of a polyhedron and its faces

The complex `FinitePolyhedralComplex.ofPolyhedron` of a rational-normal polyhedron `P` has as cells
the nonempty exposed faces of `P`; in particular `P` is a cell exactly when it is nonempty. No
boundedness, salience or rationality of the offsets is assumed, so `P` may be unbounded, have
lineality, or be a point with irrational coordinates.

Adapted from `Mei/Geometry/Convex/PolyhedralComplex/OfPolyhedron/Basic.lean` at
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f` (Apache 2.0).

The cells of the complex are exactly the nonempty exposed faces of `P`
(`FinitePolyhedralComplex.mem_cells_ofPolyhedron`), and its support is `P`
(`FinitePolyhedralComplex.support_ofPolyhedron`). For a polyhedron, exposed faces of exposed
faces are exposed faces, and the intersection of two faces is a face of each of them; this is
what makes the cells a complex. If `P` is a cell of a complex `C`, then the complex of `P` is a
subcomplex of `C` (`FinitePolyhedralComplex.ofPolyhedron_isSubcomplex`). A subdivision of the
face complex is characterized by equality of supports; a weak refinement into it only requires
containment of the support. Inclusion of two face complexes is equivalent to exposure of the
first polyhedron as a face of the second.
-/

public section

namespace TauCeti

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

namespace FinitePolyhedralComplex

variable (h)

/-- The complex of a rational-normal polyhedron `P`: its cells are the nonempty exposed faces of
`P`. -/
noncomputable def ofPolyhedron (P : Set V) (hP : IsRationalNormalPolyhedron h P) :
    FinitePolyhedralComplex h :=
  have hfin : {F : Set V | IsPolyhedralFace P F}.Finite :=
    hP.isConvexPolyhedron.finite_setOf_isExposed.subset fun _ hF => hF.isExposed
  have hface {F : Set V} (hF : F ∈ hfin.toFinset) := hfin.mem_toFinset.mp hF
  { cells := hfin.toFinset
    nonempty _ hF := (hface hF).nonempty
    rational _ hF := (hface hF).isExposed.isExtreme.isRationalNormalPolyhedron hP
      ((hface hF).isExposed.convex hP.convex)
    face_closed _ hF _ hG := hfin.mem_toFinset.mpr
      ⟨hG.nonempty, (hface hF).isExposed.trans_of_isConvexPolyhedron
        hG.isExposed hP.isConvexPolyhedron⟩
    inter_face _ hF _ hG _ := by
      simpa only [Set.inter_comm] using
        (hface hG).isExposed.inter_of_subset (hface hF).isExposed.subset }

variable {h} {P : Set V} (hP : IsRationalNormalPolyhedron h P)

/-- The cells of the complex of a polyhedron are its nonempty exposed faces. -/
@[simp]
theorem mem_cells_ofPolyhedron {F : Set V} :
    F ∈ (ofPolyhedron h P hP).cells ↔ IsPolyhedralFace P F :=
  Set.Finite.mem_toFinset _

/-- A polyhedron occurs as a cell of its face complex exactly when it is nonempty. -/
theorem self_mem_cells_ofPolyhedron_iff : P ∈ (ofPolyhedron h P hP).cells ↔ P.Nonempty :=
  (mem_cells_ofPolyhedron hP).trans ⟨fun hF => hF.nonempty, fun hne => ⟨hne, IsExposed.refl P⟩⟩

/-- A nonempty polyhedron is a cell of its own complex. -/
theorem self_mem_cells_ofPolyhedron (hne : P.Nonempty) : P ∈ (ofPolyhedron h P hP).cells :=
  (self_mem_cells_ofPolyhedron_iff hP).mpr hne

/-- A polyhedron is the support of its complex. -/
@[simp]
theorem support_ofPolyhedron : (ofPolyhedron h P hP).support = P := by
  ext x
  rw [mem_support]
  constructor
  · rintro ⟨F, hF, hxF⟩
    exact ((mem_cells_ofPolyhedron hP).mp hF).isExposed.subset hxF
  · exact fun hx => ⟨P, self_mem_cells_ofPolyhedron hP ⟨x, hx⟩, hx⟩

/-- A face complex determines its polyhedron. -/
@[simp]
theorem ofPolyhedron_inj {Q : Set V} (hQ : IsRationalNormalPolyhedron h Q) :
    ofPolyhedron h P hP = ofPolyhedron h Q hQ ↔ P = Q := by
  refine ⟨fun e => ?_, fun e => by subst Q; rfl⟩
  simpa only [support_ofPolyhedron] using congrArg support e

/-- A face complex has a cell exactly when its polyhedron has a point. -/
@[simp]
theorem cells_ofPolyhedron_nonempty : (ofPolyhedron h P hP).cells.Nonempty ↔ P.Nonempty := by
  refine ⟨fun ⟨F, hF⟩ => ?_, fun hne => ⟨P, self_mem_cells_ofPolyhedron hP hne⟩⟩
  have hf := (mem_cells_ofPolyhedron hP).mp hF
  exact hf.nonempty.mono hf.isExposed.subset

/-- A face complex has no cells exactly when its polyhedron is empty. -/
@[simp]
theorem cells_ofPolyhedron_eq_empty : (ofPolyhedron h P hP).cells = ∅ ↔ P = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty, cells_ofPolyhedron_nonempty,
    Set.not_nonempty_iff_eq_empty]

/-- The empty polyhedron has no nonempty faces. -/
@[simp]
theorem cells_ofPolyhedron_empty (hempty : IsRationalNormalPolyhedron h (∅ : Set V)) :
    (ofPolyhedron h ∅ hempty).cells = ∅ :=
  (cells_ofPolyhedron_eq_empty hempty).mpr rfl

/-- A complex weakly refines the face complex of `P` exactly when its support lies in `P`. -/
@[simp]
theorem isWeakRefinement_ofPolyhedron (C : FinitePolyhedralComplex h) :
    C.IsWeakRefinement (ofPolyhedron h P hP) ↔ C.support ⊆ P := by
  refine ⟨fun href => ?_, fun hsub => isWeakRefinement_iff.mpr fun F hF => ?_⟩
  · simpa only [support_ofPolyhedron] using href.support_subset
  · have hFP := (subset_support hF).trans hsub
    exact ⟨P, self_mem_cells_ofPolyhedron hP ((C.nonempty F hF).mono hFP), hFP⟩

/-- A complex subdivides the face complex of a polyhedron exactly when its support equals it. -/
@[simp]
theorem isSubdivision_ofPolyhedron (C : FinitePolyhedralComplex h) :
    C.IsSubdivision (ofPolyhedron h P hP) ↔ C.support = P := by
  rw [isSubdivision_iff, isWeakRefinement_ofPolyhedron, support_ofPolyhedron]
  exact ⟨And.right, fun e => ⟨e.subset, e⟩⟩

/-- The face complex of `P` weakly refines `C` exactly when `P`, if nonempty, lies in a cell of
`C`. -/
theorem ofPolyhedron_isWeakRefinement_iff (C : FinitePolyhedralComplex h) :
    (ofPolyhedron h P hP).IsWeakRefinement C ↔ P.Nonempty → ∃ Q ∈ C.cells, P ⊆ Q := by
  refine ⟨fun href hne => isWeakRefinement_iff.mp href P (self_mem_cells_ofPolyhedron hP hne),
    fun hcell => isWeakRefinement_iff.mpr fun F hF => ?_⟩
  have hf := (mem_cells_ofPolyhedron hP).mp hF
  obtain ⟨Q, hQ, hPQ⟩ := hcell (hf.nonempty.mono hf.isExposed.subset)
  exact ⟨Q, hQ, hf.isExposed.subset.trans hPQ⟩

/-- If a polyhedron is a cell of a complex, its complex of faces is a subcomplex. -/
theorem ofPolyhedron_isSubcomplex (C : FinitePolyhedralComplex h) (hPC : P ∈ C.cells) :
    (ofPolyhedron h P (C.rational P hPC)).IsSubcomplex C :=
  isSubcomplex_iff.mpr fun F hF =>
    C.face_closed P hPC F ((mem_cells_ofPolyhedron (C.rational P hPC)).mp hF)

/-- The face complex of `P` is a subcomplex of `C` exactly when `P`, if nonempty, is a cell of
`C`. -/
theorem ofPolyhedron_isSubcomplex_iff (C : FinitePolyhedralComplex h) :
    (ofPolyhedron h P hP).IsSubcomplex C ↔ P.Nonempty → P ∈ C.cells := by
  refine ⟨fun hsub hne => isSubcomplex_iff.mp hsub (self_mem_cells_ofPolyhedron hP hne),
    fun hcell => isSubcomplex_iff.mpr fun _ hF => ?_⟩
  have hf := (mem_cells_ofPolyhedron hP).mp hF
  exact C.face_closed P (hcell (hf.nonempty.mono hf.isExposed.subset)) _ hf

/-- Inclusion between two face complexes is exactly the exposed-face relation. -/
@[simp]
theorem ofPolyhedron_isSubcomplex_ofPolyhedron {Q : Set V}
    (hQ : IsRationalNormalPolyhedron h Q) :
    (ofPolyhedron h P hP).IsSubcomplex (ofPolyhedron h Q hQ) ↔ IsExposed ℝ Q P := by
  rw [ofPolyhedron_isSubcomplex_iff, mem_cells_ofPolyhedron]
  exact ⟨fun hface hne => (hface hne).isExposed hne, fun hexp hne => ⟨hne, hexp⟩⟩

/-- The face complex of the whole space is the complex with the single cell `Set.univ`. -/
theorem ofPolyhedron_univ (hU : IsRationalNormalPolyhedron h (Set.univ : Set V)) :
    ofPolyhedron h Set.univ hU = univ h := by
  apply IsSubcomplex.antisymm
  · exact (ofPolyhedron_isSubcomplex_iff hU _).mpr fun _ => mem_cells_univ.mpr rfl
  · apply isSubcomplex_iff.mpr
    intro F hF
    obtain rfl := mem_cells_univ.mp hF
    exact self_mem_cells_ofPolyhedron hU Set.univ_nonempty

end FinitePolyhedralComplex

end TauCeti

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
subcomplex of `C` (`FinitePolyhedralComplex.isSubcomplex_ofPolyhedron`).
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

/-- A nonempty polyhedron is a cell of its own complex. -/
theorem self_mem_cells_ofPolyhedron (hne : P.Nonempty) : P ∈ (ofPolyhedron h P hP).cells :=
  (mem_cells_ofPolyhedron hP).mpr ⟨hne, IsExposed.refl P⟩

/-- A polyhedron is the support of its complex. -/
@[simp]
theorem support_ofPolyhedron : (ofPolyhedron h P hP).support = P := by
  ext x
  rw [mem_support]
  constructor
  · rintro ⟨F, hF, hxF⟩
    exact ((mem_cells_ofPolyhedron hP).mp hF).isExposed.subset hxF
  · exact fun hx => ⟨P, self_mem_cells_ofPolyhedron hP ⟨x, hx⟩, hx⟩

/-- If a polyhedron is a cell of a complex, its complex of faces is a subcomplex. -/
theorem isSubcomplex_ofPolyhedron (C : FinitePolyhedralComplex h) (hPC : P ∈ C.cells) :
    (ofPolyhedron h P (C.rational P hPC)).IsSubcomplex C :=
  isSubcomplex_iff.mpr fun F hF =>
    C.face_closed P hPC F ((mem_cells_ofPolyhedron (C.rational P hPC)).mp hF)

end FinitePolyhedralComplex

end TauCeti

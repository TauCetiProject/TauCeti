/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Convex.PolyhedralComplex.Basic
public import TauCeti.Analysis.Convex.Polyhedron.Face.Intersection

/-!
# Common refinements of finite rational-normal polyhedral complexes

The cells are exactly the nonempty intersections of original cell carriers.
Face closure follows from the active-inequality face decomposition for an
intersection of polyhedra. The support is the intersection of the supports,
and every common weak refinement weakly refines this complex. Equal supports
therefore give an actual common subdivision. Lineality is allowed.

Adapted from `Mei/Geometry/Convex/PolyhedralComplex/CommonRefinement.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `7f1e4c7714fb020473694755ad8748c8f15d0e7f` (Apache 2.0).
-/

public section

namespace TauCeti.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- The finite family of nonempty intersections before bundling the complex. -/
private noncomputable def commonCells (C D : FinitePolyhedralComplex h) : Finset (Set V) := by
  classical
  exact ((C.cells ×ˢ D.cells).filter (fun p => (p.1 ∩ p.2).Nonempty)).image
    (fun p => p.1 ∩ p.2)

/-- Membership in the finite intersection family records both original cells. -/
private theorem mem_commonCells {C D : FinitePolyhedralComplex h} {R : Set V} :
    R ∈ commonCells C D ↔ ∃ P ∈ C.cells, ∃ Q ∈ D.cells, (P ∩ Q).Nonempty ∧ P ∩ Q = R := by
  classical
  constructor
  · intro hR
    obtain ⟨⟨P, Q⟩, hpq, rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨hpq, hne⟩ := Finset.mem_filter.mp hpq
    obtain ⟨hP, hQ⟩ := Finset.mem_product.mp hpq
    exact ⟨P, hP, Q, hQ, hne, rfl⟩
  · rintro ⟨P, hP, Q, hQ, hne, rfl⟩
    exact Finset.mem_image.mpr ⟨(P, Q),
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hP, hQ⟩, hne⟩, rfl⟩

/-- The common refinement consists of all nonempty pairwise intersections of cells. -/
noncomputable def commonRefinement (C D : FinitePolyhedralComplex h) :
    FinitePolyhedralComplex h where
  cells := commonCells C D
  nonempty := by
    intro R hR
    obtain ⟨P, _, Q, _, hne, rfl⟩ := mem_commonCells.mp hR
    exact hne
  rational := by
    intro R hR
    obtain ⟨P, hP, Q, hQ, _, rfl⟩ := mem_commonCells.mp hR
    exact (C.rational P hP).inter (D.rational Q hQ)
  face_closed := by
    intro R hR F hF
    obtain ⟨P, hP, Q, hQ, _, rfl⟩ := mem_commonCells.mp hR
    obtain ⟨F₁, F₂, hF₁, hF₂, hne₁, hne₂, heq⟩ :=
      hF.isExposed.exists_inter_of_isConvexPolyhedron (C.isConvexPolyhedron hP)
        (D.isConvexPolyhedron hQ) hF.nonempty
    apply mem_commonCells.mpr
    exact ⟨F₁, C.face_closed P hP F₁ ⟨hne₁, hF₁⟩,
      F₂, D.face_closed Q hQ F₂ ⟨hne₂, hF₂⟩, heq ▸ hF.nonempty, heq.symm⟩
  inter_face := by
    intro R hR S hS hne
    obtain ⟨P, hP, Q, hQ, _, rfl⟩ := mem_commonCells.mp hR
    obtain ⟨P', hP', Q', hQ', _, rfl⟩ := mem_commonCells.mp hS
    obtain ⟨x, hx⟩ := hne
    have hC := C.inter_face P hP P' hP' ⟨x, hx.1.1, hx.2.1⟩
    have hD := D.inter_face Q hQ Q' hQ' ⟨x, hx.1.2, hx.2.2⟩
    have heq : (P ∩ P') ∩ (Q ∩ Q') = (P ∩ Q) ∩ (P' ∩ Q') :=
      Set.inter_inter_inter_comm P P' Q Q'
    simpa only [heq] using hC.inter_inter hD

/-- The public carrier characterization of the cells of a common refinement. -/
@[simp]
theorem mem_commonRefinement_cells {C D : FinitePolyhedralComplex h} {R : Set V} :
    R ∈ (C.commonRefinement D).cells ↔
      ∃ P ∈ C.cells, ∃ Q ∈ D.cells, (P ∩ Q).Nonempty ∧ P ∩ Q = R := by
  simp only [commonRefinement, mem_commonCells]

/-- The support of the common refinement is exactly the intersection of supports. -/
@[simp]
theorem support_commonRefinement (C D : FinitePolyhedralComplex h) :
    (C.commonRefinement D).support = C.support ∩ D.support := by
  ext x
  constructor
  · intro hx
    obtain ⟨R, hR, hxR⟩ := mem_support.mp hx
    obtain ⟨P, hP, Q, hQ, _, rfl⟩ := mem_commonRefinement_cells.mp hR
    exact ⟨mem_support.mpr ⟨P, hP, hxR.1⟩, mem_support.mpr ⟨Q, hQ, hxR.2⟩⟩
  · rintro ⟨hxC, hxD⟩
    obtain ⟨P, hP, hxP⟩ := mem_support.mp hxC
    obtain ⟨Q, hQ, hxQ⟩ := mem_support.mp hxD
    exact mem_support.mpr ⟨P ∩ Q,
      mem_commonRefinement_cells.mpr ⟨P, hP, Q, hQ, ⟨x, hxP, hxQ⟩, rfl⟩, hxP, hxQ⟩

/-- The common refinement weakly refines its first complex. -/
theorem commonRefinement_isWeakRefinement_left (C D : FinitePolyhedralComplex h) :
    (C.commonRefinement D).IsWeakRefinement C := by
  apply isWeakRefinement_iff.mpr
  intro R hR
  obtain ⟨P, hP, Q, _, _, rfl⟩ := mem_commonRefinement_cells.mp hR
  exact ⟨P, hP, Set.inter_subset_left⟩

/-- The common refinement weakly refines its second complex. -/
theorem commonRefinement_isWeakRefinement_right (C D : FinitePolyhedralComplex h) :
    (C.commonRefinement D).IsWeakRefinement D := by
  apply isWeakRefinement_iff.mpr
  intro R hR
  obtain ⟨P, _, Q, hQ, _, rfl⟩ := mem_commonRefinement_cells.mp hR
  exact ⟨Q, hQ, Set.inter_subset_right⟩

/-- Every common weak refinement weakly refines the intersection complex. -/
theorem isWeakRefinement_commonRefinement {C D E : FinitePolyhedralComplex h}
    (hEC : E.IsWeakRefinement C) (hED : E.IsWeakRefinement D) :
    E.IsWeakRefinement (C.commonRefinement D) := by
  apply isWeakRefinement_iff.mpr
  intro R hR
  obtain ⟨P, hP, hRP⟩ := isWeakRefinement_iff.mp hEC R hR
  obtain ⟨Q, hQ, hRQ⟩ := isWeakRefinement_iff.mp hED R hR
  obtain ⟨x, hx⟩ := E.nonempty R hR
  exact ⟨P ∩ Q, mem_commonRefinement_cells.mpr
    ⟨P, hP, Q, hQ, ⟨x, hRP hx, hRQ hx⟩, rfl⟩, fun y hy => ⟨hRP hy, hRQ hy⟩⟩

/-- Weakly refining a common refinement is equivalent to weakly refining both originals. -/
theorem isWeakRefinement_commonRefinement_iff {C D E : FinitePolyhedralComplex h} :
    E.IsWeakRefinement (C.commonRefinement D) ↔ E.IsWeakRefinement C ∧ E.IsWeakRefinement D := by
  constructor
  · intro hE
    exact ⟨hE.trans (commonRefinement_isWeakRefinement_left C D),
      hE.trans (commonRefinement_isWeakRefinement_right C D)⟩
  · rintro ⟨hEC, hED⟩
    exact isWeakRefinement_commonRefinement hEC hED

/-- If the first support is contained in the second, the common refinement subdivides it. -/
theorem commonRefinement_isSubdivision_left {C D : FinitePolyhedralComplex h}
    (hsupport : C.support ⊆ D.support) : (C.commonRefinement D).IsSubdivision C := by
  apply isSubdivision_iff.mpr
  refine ⟨commonRefinement_isWeakRefinement_left C D, ?_⟩
  rw [support_commonRefinement, Set.inter_eq_left.mpr hsupport]

/-- If the second support is contained in the first, the common refinement subdivides it. -/
theorem commonRefinement_isSubdivision_right {C D : FinitePolyhedralComplex h}
    (hsupport : D.support ⊆ C.support) : (C.commonRefinement D).IsSubdivision D := by
  apply isSubdivision_iff.mpr
  refine ⟨commonRefinement_isWeakRefinement_right C D, ?_⟩
  rw [support_commonRefinement, Set.inter_eq_right.mpr hsupport]

/-- Common refinement is independent of the order of its two inputs. -/
theorem commonRefinement_comm (C D : FinitePolyhedralComplex h) :
    C.commonRefinement D = D.commonRefinement C := by
  apply IsWeakRefinement.antisymm
  · exact isWeakRefinement_commonRefinement (commonRefinement_isWeakRefinement_right C D)
      (commonRefinement_isWeakRefinement_left C D)
  · exact isWeakRefinement_commonRefinement (commonRefinement_isWeakRefinement_right D C)
      (commonRefinement_isWeakRefinement_left D C)

/-- Taking the common refinement of a complex with itself retains exactly its cells. -/
@[simp]
theorem commonRefinement_self (C : FinitePolyhedralComplex h) : C.commonRefinement C = C := by
  apply IsWeakRefinement.antisymm (commonRefinement_isWeakRefinement_left C C)
  exact isWeakRefinement_commonRefinement (IsWeakRefinement.refl C) (IsWeakRefinement.refl C)

end TauCeti.FinitePolyhedralComplex

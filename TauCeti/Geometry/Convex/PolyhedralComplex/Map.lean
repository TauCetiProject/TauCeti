/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Rational.Map
public import TauCeti.Geometry.Convex.PolyhedralComplex.Basic

/-!
# Integral affine transport of finite polyhedral complexes

An integral affine equivalence `e` carries every cell of a `TauCeti.FinitePolyhedralComplex` to its
image. Exposed sets are preserved by continuous affine equivalences, so faces of image cells are
images of faces, and rational normals are transported by the existing presentation API (the
translation of `e` and the offsets of the presentations are arbitrary). The image complex has
support `e '' C.support` (`TauCeti.FinitePolyhedralComplex.support_image`), and transport preserves
weak refinements, subdivisions, subcomplexes and the cells of each ambient codimension.

Adapted from `Mei/Geometry/Convex/PolyhedralComplex/Map.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).
-/

public section

variable {N N' V W : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedAddCommGroup W] [NormedSpace ℝ V] [NormedSpace ℝ W]
  {i : N →+ V} {i' : N' →+ W}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}

/-- Integral affine equivalences preserve exposed subsets. -/
theorem IsExposed.image_integralAffineEquiv {P F : Set V} (hF : IsExposed ℝ P F)
    (e : TauCeti.Toric.IntegralAffineEquiv h h') : IsExposed ℝ (e '' P) (e '' F) := by
  simpa using hF.image_continuousAffineEquiv e.toContinuousAffineEquiv

namespace TauCeti

/-- Integral affine equivalences preserve faces. -/
theorem IsPolyhedralFace.image {P F : Set V} (hF : IsPolyhedralFace P F)
    (e : Toric.IntegralAffineEquiv h h') : IsPolyhedralFace (e '' P) (e '' F) :=
  ⟨hF.nonempty.image e, hF.isExposed.image_integralAffineEquiv e⟩

namespace FinitePolyhedralComplex

/-- Transport the cells of a complex by an integral affine equivalence. -/
noncomputable def image (C : FinitePolyhedralComplex h) (e : Toric.IntegralAffineEquiv h h') :
    FinitePolyhedralComplex h' :=
  open scoped Classical in
  { cells := C.cells.image (e '' ·)
    nonempty := by
      intro P hP
      obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
      exact (C.nonempty Q hQ).image e
    rational := by
      intro P hP
      obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
      exact (C.rational Q hQ).image e
    face_closed := by
      intro P hP F hF
      obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
      have hback : IsPolyhedralFace Q (e.symm '' F) := by
        simpa only [e.symm_image_image] using hF.image e.symm
      exact Finset.mem_image.mpr ⟨e.symm '' F, C.face_closed Q hQ _ hback, e.image_symm_image F⟩
    inter_face := by
      intro P hP Q hQ hne
      obtain ⟨P₀, hP₀, rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨Q₀, hQ₀, rfl⟩ := Finset.mem_image.mp hQ
      rw [← Set.image_inter e.toAffineEquiv.injective] at hne ⊢
      exact (C.inter_face P₀ hP₀ Q₀ hQ₀ hne.of_image).image_integralAffineEquiv e }

@[simp]
theorem mem_cells_image {C : FinitePolyhedralComplex h} {e : Toric.IntegralAffineEquiv h h'}
    {P : Set W} : P ∈ (C.image e).cells ↔ ∃ Q ∈ C.cells, e '' Q = P := by
  classical
  exact Finset.mem_image

@[simp]
theorem support_image (C : FinitePolyhedralComplex h) (e : Toric.IntegralAffineEquiv h h') :
    (C.image e).support = e '' C.support := by
  ext x
  simp only [mem_support, mem_cells_image, Set.mem_image]
  aesop

@[simp]
theorem image_refl (C : FinitePolyhedralComplex h) :
    C.image (Toric.IntegralAffineEquiv.refl h) = C := by
  ext P
  simp [mem_cells_image]

theorem image_trans {N'' U : Type*} [AddCommGroup N''] [NormedAddCommGroup U] [NormedSpace ℝ U]
    {i'' : N'' →+ U} {h'' : Toric.IsIntegralLattice i''} (C : FinitePolyhedralComplex h)
    (e : Toric.IntegralAffineEquiv h h') (f : Toric.IntegralAffineEquiv h' h'') :
    (C.image e).image f = C.image (e.trans f) := by
  ext P
  simp [mem_cells_image, Set.image_image]

/-- Integral affine transport preserves weak refinement. -/
theorem IsWeakRefinement.image {C D : FinitePolyhedralComplex h} (hCD : C.IsWeakRefinement D)
    (e : Toric.IntegralAffineEquiv h h') : (C.image e).IsWeakRefinement (D.image e) := by
  rw [isWeakRefinement_iff] at hCD ⊢
  intro P hP
  obtain ⟨Q, hQ, rfl⟩ := mem_cells_image.mp hP
  obtain ⟨R, hR, hQR⟩ := hCD Q hQ
  exact ⟨e '' R, mem_cells_image.mpr ⟨R, hR, rfl⟩, Set.image_mono hQR⟩

/-- Integral affine transport preserves subdivision. -/
theorem IsSubdivision.image {C D : FinitePolyhedralComplex h} (hCD : C.IsSubdivision D)
    (e : Toric.IntegralAffineEquiv h h') : (C.image e).IsSubdivision (D.image e) :=
  isSubdivision_iff.mpr ⟨(isSubdivision_iff.mp hCD).1.image e, by
    rw [support_image, support_image, (isSubdivision_iff.mp hCD).2]⟩

/-- Integral affine transport preserves subcomplexes. -/
theorem IsSubcomplex.image {C D : FinitePolyhedralComplex h} (hCD : C.IsSubcomplex D)
    (e : Toric.IntegralAffineEquiv h h') : (C.image e).IsSubcomplex (D.image e) := by
  rw [isSubcomplex_iff] at hCD ⊢
  intro P hP
  obtain ⟨Q, hQ, rfl⟩ := mem_cells_image.mp hP
  exact mem_cells_image.mpr ⟨Q, hCD hQ, rfl⟩

/-- Integral affine transport carries the cells of each ambient codimension to the cells of the
same codimension of the image complex. -/
theorem mem_cellsOfCodimension_image (C : FinitePolyhedralComplex h)
    (e : Toric.IntegralAffineEquiv h h') (k : ℕ) (Q : Set W) :
    Q ∈ (C.image e).cellsOfCodimension k ↔ ∃ P ∈ C.cellsOfCodimension k, e '' P = Q := by
  have hd (P : Set V) : Module.finrank ℝ (affineSpan ℝ (e '' P)).direction =
      Module.finrank ℝ (affineSpan ℝ P).direction := by
    rw [direction_affineSpan, direction_affineSpan, ← AffineEquiv.coe_toAffineMap,
      ← AffineMap.map_vectorSpan]
    exact e.toAffineEquiv.linear.finrank_map_eq _
  have hv := e.toAffineEquiv.linear.finrank_eq
  simp only [mem_cellsOfCodimension, mem_cells_image]
  constructor
  · rintro ⟨⟨P, hP, rfl⟩, hdim⟩
    exact ⟨P, ⟨hP, by rwa [hd, ← hv] at hdim⟩, rfl⟩
  · rintro ⟨P, ⟨hP, hdim⟩, rfl⟩
    exact ⟨⟨P, hP, rfl⟩, by rw [hd, ← hv]; exact hdim⟩

end FinitePolyhedralComplex

end TauCeti

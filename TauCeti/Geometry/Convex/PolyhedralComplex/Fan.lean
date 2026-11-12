/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Convex.PolyhedralComplex.Basic
public import TauCeti.Analysis.Convex.Polyhedron.Rational.Cone
public import TauCeti.Geometry.Convex.Cone.Face.Exposed
public import TauCeti.Geometry.Toric.Algebraic.Fan.Subdivision

/-!
# Conical polyhedral complexes and toric fans

Finite polyhedral complexes whose cells are salient cones are precisely toric
fans. The conversions retain the actual cell carriers, are inverse, preserve
supports, and identify the subdivision relations.

The construction uses `TauCeti.Toric.Fan` and `PointedCone.IsFaceOf` rather than
introducing a second fan carrier. Rational cone duality identifies rational-normal
polyhedral cones with lattice-rational cones, and exposed faces identify the
affine and conical face conventions.

Adapted from `Mei/Geometry/Convex/PolyhedralComplex/Fan.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `7f1e4c7714fb020473694755ad8748c8f15d0e7f` (Apache 2.0).
The `IsConical` predicate in the complex owner is adapted from
`Mei/Geometry/Convex/PolyhedralComplex/Basic.lean` at the same commit.
-/

public section

open TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V}

namespace TauCeti.Toric.Fan

/-- Regard the cones of a toric fan as the cells of a finite polyhedral complex. -/
noncomputable def toPolyhedralComplex (Φ : Fan i) : TauCeti.FinitePolyhedralComplex Φ.lattice := by
  classical
  exact {
    cells := Φ.finite_cones.toFinset.image (fun σ : PointedCone ℝ V => (σ : Set V))
    nonempty P hP := by
      obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hP
      exact ⟨0, σ.zero_mem⟩
    rational P hP := by
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hP
      exact (TauCeti.isRationalNormalPolyhedron_coe_iff (h := Φ.lattice)).mpr
        (Φ.isToricCone (Φ.finite_cones.mem_toFinset.mp hσ)).rational
    face_closed P hP S hS := by
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨τ, hτ, rfl⟩ := hS.isExposed.exists_isFaceOf_coe_eq hS.nonempty
      exact Finset.mem_image.mpr ⟨τ, Φ.finite_cones.mem_toFinset.mpr
        (Φ.mem_of_isFaceOf (Φ.finite_cones.mem_toFinset.mp hσ) hτ), rfl⟩
    inter_face P hP Q hQ _ := by
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hQ
      exact (Φ.inf_isFaceOf_left (Φ.finite_cones.mem_toFinset.mp hσ)
        (Φ.finite_cones.mem_toFinset.mp hτ)).isExposed_of_fg
          (Φ.isToricCone (Φ.finite_cones.mem_toFinset.mp hσ)).fg }

/-- The cells of a fan's complex are exactly its cone carriers. -/
@[simp]
theorem mem_toPolyhedralComplex_cells (Φ : Fan i) (P : Set V) :
    P ∈ Φ.toPolyhedralComplex.cells ↔ ∃ σ ∈ Φ.cones, (σ : Set V) = P := by
  classical
  simp [toPolyhedralComplex]

/-- Passing from a fan to its complex retains its support. -/
@[simp]
theorem support_toPolyhedralComplex (Φ : Fan i) :
    Φ.toPolyhedralComplex.support = Φ.support := by
  ext x
  simp only [TauCeti.FinitePolyhedralComplex.mem_support, mem_toPolyhedralComplex_cells,
    mem_support]
  aesop

open TauCeti.FinitePolyhedralComplex

/-- The complex associated to a fan is conical. -/
theorem isConical_toPolyhedralComplex (Φ : Fan i) : Φ.toPolyhedralComplex.IsConical := by
  apply (isConical_iff _).mpr
  intro P hP
  obtain ⟨σ, _, hσ⟩ := (Φ.mem_toPolyhedralComplex_cells P).mp hP
  exact ⟨σ, hσ⟩

/-- Every cone cell in the complex of a toric fan is salient. -/
theorem salient_toPolyhedralComplex (Φ : Fan i) (σ : PointedCone ℝ V)
    (hσ : (σ : Set V) ∈ Φ.toPolyhedralComplex.cells) : (σ : ConvexCone ℝ V).Salient := by
  obtain ⟨τ, hτ, heq⟩ := (Φ.mem_toPolyhedralComplex_cells _).mp hσ
  have : τ = σ := SetLike.coe_injective heq
  exact this ▸ (Φ.isToricCone hτ).salient

end TauCeti.Toric.Fan

namespace TauCeti.FinitePolyhedralComplex

variable {h : IsIntegralLattice i}

/-- The cone cells of a complex form a toric fan when they are salient. -/
def toFan (C : FinitePolyhedralComplex h)
    (hsal : ∀ σ : PointedCone ℝ V, (σ : Set V) ∈ C.cells →
      (σ : ConvexCone ℝ V).Salient) : Fan i where
  lattice := h
  cones := {σ | (σ : Set V) ∈ C.cells}
  finite_cones := C.cells.finite_toSet.preimage SetLike.coe_injective.injOn
  isToricCone {σ} hσ :=
    ⟨(TauCeti.isRationalNormalPolyhedron_coe_iff (h := h)).mp (C.rational _ hσ), hsal _ hσ⟩
  mem_of_isFaceOf {σ τ} hσ hτ := by
    exact C.face_closed _ hσ _ (show TauCeti.IsPolyhedralFace _ _ from ⟨⟨0, τ.zero_mem⟩,
      hτ.isExposed_of_fg ((TauCeti.isRationalNormalPolyhedron_coe_iff (h := h)).mp
        (C.rational _ hσ)).fg⟩)
  inf_isFaceOf_left {σ τ} hσ hτ := by
    have hne : ((σ : Set V) ∩ (τ : Set V)).Nonempty := ⟨0, σ.zero_mem, τ.zero_mem⟩
    obtain ⟨F, hF, heq⟩ := (C.inter_face _ hσ _ hτ hne).exists_isFaceOf_coe_eq hne
    have heq' : F = σ ⊓ τ := SetLike.coe_injective heq
    exact heq' ▸ hF

/-- A cone belongs to the associated fan exactly when its carrier is a cell. -/
@[simp]
theorem mem_toFan_cones (C : FinitePolyhedralComplex h) (hsal)
    (σ : PointedCone ℝ V) : σ ∈ (C.toFan hsal).cones ↔ (σ : Set V) ∈ C.cells :=
  Iff.rfl

/-- Converting a conical complex to a fan retains its support. -/
@[simp]
theorem support_toFan (C : FinitePolyhedralComplex h) (hc : C.IsConical) (hsal) :
    (C.toFan hsal).support = C.support := by
  ext x
  simp only [Fan.mem_support, mem_toFan_cones, mem_support]
  constructor
  · rintro ⟨σ, hσ, hx⟩
    exact ⟨σ, hσ, hx⟩
  · rintro ⟨P, hP, hx⟩
    obtain ⟨σ, rfl⟩ := (isConical_iff C).mp hc P hP
    exact ⟨σ, hP, hx⟩

/-- Converting a conical complex to a fan and back recovers the complex. -/
@[simp]
theorem toPolyhedralComplex_toFan (C : FinitePolyhedralComplex h) (hc : C.IsConical)
    (hsal) : (C.toFan hsal).toPolyhedralComplex = C := by
  apply FinitePolyhedralComplex.ext
  ext P
  simp only [Fan.mem_toPolyhedralComplex_cells, mem_toFan_cones]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact hσ
  · intro hP
    obtain ⟨σ, hσ⟩ := (isConical_iff C).mp hc P hP
    exact ⟨σ, hσ ▸ hP, hσ⟩

end TauCeti.FinitePolyhedralComplex

namespace TauCeti.Toric.Fan

open TauCeti.FinitePolyhedralComplex

/-- Converting a fan to its complex and back recovers the fan. -/
@[simp]
theorem toFan_toPolyhedralComplex (Φ : Fan i) :
    Φ.toPolyhedralComplex.toFan (salient_toPolyhedralComplex Φ) = Φ := by
  apply Fan.ext
  ext σ
  simp only [mem_toFan_cones, mem_toPolyhedralComplex_cells]
  constructor
  · rintro ⟨τ, hτ, heq⟩
    exact SetLike.coe_injective heq ▸ hτ
  · intro hσ
    exact ⟨σ, hσ, rfl⟩

/-- Fan subdivision agrees exactly with subdivision of the associated polyhedral complexes. -/
theorem isSubdivision_iff_toPolyhedralComplex (Φ Ψ : Fan i) :
    Φ.IsSubdivision Ψ ↔ Φ.toPolyhedralComplex.IsSubdivision Ψ.toPolyhedralComplex := by
  constructor
  · intro hsub
    apply TauCeti.FinitePolyhedralComplex.isSubdivision_iff.mpr
    refine ⟨?_, by simpa using hsub.support_eq⟩
    apply TauCeti.FinitePolyhedralComplex.isWeakRefinement_iff.mpr
    intro P hP
    obtain ⟨σ, hσ, rfl⟩ := (Φ.mem_toPolyhedralComplex_cells P).mp hP
    obtain ⟨τ, hτ, hστ⟩ := hsub.exists_cone_le hσ
    exact ⟨τ, (Ψ.mem_toPolyhedralComplex_cells _).mpr ⟨τ, hτ, rfl⟩, hστ⟩
  · intro hsub
    have hsub := TauCeti.FinitePolyhedralComplex.isSubdivision_iff.mp hsub
    refine ⟨?_, by simpa using hsub.2⟩
    intro σ hσ
    obtain ⟨Q, hQ, hσQ⟩ :=
      (TauCeti.FinitePolyhedralComplex.isWeakRefinement_iff.mp hsub.1) (σ : Set V)
      ((Φ.mem_toPolyhedralComplex_cells _).mpr ⟨σ, hσ, rfl⟩)
    obtain ⟨τ, hτ, rfl⟩ := (Ψ.mem_toPolyhedralComplex_cells Q).mp hQ
    exact ⟨τ, hτ, hσQ⟩

end TauCeti.Toric.Fan

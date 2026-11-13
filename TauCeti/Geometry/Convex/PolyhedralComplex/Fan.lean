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

A toric fan can be studied within the geometry of polyhedral complexes, which also allows
affine cells and lineality. `TauCeti.Toric.Fan.toFinitePolyhedralComplex` takes the cone carriers
as cells and preserves support. For a finite polyhedral complex whose cone cells are salient,
`TauCeti.FinitePolyhedralComplex.toFan` extracts precisely those cone cells. When the complex is
conical, this recovers every cell, preserves the support and inverts the fan-to-complex
construction. Subdivision of conical complexes with salient cone cells then agrees with fan
subdivision.

Rational cone duality characterizes the lattice-rational cones among rational-normal polyhedra.
Exposed faces of a polyhedral cone identify its polyhedral faces with its cone faces.

Adapted from `Mei/Geometry/Convex/PolyhedralComplex/Fan.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `7f1e4c7714fb020473694755ad8748c8f15d0e7f` (Apache 2.0).
-/

public section

open TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V}

namespace TauCeti.Toric.Fan

/-- Regard the cones of a toric fan as the cells of a finite polyhedral complex. -/
noncomputable def toFinitePolyhedralComplex (Φ : Fan i) :
    TauCeti.FinitePolyhedralComplex Φ.lattice := by
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
theorem mem_cells_toFinitePolyhedralComplex (Φ : Fan i) (P : Set V) :
    P ∈ Φ.toFinitePolyhedralComplex.cells ↔ ∃ σ ∈ Φ.cones, (σ : Set V) = P := by
  classical
  simp [toFinitePolyhedralComplex]

/-- Passing from a fan to its complex retains its support. -/
@[simp]
theorem support_toFinitePolyhedralComplex (Φ : Fan i) :
    Φ.toFinitePolyhedralComplex.support = Φ.support := by
  ext x
  simp only [TauCeti.FinitePolyhedralComplex.mem_support, mem_cells_toFinitePolyhedralComplex,
    mem_support]
  aesop

open TauCeti.FinitePolyhedralComplex

/-- The complex associated to a fan is conical. -/
@[simp]
theorem isConical_toFinitePolyhedralComplex (Φ : Fan i) :
    Φ.toFinitePolyhedralComplex.IsConical := by
  apply isConical_iff.mpr
  intro P hP
  obtain ⟨σ, _, hσ⟩ := (Φ.mem_cells_toFinitePolyhedralComplex P).mp hP
  exact ⟨σ, hσ⟩

/-- Every cone cell in the complex of a toric fan is salient. -/
theorem salient_of_mem_cells_toFinitePolyhedralComplex (Φ : Fan i) (σ : PointedCone ℝ V)
    (hσ : (σ : Set V) ∈ Φ.toFinitePolyhedralComplex.cells) : (σ : ConvexCone ℝ V).Salient := by
  obtain ⟨τ, hτ, heq⟩ := (Φ.mem_cells_toFinitePolyhedralComplex _).mp hσ
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
    obtain ⟨σ, rfl⟩ := isConical_iff.mp hc P hP
    exact ⟨σ, hP, hx⟩

/-- Converting a conical complex to a fan and back recovers the complex. -/
@[simp]
theorem toFinitePolyhedralComplex_toFan (C : FinitePolyhedralComplex h) (hc : C.IsConical)
    (hsal) : (C.toFan hsal).toFinitePolyhedralComplex = C := by
  apply FinitePolyhedralComplex.ext
  ext P
  simp only [Fan.mem_cells_toFinitePolyhedralComplex, mem_toFan_cones]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact hσ
  · intro hP
    obtain ⟨σ, hσ⟩ := isConical_iff.mp hc P hP
    exact ⟨σ, hσ ▸ hP, hσ⟩

end TauCeti.FinitePolyhedralComplex

namespace TauCeti.Toric.Fan

open TauCeti.FinitePolyhedralComplex

/-- Converting a fan to its complex and back recovers the fan. -/
@[simp]
theorem toFan_toFinitePolyhedralComplex (Φ : Fan i) :
    Φ.toFinitePolyhedralComplex.toFan (salient_of_mem_cells_toFinitePolyhedralComplex Φ) = Φ := by
  apply Fan.ext
  ext σ
  simp only [mem_toFan_cones, mem_cells_toFinitePolyhedralComplex]
  constructor
  · rintro ⟨τ, hτ, heq⟩
    exact SetLike.coe_injective heq ▸ hτ
  · intro hσ
    exact ⟨σ, hσ, rfl⟩

/-- A fan is determined by its associated complex. -/
@[simp]
theorem toFinitePolyhedralComplex_inj {Φ Ψ : Fan i} :
    Φ.toFinitePolyhedralComplex = Ψ.toFinitePolyhedralComplex ↔ Φ = Ψ := by
  constructor
  · intro heq
    apply Fan.ext
    ext σ
    have h (Θ : Fan i) : (σ : Set V) ∈ Θ.toFinitePolyhedralComplex.cells ↔ σ ∈ Θ.cones := by
      simp
    rw [← h Φ, ← h Ψ, heq]
  · rintro rfl
    rfl

/-- Subdivision of the complexes of two fans agrees with subdivision of the fans. -/
@[simp]
theorem isSubdivision_toFinitePolyhedralComplex_iff {Φ Ψ : Fan i} :
    Φ.toFinitePolyhedralComplex.IsSubdivision Ψ.toFinitePolyhedralComplex ↔ Φ.IsSubdivision Ψ := by
  constructor
  · intro hsub
    have hsub := TauCeti.FinitePolyhedralComplex.isSubdivision_iff.mp hsub
    refine ⟨?_, by simpa using hsub.2⟩
    intro σ hσ
    obtain ⟨Q, hQ, hσQ⟩ :=
      (TauCeti.FinitePolyhedralComplex.isWeakRefinement_iff.mp hsub.1) (σ : Set V)
      ((Φ.mem_cells_toFinitePolyhedralComplex _).mpr ⟨σ, hσ, rfl⟩)
    obtain ⟨τ, hτ, rfl⟩ := (Ψ.mem_cells_toFinitePolyhedralComplex Q).mp hQ
    exact ⟨τ, hτ, hσQ⟩
  · intro hsub
    apply TauCeti.FinitePolyhedralComplex.isSubdivision_iff.mpr
    refine ⟨?_, by simpa using hsub.support_eq⟩
    apply TauCeti.FinitePolyhedralComplex.isWeakRefinement_iff.mpr
    intro P hP
    obtain ⟨σ, hσ, rfl⟩ := (Φ.mem_cells_toFinitePolyhedralComplex P).mp hP
    obtain ⟨τ, hτ, hστ⟩ := hsub.exists_cone_le hσ
    exact ⟨τ, (Ψ.mem_cells_toFinitePolyhedralComplex _).mpr ⟨τ, hτ, rfl⟩, hστ⟩

end TauCeti.Toric.Fan

namespace TauCeti.FinitePolyhedralComplex

variable {h : IsIntegralLattice i} {C D : FinitePolyhedralComplex h}

/-- Subdivision of the fans of two conical complexes agrees with subdivision of the complexes. -/
@[simp]
theorem isSubdivision_toFan_iff (hc : C.IsConical) (hd : D.IsConical) (hsalC) (hsalD) :
    (C.toFan hsalC).IsSubdivision (D.toFan hsalD) ↔ C.IsSubdivision D := by
  rw [← Fan.isSubdivision_toFinitePolyhedralComplex_iff, toFinitePolyhedralComplex_toFan C hc,
    toFinitePolyhedralComplex_toFan D hd]

/-- The fan extracted from a conical complex determines the complex. -/
@[simp]
theorem toFan_inj (hc : C.IsConical) (hd : D.IsConical) (hsalC) (hsalD) :
    C.toFan hsalC = D.toFan hsalD ↔ C = D := by
  rw [← Fan.toFinitePolyhedralComplex_inj, toFinitePolyhedralComplex_toFan C hc,
    toFinitePolyhedralComplex_toFan D hd]

end TauCeti.FinitePolyhedralComplex

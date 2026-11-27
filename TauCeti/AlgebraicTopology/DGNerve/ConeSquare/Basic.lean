/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGNerve.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.ProdStdSimplex.Square
public import TauCeti.CategoryTheory.DG.CochainComplex.HomotopyCategory
public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCocone.Basic

/-!
# Mapping cone and mapping cocone squares in the dg nerve

For a cochain map `f : X ⟶ Y`, the native dg nerve contains the candidate cofiber square
with corners `X, Y, 0, mappingCone f` and the candidate fiber square with corners
`mappingCocone f, X, 0, Y`. Their diagonals are zero. The triangle through `Y` in the
first square carries `mappingCone.inl f`; the triangle through `X` in the second carries
`-mappingCocone.snd f`. The triangles through zero carry zero homotopies.

These are coherent diagrams, with both triangles specified. No universal property of
either square is asserted here. The construction uses Mathlib's mapping cone differential
and its shifted mapping cocone, due to Joël Riou, and the dg-nerve 2-simplex equation
`d η = g ∘ f - h` of Lurie's *Higher Algebra*, Construction 1.3.1.6 and §1.3.2.
-/

public section

noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Simplicial
open CochainComplex HomComplex SSet HomologicalComplex
open scoped ZeroObject

namespace TauCeti.dgNerve

variable (R : Type v) [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear R C] [HasZeroObject C]
  {X Y : CochainComplex C ℤ} (f : X ⟶ Y) [HasHomotopyCofiber f]

/-- The triangle `X → Y → Cone(f)` with zero long edge and the canonical cone homotopy. -/
def mappingConeTriangle : (dgNerve R (CochainComplex C ℤ)) _⦋2⦌ :=
  DGNerve.Simplex.mk₂ (cochainHomLinearEquivDGCycles R _ _ f)
    (cochainHomLinearEquivDGCycles R _ _ (mappingCone.inr f)) 0 (mappingCone.inl f) (by
      rw [dgCompZero_cochainHomLinearEquivDGCycles, dgDifferential_linearHomComplex]
      simp only [Submodule.coe_zero, sub_zero]
      exact (mappingCone.δ_inl f).trans
        (cochainHomLinearEquivDGCycles_apply_coe R (f ≫ mappingCone.inr f)).symm)

/-- The triangle `X → 0 → Cone(f)` with zero long edge and zero homotopy. -/
def mappingConeZeroTriangle : (dgNerve R (CochainComplex C ℤ)) _⦋2⦌ :=
  DGNerve.Simplex.mk₂ (0 : dgCycles R X (0 : CochainComplex C ℤ))
    (0 : dgCycles R (0 : CochainComplex C ℤ) (mappingCone f)) 0 0 (by simp [dgCompZero_def])

/-- The upper triangle of the candidate cone square is the route through zero. -/
@[simp]
lemma mappingConeZeroTriangle_δ_one :
    (dgNerve R (CochainComplex C ℤ)).δ 1 (mappingConeZeroTriangle R f) =
      DGNerve.Simplex.edge (0 : dgCycles R X (mappingCone f)) := by
  rw [dgNerve_δ, mappingConeZeroTriangle, DGNerve.Simplex.mk₂_map_δ_one]

omit [HasZeroObject C] in
/-- The cone triangle has zero long edge. -/
@[simp]
lemma mappingConeTriangle_δ_one :
    (dgNerve R (CochainComplex C ℤ)).δ 1 (mappingConeTriangle R f) =
      DGNerve.Simplex.edge (0 : dgCycles R X (mappingCone f)) := by
  rw [dgNerve_δ, mappingConeTriangle, DGNerve.Simplex.mk₂_map_δ_one]

/-- The candidate cofiber square, with `X` at `(0,0)`, `Y` at `(1,0)`, zero at `(0,1)`
and the mapping cone at `(1,1)`. -/
def mappingConeSquare : Δ[1] ⊗ Δ[1] ⟶ dgNerve R (CochainComplex C ℤ) :=
  prodStdSimplex₁.squareDesc (SSet.yonedaEquiv.symm (mappingConeZeroTriangle R f))
    (SSet.yonedaEquiv.symm (mappingConeTriangle R f)) (by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm]
      simp)

/-- Restriction of the cone square to its triangle through zero. -/
@[reassoc (attr := simp)]
lemma ι_zero_mappingConeSquare :
    prodStdSimplex₁.ι 0 ≫ mappingConeSquare R f =
      SSet.yonedaEquiv.symm (mappingConeZeroTriangle R f) := by
  simp [mappingConeSquare]

/-- Restriction of the cone square to its triangle through `Y`. -/
@[reassoc (attr := simp)]
lemma ι_one_mappingConeSquare :
    prodStdSimplex₁.ι 1 ≫ mappingConeSquare R f =
      SSet.yonedaEquiv.symm (mappingConeTriangle R f) := by
  simp [mappingConeSquare]

/-- The triangle `Cocone(f) → X → Y` with zero long edge and homotopy `-snd`. -/
def mappingCoconeTriangle : (dgNerve R (CochainComplex C ℤ)) _⦋2⦌ :=
  DGNerve.Simplex.mk₂ (cochainHomLinearEquivDGCycles R _ _ (mappingCocone.fst f))
    (cochainHomLinearEquivDGCycles R _ _ f) 0 (-mappingCocone.snd f) (by
      rw [dgCompZero_cochainHomLinearEquivDGCycles, dgDifferential_linearHomComplex]
      simp only [Submodule.coe_zero, sub_zero]
      exact (mappingCocone.δ_neg_snd f).trans
        (cochainHomLinearEquivDGCycles_apply_coe R (mappingCocone.fst f ≫ f)).symm)

/-- The triangle `Cocone(f) → 0 → Y` with zero long edge and zero homotopy. -/
def mappingCoconeZeroTriangle : (dgNerve R (CochainComplex C ℤ)) _⦋2⦌ :=
  DGNerve.Simplex.mk₂ (0 : dgCycles R (mappingCocone f) (0 : CochainComplex C ℤ))
    (0 : dgCycles R (0 : CochainComplex C ℤ) Y) 0 0 (by simp [dgCompZero_def])

/-- The triangle through zero has zero long edge. -/
@[simp]
lemma mappingCoconeZeroTriangle_δ_one :
    (dgNerve R (CochainComplex C ℤ)).δ 1 (mappingCoconeZeroTriangle R f) =
      DGNerve.Simplex.edge (0 : dgCycles R (mappingCocone f) Y) := by
  rw [dgNerve_δ, mappingCoconeZeroTriangle, DGNerve.Simplex.mk₂_map_δ_one]

omit [HasZeroObject C] in
/-- The cocone triangle has zero long edge. -/
@[simp]
lemma mappingCoconeTriangle_δ_one :
    (dgNerve R (CochainComplex C ℤ)).δ 1 (mappingCoconeTriangle R f) =
      DGNerve.Simplex.edge (0 : dgCycles R (mappingCocone f) Y) := by
  rw [dgNerve_δ, mappingCoconeTriangle, DGNerve.Simplex.mk₂_map_δ_one]

/-- The candidate fiber square, with `Cocone(f)` at `(0,0)`, `X` at `(1,0)`, zero at `(0,1)`
and `Y` at `(1,1)`. -/
def mappingCoconeSquare : Δ[1] ⊗ Δ[1] ⟶ dgNerve R (CochainComplex C ℤ) :=
  prodStdSimplex₁.squareDesc (SSet.yonedaEquiv.symm (mappingCoconeZeroTriangle R f))
    (SSet.yonedaEquiv.symm (mappingCoconeTriangle R f)) (by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm]
      simp)

/-- Restriction of the cocone square to its triangle through zero. -/
@[reassoc (attr := simp)]
lemma ι_zero_mappingCoconeSquare :
    prodStdSimplex₁.ι 0 ≫ mappingCoconeSquare R f =
      SSet.yonedaEquiv.symm (mappingCoconeZeroTriangle R f) := by
  simp [mappingCoconeSquare]

/-- Restriction of the cocone square to its triangle through `X`. -/
@[reassoc (attr := simp)]
lemma ι_one_mappingCoconeSquare :
    prodStdSimplex₁.ι 1 ≫ mappingCoconeSquare R f =
      SSet.yonedaEquiv.symm (mappingCoconeTriangle R f) := by
  simp [mappingCoconeSquare]

omit [HasZeroObject C] in
/-- The ordered vertices of `mappingConeTriangle`. -/
@[simp]
lemma mappingConeTriangle_obj :
    DGNerve.Simplex.obj (mappingConeTriangle R f) = ![X, Y, mappingCone f] := by
  simp [mappingConeTriangle]

omit [HasZeroObject C] in
/-- The homotopy carried by `mappingConeTriangle`. -/
@[simp]
lemma mappingConeTriangle_coh :
    (mappingConeTriangle R f).coh 0 2 {1} (-1) (by decide) (by decide) (by simp) ≍
      mappingCone.inl f := by
  rw [mappingConeTriangle]
  exact DGNerve.Simplex.mk₂_coh_zero_two_singleton_heq _ _ _ _ _

omit [HasZeroObject C] in
/-- The first edge of `mappingConeTriangle`. -/
@[simp]
lemma mappingConeTriangle_δ_two :
    (dgNerve R (CochainComplex C ℤ)).δ 2 (mappingConeTriangle R f) =
      DGNerve.Simplex.edge (cochainHomLinearEquivDGCycles R _ _ f) := by
  rw [dgNerve_δ, mappingConeTriangle, DGNerve.Simplex.mk₂_map_δ_two]

omit [HasZeroObject C] in
/-- The second edge of `mappingConeTriangle`. -/
@[simp]
lemma mappingConeTriangle_δ_zero :
    (dgNerve R (CochainComplex C ℤ)).δ 0 (mappingConeTriangle R f) =
      DGNerve.Simplex.edge (cochainHomLinearEquivDGCycles R _ _ (mappingCone.inr f)) := by
  rw [dgNerve_δ, mappingConeTriangle, DGNerve.Simplex.mk₂_map_δ_zero]

/-- The ordered vertices of `mappingConeZeroTriangle`. -/
@[simp]
lemma mappingConeZeroTriangle_obj :
    DGNerve.Simplex.obj (mappingConeZeroTriangle R f) =
      ![X, (0 : CochainComplex C ℤ), mappingCone f] := by
  simp [mappingConeZeroTriangle]

/-- The homotopy carried by `mappingConeZeroTriangle`. -/
@[simp]
lemma mappingConeZeroTriangle_coh :
    (mappingConeZeroTriangle R f).coh 0 2 {1} (-1) (by decide) (by decide) (by simp) ≍
      (0 : Cochain X (mappingCone f) (-1)) := by
  rw [mappingConeZeroTriangle]
  exact DGNerve.Simplex.mk₂_coh_zero_two_singleton_heq _ _ _ _ _

/-- The first edge of `mappingConeZeroTriangle`. -/
@[simp]
lemma mappingConeZeroTriangle_δ_two :
    (dgNerve R (CochainComplex C ℤ)).δ 2 (mappingConeZeroTriangle R f) =
      DGNerve.Simplex.edge ((0 : dgCycles R X (0 : CochainComplex C ℤ))) := by
  rw [dgNerve_δ, mappingConeZeroTriangle, DGNerve.Simplex.mk₂_map_δ_two]

/-- The second edge of `mappingConeZeroTriangle`. -/
@[simp]
lemma mappingConeZeroTriangle_δ_zero :
    (dgNerve R (CochainComplex C ℤ)).δ 0 (mappingConeZeroTriangle R f) =
      DGNerve.Simplex.edge ((0 : dgCycles R (0 : CochainComplex C ℤ) (mappingCone f))) := by
  rw [dgNerve_δ, mappingConeZeroTriangle, DGNerve.Simplex.mk₂_map_δ_zero]

omit [HasZeroObject C] in
/-- The ordered vertices of `mappingCoconeTriangle`. -/
@[simp]
lemma mappingCoconeTriangle_obj :
    DGNerve.Simplex.obj (mappingCoconeTriangle R f) = ![mappingCocone f, X, Y] := by
  simp [mappingCoconeTriangle]

omit [HasZeroObject C] in
/-- The homotopy carried by `mappingCoconeTriangle`. -/
@[simp]
lemma mappingCoconeTriangle_coh :
    (mappingCoconeTriangle R f).coh 0 2 {1} (-1) (by decide) (by decide) (by simp) ≍
      -mappingCocone.snd f := by
  rw [mappingCoconeTriangle]
  exact DGNerve.Simplex.mk₂_coh_zero_two_singleton_heq _ _ _ _ _

omit [HasZeroObject C] in
/-- The first edge of `mappingCoconeTriangle`. -/
@[simp]
lemma mappingCoconeTriangle_δ_two :
    (dgNerve R (CochainComplex C ℤ)).δ 2 (mappingCoconeTriangle R f) =
      DGNerve.Simplex.edge (cochainHomLinearEquivDGCycles R _ _ (mappingCocone.fst f)) := by
  rw [dgNerve_δ, mappingCoconeTriangle, DGNerve.Simplex.mk₂_map_δ_two]

omit [HasZeroObject C] in
/-- The second edge of `mappingCoconeTriangle`. -/
@[simp]
lemma mappingCoconeTriangle_δ_zero :
    (dgNerve R (CochainComplex C ℤ)).δ 0 (mappingCoconeTriangle R f) =
      DGNerve.Simplex.edge (cochainHomLinearEquivDGCycles R _ _ f) := by
  rw [dgNerve_δ, mappingCoconeTriangle, DGNerve.Simplex.mk₂_map_δ_zero]

/-- The ordered vertices of `mappingCoconeZeroTriangle`. -/
@[simp]
lemma mappingCoconeZeroTriangle_obj :
    DGNerve.Simplex.obj (mappingCoconeZeroTriangle R f) =
      ![mappingCocone f, (0 : CochainComplex C ℤ), Y] := by
  simp [mappingCoconeZeroTriangle]

/-- The homotopy carried by `mappingCoconeZeroTriangle`. -/
@[simp]
lemma mappingCoconeZeroTriangle_coh :
    (mappingCoconeZeroTriangle R f).coh 0 2 {1} (-1) (by decide) (by decide) (by simp) ≍
      (0 : Cochain (mappingCocone f) Y (-1)) := by
  rw [mappingCoconeZeroTriangle]
  exact DGNerve.Simplex.mk₂_coh_zero_two_singleton_heq _ _ _ _ _

/-- The first edge of `mappingCoconeZeroTriangle`. -/
@[simp]
lemma mappingCoconeZeroTriangle_δ_two :
    (dgNerve R (CochainComplex C ℤ)).δ 2 (mappingCoconeZeroTriangle R f) =
      DGNerve.Simplex.edge ((0 : dgCycles R (mappingCocone f) (0 : CochainComplex C ℤ))) := by
  rw [dgNerve_δ, mappingCoconeZeroTriangle, DGNerve.Simplex.mk₂_map_δ_two]

/-- The second edge of `mappingCoconeZeroTriangle`. -/
@[simp]
lemma mappingCoconeZeroTriangle_δ_zero :
    (dgNerve R (CochainComplex C ℤ)).δ 0 (mappingCoconeZeroTriangle R f) =
      DGNerve.Simplex.edge ((0 : dgCycles R (0 : CochainComplex C ℤ) Y)) := by
  rw [dgNerve_δ, mappingCoconeZeroTriangle, DGNerve.Simplex.mk₂_map_δ_zero]

/-- The bottom edge of the candidate mappingCone square. -/
@[reassoc (attr := simp)]
lemma mappingConeSquare_bottom :
    lift (𝟙 Δ[1]) (stdSimplex.σ 0 ≫ stdSimplex.δ 1) ≫ mappingConeSquare R f =
      SSet.yonedaEquiv.symm (DGNerve.Simplex.edge (cochainHomLinearEquivDGCycles R _ _ f)) := by
  rw [← lift_whiskerLeft_assoc, ← prodStdSimplex₁.δ_two_ι_one_assoc, ι_one_mappingConeSquare,
    stdSimplex.δ_comp_yonedaEquiv_symm, mappingConeTriangle_δ_two]

/-- The right edge of the candidate mappingCone square. -/
@[reassoc (attr := simp)]
lemma mappingConeSquare_right :
    lift (stdSimplex.σ 0 ≫ stdSimplex.δ 0) (𝟙 Δ[1]) ≫ mappingConeSquare R f =
      SSet.yonedaEquiv.symm (DGNerve.Simplex.edge
        (cochainHomLinearEquivDGCycles R _ _ (mappingCone.inr f))) := by
  rw [← lift_whiskerRight_assoc, ← prodStdSimplex₁.δ_zero_ι_one_assoc, ι_one_mappingConeSquare,
    stdSimplex.δ_comp_yonedaEquiv_symm, mappingConeTriangle_δ_zero]

/-- The left edge of the candidate mappingCone square. -/
@[reassoc (attr := simp)]
lemma mappingConeSquare_left :
    lift (stdSimplex.σ 0 ≫ stdSimplex.δ 1) (𝟙 Δ[1]) ≫ mappingConeSquare R f =
      SSet.yonedaEquiv.symm (DGNerve.Simplex.edge
        ((0 : dgCycles R X (0 : CochainComplex C ℤ)))) := by
  rw [← lift_whiskerRight_assoc, ← prodStdSimplex₁.δ_two_ι_zero_assoc, ι_zero_mappingConeSquare,
    stdSimplex.δ_comp_yonedaEquiv_symm, mappingConeZeroTriangle_δ_two]

/-- The top edge of the candidate mappingCone square. -/
@[reassoc (attr := simp)]
lemma mappingConeSquare_top :
    lift (𝟙 Δ[1]) (stdSimplex.σ 0 ≫ stdSimplex.δ 0) ≫ mappingConeSquare R f =
      SSet.yonedaEquiv.symm (DGNerve.Simplex.edge
        ((0 : dgCycles R (0 : CochainComplex C ℤ) (mappingCone f)))) := by
  rw [← lift_whiskerLeft_assoc, ← prodStdSimplex₁.δ_zero_ι_zero_assoc, ι_zero_mappingConeSquare,
    stdSimplex.δ_comp_yonedaEquiv_symm, mappingConeZeroTriangle_δ_zero]

/-- The diagonal of the candidate mappingCone square is zero. -/
@[reassoc (attr := simp)]
lemma mappingConeSquare_diagonal :
    lift (𝟙 Δ[1]) (𝟙 Δ[1]) ≫ mappingConeSquare R f =
      SSet.yonedaEquiv.symm (DGNerve.Simplex.edge (0 : dgCycles R X (mappingCone f))) := by
  rw [← prodStdSimplex₁.δ_one_ι_zero_eq_lift, Category.assoc,
    ι_zero_mappingConeSquare, stdSimplex.δ_comp_yonedaEquiv_symm,
    mappingConeZeroTriangle_δ_one]

/-- The bottom edge of the candidate mappingCocone square. -/
@[reassoc (attr := simp)]
lemma mappingCoconeSquare_bottom :
    lift (𝟙 Δ[1]) (stdSimplex.σ 0 ≫ stdSimplex.δ 1) ≫ mappingCoconeSquare R f =
      SSet.yonedaEquiv.symm (DGNerve.Simplex.edge
        (cochainHomLinearEquivDGCycles R _ _ (mappingCocone.fst f))) := by
  rw [← lift_whiskerLeft_assoc, ← prodStdSimplex₁.δ_two_ι_one_assoc, ι_one_mappingCoconeSquare,
    stdSimplex.δ_comp_yonedaEquiv_symm, mappingCoconeTriangle_δ_two]

/-- The right edge of the candidate mappingCocone square. -/
@[reassoc (attr := simp)]
lemma mappingCoconeSquare_right :
    lift (stdSimplex.σ 0 ≫ stdSimplex.δ 0) (𝟙 Δ[1]) ≫ mappingCoconeSquare R f =
      SSet.yonedaEquiv.symm (DGNerve.Simplex.edge (cochainHomLinearEquivDGCycles R _ _ f)) := by
  rw [← lift_whiskerRight_assoc, ← prodStdSimplex₁.δ_zero_ι_one_assoc, ι_one_mappingCoconeSquare,
    stdSimplex.δ_comp_yonedaEquiv_symm, mappingCoconeTriangle_δ_zero]

/-- The left edge of the candidate mappingCocone square. -/
@[reassoc (attr := simp)]
lemma mappingCoconeSquare_left :
    lift (stdSimplex.σ 0 ≫ stdSimplex.δ 1) (𝟙 Δ[1]) ≫ mappingCoconeSquare R f =
      SSet.yonedaEquiv.symm (DGNerve.Simplex.edge
        ((0 : dgCycles R (mappingCocone f) (0 : CochainComplex C ℤ)))) := by
  rw [← lift_whiskerRight_assoc, ← prodStdSimplex₁.δ_two_ι_zero_assoc, ι_zero_mappingCoconeSquare,
    stdSimplex.δ_comp_yonedaEquiv_symm, mappingCoconeZeroTriangle_δ_two]

/-- The top edge of the candidate mappingCocone square. -/
@[reassoc (attr := simp)]
lemma mappingCoconeSquare_top :
    lift (𝟙 Δ[1]) (stdSimplex.σ 0 ≫ stdSimplex.δ 0) ≫ mappingCoconeSquare R f =
      SSet.yonedaEquiv.symm (DGNerve.Simplex.edge
        ((0 : dgCycles R (0 : CochainComplex C ℤ) Y))) := by
  rw [← lift_whiskerLeft_assoc, ← prodStdSimplex₁.δ_zero_ι_zero_assoc, ι_zero_mappingCoconeSquare,
    stdSimplex.δ_comp_yonedaEquiv_symm, mappingCoconeZeroTriangle_δ_zero]

/-- The diagonal of the candidate mappingCocone square is zero. -/
@[reassoc (attr := simp)]
lemma mappingCoconeSquare_diagonal :
    lift (𝟙 Δ[1]) (𝟙 Δ[1]) ≫ mappingCoconeSquare R f =
      SSet.yonedaEquiv.symm (DGNerve.Simplex.edge (0 : dgCycles R (mappingCocone f) Y)) := by
  rw [← prodStdSimplex₁.δ_one_ι_zero_eq_lift, Category.assoc,
    ι_zero_mappingCoconeSquare, stdSimplex.δ_comp_yonedaEquiv_symm,
    mappingCoconeZeroTriangle_δ_one]

end TauCeti.dgNerve

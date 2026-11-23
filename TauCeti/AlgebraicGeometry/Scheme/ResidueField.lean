/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-!
# Generators of residue fields on affine schemes

The values of the coordinate ring generate the residue field at each point of an
affine scheme. Consequently, algebra generators on an affine scheme give field
generators on residue fields, also after restricting the source to a subscheme.

## Main results

* `Spec.closure_range_Γevaluation_eq_top`: affine coordinate values generate the
  residue field.
* `Hom.Γevaluation_naturality_of_Spec`: affine coordinate values commute with the
  induced maps on residue fields.
* `Hom.adjoin_residueField_eq_top_of_isIso_residueFieldMap`: algebra generators give
  residue-field generators when the source morphism induces a residue-field isomorphism.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- The values of the coordinates of `Spec R` at `x` generate its residue field. -/
theorem Spec.closure_range_Γevaluation_eq_top (R : CommRingCat.{u}) (x : Spec R) :
    Subfield.closure (Set.range ((ΓSpecIso R).inv ≫ (Spec R).Γevaluation x)) = ⊤ := by
  have : x.asIdeal.IsPrime := x.isPrime
  let e := (residueFieldIso R x).inv
  have he : Function.Surjective e := (ConcreteCategory.bijective_of_isIso e).surjective
  have h : Set.range (CommRingCat.ofHom (algebraMap R x.asIdeal.ResidueField)) =
      Set.range (algebraMap (R ⧸ x.asIdeal) x.asIdeal.ResidueField) := by
    -- Express the underlying function of the categorical morphism as an algebra map.
    change Set.range (algebraMap R x.asIdeal.ResidueField) = _
    rw [IsScalarTower.algebraMap_eq R (R ⧸ x.asIdeal) x.asIdeal.ResidueField, RingHom.coe_comp,
      Ideal.Quotient.algebraMap_eq, Set.range_comp, Ideal.Quotient.mk_surjective.range_eq,
      Set.image_univ]
  -- The affine residue field is the fraction field of the prime quotient.
  have heval : CommRingCat.ofHom (algebraMap R x.asIdeal.ResidueField) ≫ e =
      (ΓSpecIso R).inv ≫ (Spec R).Γevaluation x :=
    algebraMap_residueFieldIso_inv R x
  rw [← heval, ConcreteCategory.coe_comp, Set.range_comp, h, ← RingHom.map_field_closure e.hom,
    IsFractionRing.closure_range_algebraMap, Subfield.map_top]
  exact SetLike.ext' he.range_eq

namespace Hom

/-- Affine coordinate values commute with the induced maps on residue fields. -/
theorem Γevaluation_naturality_of_Spec {R S : CommRingCat.{u}} {Y : Scheme.{u}}
    (g : Y ⟶ Spec S) (φ : R ⟶ S) {h : Y ⟶ Spec R}
    (hg : g ≫ Spec.map φ = h) (y : Y) :
    φ ≫ (ΓSpecIso S).inv ≫ (Spec S).Γevaluation (g y) ≫ g.residueFieldMap y =
      (ΓSpecIso R).inv ≫ (Spec R).Γevaluation (h y) ≫
        h.residueFieldMap y := by
  simp only [ΓSpecIso_inv_naturality_assoc,
    ← Scheme.Hom.comp_appTop_assoc, hg, Scheme.Γevaluation_naturality]

/-- The values of algebra generators of `B` over `A` generate the residue field at `y` over
that at its image in `Spec A`, provided `g : Y ⟶ Spec B` identifies the residue fields at
`y` and `g y`. This applies, for example, if `g` is an open immersion. -/
theorem adjoin_residueField_eq_top_of_isIso_residueFieldMap {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of B)) {h : Y ⟶ Spec (.of A)}
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = h)
    (y : Y) [IsIso (g.residueFieldMap y)] {s : Set B} (hs : Algebra.adjoin A s = ⊤) :
    letI := (h.residueFieldMap y).hom.toAlgebra
    IntermediateField.adjoin ((Spec (.of A)).residueField (h y))
      (((ΓSpecIso (.of B)).inv ≫ (Spec (.of B)).Γevaluation (g y) ≫ g.residueFieldMap y) '' s) =
      ⊤ := by
  let := (h.residueFieldMap y).hom.toAlgebra
  let baseValue := (ΓSpecIso (.of A)).inv ≫ (Spec (.of A)).Γevaluation (h y)
  let sourceValue :=
    (ΓSpecIso (.of B)).inv ≫ (Spec (.of B)).Γevaluation (g y) ≫ g.residueFieldMap y
  have hvalue : CommRingCat.ofHom (algebraMap A B) ≫ sourceValue =
      baseValue ≫ h.residueFieldMap y := by
    exact g.Γevaluation_naturality_of_Spec (CommRingCat.ofHom (algebraMap A B)) hg y
  let : Algebra A ((Spec (.of A)).residueField (h y)) := baseValue.hom.toAlgebra
  let : Algebra A (Y.residueField y) := (baseValue ≫ h.residueFieldMap y).hom.toAlgebra
  have : IsScalarTower A ((Spec (.of A)).residueField (h y)) (Y.residueField y) :=
    .of_algebraMap_eq fun _ ↦ rfl
  let sourceAlgHom : B →ₐ[A] Y.residueField y :=
    ⟨sourceValue.hom, ConcreteCategory.congr_hom hvalue⟩
  let F := IntermediateField.adjoin ((Spec (.of A)).residueField (h y)) (sourceValue '' s)
  have hle : Algebra.adjoin A s ≤ (F.toSubalgebra.restrictScalars A).comap sourceAlgHom :=
    Algebra.adjoin_le fun z hz ↦ IntermediateField.subset_adjoin _ _ ⟨z, hz, rfl⟩
  have hrange : Set.range sourceValue ⊆ F := by
    rintro _ ⟨z, rfl⟩
    exact hle (hs.ge Algebra.mem_top)
  have hclosure : Subfield.closure (Set.range sourceValue) = ⊤ := by
    have hsurj := (ConcreteCategory.bijective_of_isIso (g.residueFieldMap y)).surjective
    dsimp only [sourceValue]
    rw [← Category.assoc, ConcreteCategory.coe_comp, Set.range_comp,
      ← RingHom.map_field_closure (g.residueFieldMap y).hom,
      Spec.closure_range_Γevaluation_eq_top, Subfield.map_top]
    exact SetLike.ext' hsurj.range_eq
  have hle : (⊤ : Subfield (Y.residueField y)) ≤ F.toSubfield := by
    rw [← hclosure]
    exact Subfield.closure_le.mpr hrange
  exact eq_top_iff.mpr fun _ _ ↦ hle (by trivial)

end Hom

end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.Spherical
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Symmetric
public import TauCeti.CategoryTheory.Monoidal.Rigid.Functor

/-!
# Pivotal functors

A strong monoidal functor `F : C ⥤ D` between rigid categories carries a canonical isomorphism
`δ_X = F.mapRightDualIso X : F.obj Xᘁ ≅ (F.obj X)ᘁ`. When `C` and `D` are pivotal, with pivotal
isomorphisms `φ`, the functor `F` is *pivotal* if it carries the pivotal structure of `C` to that
of `D`:
`F.map φ_X = φ_{F X} ≫ (δ_X)ᘁ ≫ δ_{Xᘁ}⁻¹`,
an identity of morphisms `F.obj X ⟶ F.obj Xᘁᘁ` along the path
`F.obj X ⟶ (F.obj X)ᘁᘁ ⟶ (F.obj Xᘁ)ᘁ ⟶ F.obj Xᘁᘁ`.

The identity functor is pivotal, and a composite of pivotal functors is pivotal. A pivotal functor
preserves the left and right traces, and hence the left and right dimensions, up to the unit
comparison `ε F : 𝟙_ D ⟶ F.obj (𝟙_ C)`: for instance
`rightTrace (F.map f) = ε F ≫ F.map (rightTrace f) ≫ η F`. Between spherical categories it
therefore preserves the trace and the quantum dimension.

A braided functor carries the Drinfeld isomorphism of `X` to that of `F.obj X`, up to the
comparisons `δ`. Consequently every braided functor between symmetric rigid categories is pivotal
for their canonical pivotal structures.

## Main declarations

* `CategoryTheory.Functor.IsPivotal`: a strong monoidal functor between pivotal categories that
  preserves the pivotal structure;
* `CategoryTheory.Functor.isPivotal_id` and `CategoryTheory.Functor.isPivotal_comp`: identities
  and composites of pivotal functors are pivotal;
* `CategoryTheory.Functor.rightTrace_map` and `CategoryTheory.Functor.leftTrace_map`: a pivotal
  functor preserves the two traces, with the corollaries `CategoryTheory.Functor.rightDim_map`,
  `CategoryTheory.Functor.leftDim_map`, `CategoryTheory.Functor.trace_map` and
  `CategoryTheory.Functor.quantumDim_map`;
* `CategoryTheory.Functor.map_drinfeldIso_hom_comp_mapRightDualIso_hom`: a braided functor
  preserves Drinfeld isomorphisms;
* `CategoryTheory.Functor.isPivotal_of_braided`: a braided functor between symmetric rigid
  categories is pivotal.

## References

* A. Henriques, D. Penneys, J. Tener, *Categorified trace for module tensor categories over
  braided tensor categories*, [arXiv:1509.02937](https://arxiv.org/abs/1509.02937), §2.1
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.7
-/

public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
open TauCeti

namespace CategoryTheory.Functor

variable {C : Type*} [Category* C] [MonoidalCategory C]
variable {D : Type*} [Category* D] [MonoidalCategory D]

section Pivotal

variable [RigidCategory C] [PivotalCategory C] [RigidCategory D] [PivotalCategory D]
variable (F : C ⥤ D) [F.Monoidal]

/-- A strong monoidal functor `F` between pivotal categories is *pivotal* if it carries the
pivotal isomorphism `φ_X` of `C` to the pivotal isomorphism `φ_{F X}` of `D`, transported along
the comparisons `δ_X : F.obj Xᘁ ≅ (F.obj X)ᘁ` and `δ_{Xᘁ}`. -/
class IsPivotal : Prop where
  /-- The image of `φ_X` is `φ_{F X} ≫ (δ_X)ᘁ ≫ δ_{Xᘁ}⁻¹`. -/
  map_pivotalIsoApp_hom (X : C) : F.map (pivotalIsoApp X).hom =
    (pivotalIsoApp (F.obj X)).hom ≫ ((F.mapRightDualIso X).hom)ᘁ ≫ (F.mapRightDualIso Xᘁ).inv

/-- The defining identity of a pivotal functor, with the comparison `δ_{Xᘁ}` moved to the left:
`F.map φ_X ≫ δ_{Xᘁ} = φ_{F X} ≫ (δ_X)ᘁ`. -/
@[reassoc]
theorem map_pivotalIsoApp_hom_comp_mapRightDualIso_hom [F.IsPivotal] (X : C) :
    F.map (pivotalIsoApp X).hom ≫ (F.mapRightDualIso Xᘁ).hom =
      (pivotalIsoApp (F.obj X)).hom ≫ ((F.mapRightDualIso X).hom)ᘁ := by
  rw [IsPivotal.map_pivotalIsoApp_hom, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

variable {F} in
/-- A monoidal functor is pivotal as soon as `F.map φ_X ≫ δ_{Xᘁ} = φ_{F X} ≫ (δ_X)ᘁ` for every
`X`. -/
theorem IsPivotal.mk' (h : ∀ X : C, F.map (pivotalIsoApp X).hom ≫ (F.mapRightDualIso Xᘁ).hom =
    (pivotalIsoApp (F.obj X)).hom ≫ ((F.mapRightDualIso X).hom)ᘁ) : F.IsPivotal where
  map_pivotalIsoApp_hom X := by rw [← Category.assoc, Iso.eq_comp_inv, h]

/-- The identity functor is pivotal. -/
instance isPivotal_id : (𝟭 C).IsPivotal where
  map_pivotalIsoApp_hom X := by simp

/-- A composite of pivotal functors is pivotal. -/
instance isPivotal_comp {E : Type*} [Category* E] [MonoidalCategory E] [RigidCategory E]
    [PivotalCategory E] (G : D ⥤ E) [G.Monoidal] [F.IsPivotal] [G.IsPivotal] :
    (F ⋙ G).IsPivotal where
  map_pivotalIsoApp_hom X := by
    -- Expand the comparisons of `F ⋙ G` and the images of `φ` under `F` and then `G`.
    simp only [mapRightDualIso_comp, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
      Functor.mapIso_inv, Functor.comp_map, IsPivotal.map_pivotalIsoApp_hom, Functor.map_comp,
      comp_rightAdjointMate, Category.assoc, Functor.comp_obj]
    -- The comparison `δ` of `G` slides past the image of that of `F`.
    rw [reassoc_of% (mapRightDualIso_inv_naturality (F := G) (F.mapRightDualIso X).hom)]

/-- **A pivotal functor preserves the right trace**: the right trace of `F.map f` is the image of
the right trace of `f`, read in `𝟙_ D ⟶ 𝟙_ D` through the unit comparison of `F`. -/
theorem rightTrace_map [F.IsPivotal] {X : C} (f : X ⟶ X) :
    rightTrace (F.map f) = ε F ≫ F.map (rightTrace f) ≫ η F := by
  rw [rightTrace_eq_pivotalIsoApp, rightTrace_eq_pivotalIsoApp]
  simp only [Functor.map_comp, map_whiskerRight, Category.assoc, μ_δ_assoc]
  -- Rewrite the image of the evaluation of `(Xᘁ, Xᘁᘁ)` and of the coevaluation of `(X, Xᘁ)`
  -- through the comparisons `δ`, and use that `F` is pivotal to replace `F.map φ_X ≫ δ_{Xᘁ}`.
  rw [← mapRightDualIso_hom_whiskerRight_evaluation,
    ← comp_whiskerRight_assoc (F.map (pivotalIsoApp X).hom),
    F.map_pivotalIsoApp_hom_comp_mapRightDualIso_hom, comp_whiskerRight_assoc,
    rightAdjointMate_comp_evaluation, ← coevaluation_whiskerLeft_mapRightDualIso_inv_assoc]
  -- The comparison `δ_X` now slides around the loop and cancels against its inverse.
  rw [← whisker_exchange_assoc, ← whisker_exchange_assoc, whiskerLeft_inv_hom_assoc]

/-- **A pivotal functor preserves the left trace**: the left trace of `F.map f` is the image of
the left trace of `f`, read in `𝟙_ D ⟶ 𝟙_ D` through the unit comparison of `F`. -/
theorem leftTrace_map [F.IsPivotal] {X : C} (f : X ⟶ X) :
    leftTrace (F.map f) = ε F ≫ F.map (leftTrace f) ≫ η F := by
  rw [← rightTrace_rightAdjointMate, ← rightTrace_rightAdjointMate, ← F.rightTrace_map,
    ← rightTrace_conj (F.mapRightDualIso X), mapRightDualIso_hom_naturality, Iso.inv_hom_id_assoc]

/-- A pivotal functor preserves the right dimension. -/
theorem rightDim_map [F.IsPivotal] (X : C) :
    rightDim (F.obj X) = ε F ≫ F.map (rightDim X) ≫ η F := by
  rw [← rightTrace_id, ← rightTrace_id, ← F.map_id, F.rightTrace_map]

/-- A pivotal functor preserves the left dimension. -/
theorem leftDim_map [F.IsPivotal] (X : C) :
    leftDim (F.obj X) = ε F ≫ F.map (leftDim X) ≫ η F := by
  rw [← leftTrace_id, ← leftTrace_id, ← F.map_id, F.leftTrace_map]

variable [SphericalCategory C] [SphericalCategory D]

/-- A pivotal functor between spherical categories preserves the trace. -/
theorem trace_map [F.IsPivotal] {X : C} (f : X ⟶ X) :
    trace (F.map f) = ε F ≫ F.map (trace f) ≫ η F := by
  rw [trace_eq_rightTrace, trace_eq_rightTrace, F.rightTrace_map]

/-- A pivotal functor between spherical categories preserves the quantum dimension. -/
theorem quantumDim_map [F.IsPivotal] (X : C) :
    quantumDim (F.obj X) = ε F ≫ F.map (quantumDim X) ≫ η F := by
  rw [quantumDim_eq_rightDim, quantumDim_eq_rightDim, F.rightDim_map]

end Pivotal

section Braided

variable [BraidedCategory C] [RightRigidCategory C] [BraidedCategory D] [RightRigidCategory D]
variable (F : C ⥤ D) [F.Braided]

/-- A braided functor carries the Drinfeld isomorphism of `X` to that of `F.obj X`, transported
along the comparisons `δ_X : F.obj Xᘁ ≅ (F.obj X)ᘁ` and `δ_{Xᘁ}`. -/
@[reassoc]
theorem map_drinfeldIso_hom_comp_mapRightDualIso_hom (X : C) :
    F.map (drinfeldIso X).hom ≫ (F.mapRightDualIso Xᘁ).hom =
      (drinfeldIso (F.obj X)).hom ≫ ((F.mapRightDualIso X).hom)ᘁ := by
  refine ExactPairing.rightHom_ext (X := F.obj Xᘁ) ?_
  -- Both sides evaluate to the braided evaluation of `(F.obj X, F.obj Xᘁ)`: on the left, this is
  -- the image of the corresponding identity in `C`.
  have h : F.map ((drinfeldIso X).hom ▷ Xᘁ) ≫ F.map (ε_ Xᘁ Xᘁᘁ) =
      F.map (β_ X Xᘁ).hom ≫ F.map (ε_ X Xᘁ) := by
    rw [← F.map_comp, drinfeldIso_hom_comp_evaluation, F.map_comp]
  simp only [comp_whiskerRight, Category.assoc, mapRightDualIso_hom_whiskerRight_evaluation,
    rightAdjointMate_comp_evaluation, ← whisker_exchange_assoc, μ_natural_left_assoc,
    reassoc_of% h, LaxBraided.braided_assoc, drinfeldIso_hom_comp_evaluation,
    BraidedCategory.braiding_naturality_right_assoc]

end Braided

section Symmetric

variable [SymmetricCategory C] [RigidCategory C] [SymmetricCategory D] [RigidCategory D]

/-- A braided functor between symmetric rigid categories is pivotal for their canonical pivotal
structures. -/
instance isPivotal_of_braided (F : C ⥤ D) [F.Braided] : F.IsPivotal :=
  IsPivotal.mk' fun X => by
    simpa only [pivotalIsoApp_eq_drinfeldIso] using F.map_drinfeldIso_hom_comp_mapRightDualIso_hom X

end Symmetric

end CategoryTheory.Functor

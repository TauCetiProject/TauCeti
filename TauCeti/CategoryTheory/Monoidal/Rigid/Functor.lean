/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Closed.Functor
public import TauCeti.CategoryTheory.Monoidal.Rigid.OfClosed

/-!
# Exact pairings under strong monoidal functors

A strong monoidal functor `F : C ⥤ D` carries an exact pairing `ExactPairing X Y` in `C` to an
exact pairing `ExactPairing (F.obj X) (F.obj Y)` in `D`: its evaluation and coevaluation are the
images of those of `(X, Y)`, conjugated by the unit and tensor comparisons of `F`
(`CategoryTheory.Functor.mapExactPairing`). In particular, a strong monoidal functor preserves
objects with a left or right dual (`CategoryTheory.Functor.mapHasLeftDual` and
`CategoryTheory.Functor.mapHasRightDual`).

Consequently, if `Y` has a left dual `X` and both `Y` and `F.obj Y` are closed, then the
internal Hom comparison `F.obj (Y ⟶[C] B) ⟶ (F.obj Y ⟶[D] F.obj B)` of `F` is an isomorphism
(`CategoryTheory.Functor.ihomComparison_isIso_of_exactPairing`): `TauCeti.ihomIsoTensorLeft`
identifies its source with `F.obj (X ⊗ B)` through the pairing in `C`, and its target with
`F.obj X ⊗ F.obj B` through the image pairing in `D`.

A strong monoidal functor also carries the dual-tensor comparison
`TauCeti.dualTensorIhom Y : (Y ⟶[C] 𝟙_ C) ⊗ Z ⟶ (Y ⟶[C] Z)` to the dual-tensor comparison of
`F.obj Y`, up to its internal Hom comparisons
(`CategoryTheory.Functor.map_dualTensorIhom_app_comp_ihomComparison`). So when those
comparisons are invertible, invertibility of the dual-tensor comparison of `F.obj Y` reflects
back to the image of that of `Y` (`CategoryTheory.Functor.isIso_map_dualTensorIhom_app`). For
restriction of sheaves of modules to the members of a cover, this is how the dual-tensor
comparison, and hence dualizability, is checked locally.

The dual transfers are the forward counterparts of Mathlib's
`CategoryTheory.hasLeftDualOfEquivalence` and `CategoryTheory.hasRightDualOfEquivalence` in
`Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence`, which pull duals back along a monoidal
equivalence.

## Main declarations

* `CategoryTheory.Functor.mapExactPairing`: the image of an exact pairing under a strong monoidal
  functor, with evaluation and coevaluation computed by
  `CategoryTheory.Functor.mapExactPairing_evaluation` and
  `CategoryTheory.Functor.mapExactPairing_coevaluation`;
* `CategoryTheory.Functor.mapHasLeftDual` and `CategoryTheory.Functor.mapHasRightDual`: the image
  of an object with a left or right dual has the image of that dual as a dual;
* `CategoryTheory.Functor.ihomComparison_isIso_of_exactPairing`: the internal Hom comparison of
  a strong monoidal functor is invertible at an object with a left dual;
* `CategoryTheory.Functor.whiskerLeft_ihomComparison_app_unit_comp_map_η_comp_ev`: the
  comparison of duals is compatible with evaluation;
* `CategoryTheory.Functor.map_dualTensorIhom_app_comp_ihomComparison` and
  `CategoryTheory.Functor.isIso_map_dualTensorIhom_app`: the dual-tensor comparison under a
  strong monoidal functor.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed Functor.LaxMonoidal Functor.OplaxMonoidal
  Functor.Monoidal

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable (F : C ⥤ D) [F.Monoidal]

/-- The image of an exact pairing under a strong monoidal functor `F`. The evaluation of
`(F.obj X, F.obj Y)` is the image of the evaluation of `(X, Y)`, preceded by the tensor
comparison and followed by the inverse unit comparison; dually for the coevaluation. -/
@[instance_reducible]
def mapExactPairing (X Y : C) [ExactPairing X Y] : ExactPairing (F.obj X) (F.obj Y) where
  coevaluation' := ε F ≫ F.map (η_ X Y) ≫ δ F X Y
  evaluation' := μ F Y X ≫ F.map (ε_ X Y) ≫ η F
  coevaluation_evaluation' := by
    -- Expand the image of the zigzag identity of `(X, Y)` through the comparisons of `F`.
    have h := congrArg F.map (ExactPairing.coevaluation_evaluation X Y)
    simp only [Functor.map_comp, map_whiskerLeft, map_associator_inv, map_whiskerRight,
      map_rightUnitor, map_leftUnitor_inv, Category.assoc, μ_δ_assoc, cancel_epi] at h
    rw [← cancel_mono (ε F ▷ F.obj Y ≫ μ F (𝟙_ C) Y)]
    simp only [MonoidalCategory.whiskerLeft_comp, MonoidalCategory.comp_whiskerRight,
      Category.assoc, whiskerRight_η_ε_assoc, h, whiskerLeft_ε_η_assoc]
  evaluation_coevaluation' := by
    -- Expand the image of the zigzag identity of `(X, Y)` through the comparisons of `F`.
    have h := congrArg F.map (ExactPairing.evaluation_coevaluation X Y)
    simp only [Functor.map_comp, map_whiskerLeft, map_associator, map_whiskerRight,
      map_leftUnitor, map_rightUnitor_inv, Category.assoc, μ_δ_assoc, cancel_epi] at h
    rw [← cancel_mono (F.obj X ◁ ε F ≫ μ F X (𝟙_ C))]
    simp only [MonoidalCategory.whiskerLeft_comp, MonoidalCategory.comp_whiskerRight,
      Category.assoc, whiskerLeft_η_ε_assoc, h, whiskerRight_ε_η_assoc]

variable {F}

/-- The evaluation of the image of an exact pairing under a strong monoidal functor. -/
@[simp]
theorem mapExactPairing_evaluation (X Y : C) [ExactPairing X Y] :
    @ExactPairing.evaluation D _ _ (F.obj X) (F.obj Y) (F.mapExactPairing X Y) =
      μ F Y X ≫ F.map (ε_ X Y) ≫ η F :=
  (rfl)

/-- The coevaluation of the image of an exact pairing under a strong monoidal functor. -/
@[simp]
theorem mapExactPairing_coevaluation (X Y : C) [ExactPairing X Y] :
    @ExactPairing.coevaluation D _ _ (F.obj X) (F.obj Y) (F.mapExactPairing X Y) =
      ε F ≫ F.map (η_ X Y) ≫ δ F X Y :=
  (rfl)

variable (F)

/-- A strong monoidal functor carries an object with a left dual to an object with a left dual,
the image of the dual. Not an instance: the dual it produces depends on `F`, and several functors
may have the same object as a value. -/
@[instance_reducible]
def mapHasLeftDual (Y : C) [HasLeftDual Y] : HasLeftDual (F.obj Y) where
  leftDual := F.obj (ᘁY)
  exact := F.mapExactPairing (ᘁY) Y

/-- A strong monoidal functor carries an object with a right dual to an object with a right
dual, the image of the dual. Not an instance, for the reason given on
`CategoryTheory.Functor.mapHasLeftDual`. -/
@[instance_reducible]
def mapHasRightDual (X : C) [HasRightDual X] : HasRightDual (F.obj X) where
  rightDual := F.obj (Xᘁ)
  exact := F.mapExactPairing X (Xᘁ)

variable {F}

/-- The left dual of `F.obj Y` produced by `CategoryTheory.Functor.mapHasLeftDual` is the image
of the left dual of `Y`. -/
@[simp]
theorem mapHasLeftDual_leftDual (Y : C) [HasLeftDual Y] :
    @HasLeftDual.leftDual D _ _ (F.obj Y) (F.mapHasLeftDual Y) = F.obj (ᘁY) :=
  (rfl)

/-- The right dual of `F.obj X` produced by `CategoryTheory.Functor.mapHasRightDual` is the image
of the right dual of `X`. -/
@[simp]
theorem mapHasRightDual_rightDual (X : C) [HasRightDual X] :
    @HasRightDual.rightDual D _ _ (F.obj X) (F.mapHasRightDual X) = F.obj (Xᘁ) :=
  (rfl)

variable (F)

/-- A strong monoidal functor inverts the internal Hom comparison at an object `Y` with a left
dual `X`: both `F.obj (Y ⟶[C] B)` and `F.obj Y ⟶[D] F.obj B` are identified with
`F.obj X ⊗ F.obj B`, through the pairing and its image. -/
theorem ihomComparison_isIso_of_exactPairing (X Y : C) [ExactPairing X Y] [Closed Y]
    [Closed (F.obj Y)] :
    IsIso (F.ihomComparison Y).natTrans := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro B
  let := F.mapExactPairing X Y
  refine ihomComparison_isIso_of_tensor_comparison F Y B
    ((TauCeti.ihomIsoTensorLeft (F.obj X) (F.obj Y)).app (F.obj B))
    (F.mapIso ((TauCeti.ihomIsoTensorLeft X Y).app B) ≪≫ (μIso F X B).symm) ?_
  -- Both evaluations are the evaluation of a pairing, in `C` and in `D`; expand the image of the
  -- former through the comparisons of `F`.
  rw [← TauCeti.whiskerLeft_ihomIsoTensorLeft_hom_app_comp_evaluation (D := X) (Y := Y) B]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, μIso_inv, Iso.app_inv,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    TauCeti.whiskerLeft_ihomIsoTensorLeft_inv_app_comp_ev, mapExactPairing_evaluation,
    MonoidalCategory.comp_whiskerRight, Functor.map_comp, map_whiskerLeft, map_associator_inv,
    map_whiskerRight, μ_δ_assoc, curriedTensor_obj_obj, LaxMonoidal.left_unitality,
    whiskerRight_η_ε_assoc]

/-- The comparison `F.obj (Y ⟶[C] 𝟙_ C) ⟶ (F.obj Y ⟶[D] 𝟙_ D)` of the duals is compatible with
evaluation: evaluating after it is the image of the evaluation of `Y`, preceded by the tensor
comparison and followed by the inverse unit comparison. -/
@[reassoc]
theorem whiskerLeft_ihomComparison_app_unit_comp_map_η_comp_ev (Y : C) [Closed Y]
    [Closed (F.obj Y)] :
    F.obj Y ◁ ((F.ihomComparison Y).natTrans.app (𝟙_ C) ≫ (ihom (F.obj Y)).map (η F)) ≫
        (ihom.ev (F.obj Y)).app (𝟙_ D) =
      μ F Y (Y ⟶[C] 𝟙_ C) ≫ F.map ((ihom.ev Y).app (𝟙_ C)) ≫ η F := by
  simp

/-- A strong monoidal functor carries the dual-tensor comparison of `Y` to that of `F.obj Y`: after
the internal Hom comparison, the image of `(Y ⟶[C] 𝟙_ C) ⊗ Z ⟶ (Y ⟶[C] Z)` is the dual-tensor
comparison of `F.obj Y` at `F.obj Z`, preceded by the tensor comparison of `F` and the comparison
`F.obj (Y ⟶[C] 𝟙_ C) ⟶ (F.obj Y ⟶[D] 𝟙_ D)` of the duals. -/
@[reassoc]
theorem map_dualTensorIhom_app_comp_ihomComparison (Y Z : C) [Closed Y] [Closed (F.obj Y)] :
    F.map ((TauCeti.dualTensorIhom Y).app Z) ≫ (F.ihomComparison Y).natTrans.app Z =
      δ F (Y ⟶[C] 𝟙_ C) Z ≫
        ((F.ihomComparison Y).natTrans.app (𝟙_ C) ≫ (ihom (F.obj Y)).map (η F)) ▷ F.obj Z ≫
        (TauCeti.dualTensorIhom (F.obj Y)).app (F.obj Z) := by
  apply uncurry_injective
  simp only [uncurry_eq, MonoidalCategory.whiskerLeft_comp, Category.assoc,
    TauCeti.whiskerLeft_dualTensorIhom_app_comp_ev, ihomComparison_ev, μ_natural_right_assoc,
    ← F.map_comp]
  -- Move the dual comparison past the associator and evaluate it.
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    whiskerLeft_ihomComparison_app_unit_comp_map_η_comp_ev]
  simp only [Functor.comp_obj, Functor.id_obj, curriedTensor_obj_obj, Functor.map_comp,
    map_associator_inv, map_whiskerRight, map_leftUnitor, Category.assoc, μ_δ_assoc,
    comp_whiskerRight]

/-- If the internal Hom comparisons of a strong monoidal functor `F` at `Y` are invertible at `Z`
and at the unit, and the dual-tensor comparison of `F.obj Y` is invertible at `F.obj Z`, then the
image of the dual-tensor comparison of `Y` at `Z` is invertible. -/
theorem isIso_map_dualTensorIhom_app (Y Z : C) [Closed Y] [Closed (F.obj Y)]
    [IsIso ((F.ihomComparison Y).natTrans.app Z)]
    [IsIso ((F.ihomComparison Y).natTrans.app (𝟙_ C))]
    [IsIso ((TauCeti.dualTensorIhom (F.obj Y)).app (F.obj Z))] :
    IsIso (F.map ((TauCeti.dualTensorIhom Y).app Z)) := by
  have : IsIso (F.map ((TauCeti.dualTensorIhom Y).app Z) ≫
      (F.ihomComparison Y).natTrans.app Z) := by
    rw [map_dualTensorIhom_app_comp_ihomComparison]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((F.ihomComparison Y).natTrans.app Z)

end CategoryTheory.Functor

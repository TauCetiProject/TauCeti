/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Closed.Functor
public import TauCeti.CategoryTheory.Monoidal.Rigid.DualFunctor
public import TauCeti.CategoryTheory.Monoidal.Rigid.Mate
public import TauCeti.CategoryTheory.Monoidal.Rigid.OfClosed

/-!
# Exact pairings under strong monoidal functors

A strong monoidal functor `F : C ⥤ D` carries an exact pairing `ExactPairing X Y` in `C` to an
exact pairing `ExactPairing (F.obj X) (F.obj Y)` in `D`: its evaluation and coevaluation are the
images of those of `(X, Y)`, conjugated by the unit and tensor comparisons of `F`
(`CategoryTheory.Functor.mapExactPairing`). In particular, a strong monoidal functor preserves
objects with a left or right dual (`CategoryTheory.Functor.mapHasLeftDual` and
`CategoryTheory.Functor.mapHasRightDual`).

Since right duals are unique up to unique isomorphism, the image `F.obj Xᘁ` of a right dual of
`X` is canonically isomorphic to the right dual `(F.obj X)ᘁ` of its image
(`CategoryTheory.Functor.mapRightDualIso`). These comparisons are natural with respect to adjoint
mates, are identities for the identity functor, and compose along a composite of functors. They
are the comparisons against which a monoidal functor between pivotal categories is required to
preserve the pivotal structure. They are also natural in the functor: a monoidal natural
transformation `τ : F ⟶ G` satisfies `τ_{Xᘁ} ≫ δ^G_X ≫ (τ_X)ᘁ = δ^F_X`.

Between right rigid categories, applying the comparison twice gives the bidual comparison
`κ_X = δ_{Xᘁ} ≫ ((δ_X)ᘁ)⁻¹ : F.obj Xᘁᘁ ≅ (F.obj X)ᘁᘁ`
(`CategoryTheory.Functor.mapDoubleRightDualIso`). It is natural in `X`, so it assembles into a
natural isomorphism `doubleRightDualFunctor C ⋙ F ≅ F ⋙ doubleRightDualFunctor D`. It is the
identity for the identity functor, satisfies `κ^{F ⋙ G}_X = G.map κ^F_X ≫ κ^G_{F X}` for a
composite, and commutes with monoidal natural isomorphisms. It is the comparison along which a
braided functor preserves Drinfeld isomorphisms and a pivotal functor preserves pivotal
structures.

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
* `CategoryTheory.Functor.mapRightDualIso`: the comparison `F.obj Xᘁ ≅ (F.obj X)ᘁ`, characterized
  by `CategoryTheory.Functor.mapRightDualIso_hom_whiskerRight_evaluation`, natural by
  `CategoryTheory.Functor.mapRightDualIso_hom_naturality`, and computed for identities and
  composites by `CategoryTheory.Functor.mapRightDualIso_id` and
  `CategoryTheory.Functor.mapRightDualIso_comp`;
* `CategoryTheory.NatTrans.app_comp_mapRightDualIso_hom_comp_rightAdjointMate` and
  `CategoryTheory.Iso.hom_app_comp_mapRightDualIso_hom`: the comparison is natural with respect to
  monoidal natural transformations and isomorphisms;
* `CategoryTheory.Functor.mapDoubleRightDualIso`: the bidual comparison
  `F.obj Xᘁᘁ ≅ (F.obj X)ᘁᘁ`, characterized by
  `CategoryTheory.Functor.mapDoubleRightDualIso_hom_whiskerRight_evaluation`, natural by
  `CategoryTheory.Functor.mapDoubleRightDualIso_hom_naturality` and
  `CategoryTheory.Iso.hom_app_comp_mapDoubleRightDualIso_hom`, and computed for identities and
  composites by `CategoryTheory.Functor.mapDoubleRightDualIso_id` and
  `CategoryTheory.Functor.mapDoubleRightDualIso_comp`;
* `CategoryTheory.Functor.mapDoubleRightDualNatIso`: the bidual comparisons as a natural
  isomorphism `doubleRightDualFunctor C ⋙ F ≅ F ⋙ doubleRightDualFunctor D`;
* `CategoryTheory.Functor.ihomComparison_isIso_of_exactPairing`: the internal Hom comparison of
  a strong monoidal functor is invertible at an object with a left dual;
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

/-! ### The comparison between the image of a dual and the dual of an image -/

variable (F)

/-- The canonical isomorphism `F.obj Xᘁ ≅ (F.obj X)ᘁ` between the image of the right dual of `X`
under a strong monoidal functor and the right dual of `F.obj X`: both are right duals of
`F.obj X`, the first through the image pairing `F.mapExactPairing X Xᘁ`. -/
noncomputable def mapRightDualIso (X : C) [HasRightDual X] [hFX : HasRightDual (F.obj X)] :
    F.obj Xᘁ ≅ (F.obj X)ᘁ :=
  rightDualIso (F.mapExactPairing X Xᘁ) HasRightDual.exact

variable {F}

/-- Through `F.mapRightDualIso X`, the evaluation of `(F.obj X, (F.obj X)ᘁ)` is the image of the
evaluation of `(X, Xᘁ)`. This characterizes `F.mapRightDualIso X`, by
`CategoryTheory.ExactPairing.rightHom_ext`. -/
@[reassoc]
theorem mapRightDualIso_hom_whiskerRight_evaluation (X : C) [HasRightDual X]
    [hFX : HasRightDual (F.obj X)] :
    (F.mapRightDualIso X).hom ▷ F.obj X ≫ ε_ (F.obj X) (F.obj X)ᘁ =
      μ F Xᘁ X ≫ F.map (ε_ X Xᘁ) ≫ η F :=
  ExactPairing.rightDualIso_hom_whiskerRight_evaluation _ _

/-- Through the inverse of `F.mapRightDualIso X`, the coevaluation of `(F.obj X, (F.obj X)ᘁ)` is
the image of the coevaluation of `(X, Xᘁ)`. -/
@[reassoc]
theorem coevaluation_whiskerLeft_mapRightDualIso_inv (X : C) [HasRightDual X]
    [HasRightDual (F.obj X)] :
    η_ (F.obj X) (F.obj X)ᘁ ≫ F.obj X ◁ (F.mapRightDualIso X).inv =
      ε F ≫ F.map (η_ X Xᘁ) ≫ δ F X Xᘁ := by
  rw [mapRightDualIso, ExactPairing.rightDualIso_inv, ExactPairing.coevaluation_comp_rightMate]
  simp

/-- Naturality of `F.mapRightDualIso`: it intertwines the image of the mate of `f` with the mate
of the image of `f`. -/
@[reassoc]
theorem mapRightDualIso_hom_naturality {X Y : C} [HasRightDual X] [HasRightDual Y]
    [HasRightDual (F.obj X)] [HasRightDual (F.obj Y)] (f : X ⟶ Y) :
    F.map (fᘁ) ≫ (F.mapRightDualIso X).hom = (F.mapRightDualIso Y).hom ≫ (F.map f)ᘁ := by
  refine ExactPairing.rightHom_ext (X := F.obj X) ?_
  -- Both sides evaluate to the image of the evaluation `Yᘁ ◁ f ≫ ε_ Y Yᘁ` of `fᘁ`.
  have h : F.map (fᘁ ▷ X) ≫ F.map (ε_ X Xᘁ) = F.map (Yᘁ ◁ f) ≫ F.map (ε_ Y Yᘁ) := by
    rw [← F.map_comp, rightAdjointMate_comp_evaluation, F.map_comp]
  simp only [comp_whiskerRight, Category.assoc, mapRightDualIso_hom_whiskerRight_evaluation,
    rightAdjointMate_comp_evaluation, ← whisker_exchange_assoc, μ_natural_left_assoc,
    μ_natural_right_assoc, reassoc_of% h]

/-- Naturality of the inverse of `F.mapRightDualIso`. -/
@[reassoc]
theorem mapRightDualIso_inv_naturality {X Y : C} [HasRightDual X] [HasRightDual Y]
    [HasRightDual (F.obj X)] [HasRightDual (F.obj Y)] (f : X ⟶ Y) :
    (F.map f)ᘁ ≫ (F.mapRightDualIso X).inv = (F.mapRightDualIso Y).inv ≫ F.map (fᘁ) := by
  rw [Iso.comp_inv_eq, Category.assoc, mapRightDualIso_hom_naturality, Iso.inv_hom_id_assoc]

/-- For the identity functor, the comparison between the image of a dual and the dual of an image
is the identity. Only `X` needs a right dual; it is passed explicitly as the right dual of
`(𝟭 C).obj X`, which instance search does not unfold to `X`. -/
@[simp]
theorem mapRightDualIso_id (X : C) [hX : HasRightDual X] :
    (𝟭 C).mapRightDualIso X (hFX := hX) = Iso.refl _ := by
  ext
  refine ExactPairing.rightHom_ext (X := X) (Y := Xᘁ) ?_
  refine (mapRightDualIso_hom_whiskerRight_evaluation (F := 𝟭 C) X (hFX := hX)).trans ?_
  simp

/-- For a composite `F ⋙ G`, the comparison between the image of a dual and the dual of an image
is the image under `G` of the comparison for `F`, followed by the comparison for `G`. Only the
objects involved need right duals; that of `G.obj (F.obj X)` is passed explicitly as the right
dual of `(F ⋙ G).obj X`, which instance search does not unfold. -/
@[simp]
theorem mapRightDualIso_comp {E : Type*} [Category* E] [MonoidalCategory E]
    (G : D ⥤ E) [G.Monoidal] (X : C) [HasRightDual X] [HasRightDual (F.obj X)]
    [hGFX : HasRightDual (G.obj (F.obj X))] :
    (F ⋙ G).mapRightDualIso X (hFX := hGFX) =
      G.mapIso (F.mapRightDualIso X) ≪≫ G.mapRightDualIso (F.obj X) := by
  ext
  refine ExactPairing.rightHom_ext (X := G.obj (F.obj X)) (Y := (G.obj (F.obj X))ᘁ) ?_
  refine (mapRightDualIso_hom_whiskerRight_evaluation (F := F ⋙ G) X (hFX := hGFX)).trans ?_
  -- Unfold the objects of the composite, so that the evaluation identities of `F` and `G` apply.
  dsimp only [Functor.comp_obj, Iso.trans_hom, Functor.mapIso_hom]
  rw [comp_whiskerRight_assoc, mapRightDualIso_hom_whiskerRight_evaluation, μ_natural_left_assoc,
    ← G.map_comp_assoc, mapRightDualIso_hom_whiskerRight_evaluation]
  simp

/-! ### Internal Hom comparisons -/

variable (F)

/-- A strong monoidal functor inverts the internal Hom comparison at an object `Y` with a left
dual `X`: both `F.obj (Y ⟶[C] B)` and `F.obj Y ⟶[D] F.obj B` are identified with
`F.obj X ⊗ F.obj B`, through the pairing and its image. -/
theorem ihomComparison_isIso_of_exactPairing (X Y : C) [ExactPairing X Y] [Closed Y]
    [Closed (F.obj Y)] :
    IsIso (F.ihomComparison Y) := by
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

/-- A strong monoidal functor carries the dual-tensor comparison of `Y` to that of `F.obj Y`: after
the internal Hom comparison, the image of `(Y ⟶[C] 𝟙_ C) ⊗ Z ⟶ (Y ⟶[C] Z)` is the dual-tensor
comparison of `F.obj Y` at `F.obj Z`, preceded by the tensor comparison of `F` and the comparison
`F.obj (Y ⟶[C] 𝟙_ C) ⟶ (F.obj Y ⟶[D] 𝟙_ D)` of the duals. -/
@[reassoc]
theorem map_dualTensorIhom_app_comp_ihomComparison (Y Z : C) [Closed Y] [Closed (F.obj Y)] :
    F.map ((TauCeti.dualTensorIhom Y).app Z) ≫ (F.ihomComparison Y).app Z =
      δ F (Y ⟶[C] 𝟙_ C) Z ≫
        ((F.ihomComparison Y).app (𝟙_ C) ≫ (ihom (F.obj Y)).map (η F)) ▷ F.obj Z ≫
        (TauCeti.dualTensorIhom (F.obj Y)).app (F.obj Z) := by
  apply uncurry_injective
  simp only [uncurry_eq, MonoidalCategory.whiskerLeft_comp, Category.assoc,
    TauCeti.whiskerLeft_dualTensorIhom_app_comp_ev, ihomComparison_ev, μ_natural_right_assoc,
    ← F.map_comp]
  -- Move the dual comparison past the associator and evaluate it.
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    whiskerLeft_ihomComparison_app_unit_comp_map_η_comp_ev]
  -- The rest is coherence; fold the associator of `D` into the image of that of `C`.
  simp [← LaxMonoidal.associativity_inv_assoc]

/-- If the internal Hom comparisons of a strong monoidal functor `F` at `Y` are invertible at `Z`
and at the unit, and the dual-tensor comparison of `F.obj Y` is invertible at `F.obj Z`, then the
image of the dual-tensor comparison of `Y` at `Z` is invertible. -/
theorem isIso_map_dualTensorIhom_app (Y Z : C) [Closed Y] [Closed (F.obj Y)]
    [IsIso ((F.ihomComparison Y).app Z)]
    [IsIso ((F.ihomComparison Y).app (𝟙_ C))]
    [IsIso ((TauCeti.dualTensorIhom (F.obj Y)).app (F.obj Z))] :
    IsIso (F.map ((TauCeti.dualTensorIhom Y).app Z)) := by
  have : IsIso (F.map ((TauCeti.dualTensorIhom Y).app Z) ≫
      (F.ihomComparison Y).app Z) := by
    rw [map_dualTensorIhom_app_comp_ihomComparison]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((F.ihomComparison Y).app Z)

end CategoryTheory.Functor

/-! ### Naturality of the dual comparison in the functor -/

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable {F G : C ⥤ D} [F.Monoidal] [G.Monoidal]

/-- A monoidal natural transformation `τ : F ⟶ G` between strong monoidal functors is compatible
with the comparisons between images of duals and duals of images:
`τ_{Xᘁ} ≫ δ^G_X ≫ (τ_X)ᘁ = δ^F_X` as morphisms `F.obj Xᘁ ⟶ (F.obj X)ᘁ`. -/
@[reassoc]
theorem NatTrans.app_comp_mapRightDualIso_hom_comp_rightAdjointMate (τ : F ⟶ G) [τ.IsMonoidal]
    (X : C) [HasRightDual X] [HasRightDual (F.obj X)] [HasRightDual (G.obj X)] :
    τ.app Xᘁ ≫ (G.mapRightDualIso X).hom ≫ (τ.app X)ᘁ = (F.mapRightDualIso X).hom := by
  have hη : τ.app (𝟙_ C) ≫ η G = η F := by
    rw [← cancel_epi (ε F), IsMonoidal.unit_assoc, ε_η, ε_η]
  refine ExactPairing.rightHom_ext (X := F.obj X) ?_
  -- Both sides evaluate to the image under `F` of the evaluation of `(X, Xᘁ)`; on the left, move
  -- `τ` past the evaluation through its compatibility with the tensor and unit comparisons.
  rw [Functor.mapRightDualIso_hom_whiskerRight_evaluation]
  simp only [comp_whiskerRight, Category.assoc, rightAdjointMate_comp_evaluation]
  rw [← whisker_exchange_assoc, Functor.mapRightDualIso_hom_whiskerRight_evaluation,
    ← tensorHom_def_assoc, ← IsMonoidal.tensor_assoc, ← τ.naturality_assoc, hη]

/-- A monoidal natural isomorphism `α : F ≅ G` intertwines the comparisons between images of
duals and duals of images: `α_{Xᘁ} ≫ δ^G_X = δ^F_X ≫ (α_X⁻¹)ᘁ`. -/
@[reassoc]
theorem Iso.hom_app_comp_mapRightDualIso_hom (α : F ≅ G) [α.hom.IsMonoidal] (X : C)
    [HasRightDual X] [HasRightDual (F.obj X)] [HasRightDual (G.obj X)] :
    α.hom.app Xᘁ ≫ (G.mapRightDualIso X).hom = (F.mapRightDualIso X).hom ≫ (α.inv.app X)ᘁ := by
  rw [← NatTrans.app_comp_mapRightDualIso_hom_comp_rightAdjointMate α.hom X, Category.assoc,
    Category.assoc, ← comp_rightAdjointMate, Iso.inv_hom_id_app, rightAdjointMate_id,
    Category.comp_id]

end CategoryTheory

namespace CategoryTheory.Functor

open TauCeti

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-! ### The bidual comparison -/

section DoubleRightDual

variable [RightRigidCategory C] [RightRigidCategory D] (F : C ⥤ D) [F.Monoidal]

/-- The bidual comparison `κ_X : F.obj Xᘁᘁ ≅ (F.obj X)ᘁᘁ` of a strong monoidal functor between
right rigid categories: the comparison `δ_{Xᘁ} : F.obj Xᘁᘁ ≅ (F.obj Xᘁ)ᘁ`, followed by the
inverse of the right dual `(δ_X)ᘁ : (F.obj X)ᘁᘁ ≅ (F.obj Xᘁ)ᘁ` of `δ_X : F.obj Xᘁ ≅ (F.obj X)ᘁ`. -/
noncomputable def mapDoubleRightDualIso (X : C) :
    F.obj ((Xᘁ : C)ᘁ) ≅ (((F.obj X)ᘁ : D)ᘁ : D) :=
  F.mapRightDualIso Xᘁ ≪≫ (F.mapRightDualIso X).symm.rightAdjointMate

variable {F}

/-- The bidual comparison is `κ_X = δ_{Xᘁ} ≫ (δ_X⁻¹)ᘁ`. -/
theorem mapDoubleRightDualIso_hom (X : C) :
    (F.mapDoubleRightDualIso X).hom =
      (F.mapRightDualIso Xᘁ).hom ≫ ((F.mapRightDualIso X).inv)ᘁ := by
  simp [mapDoubleRightDualIso]

/-- The inverse of the bidual comparison is `κ_X⁻¹ = (δ_X)ᘁ ≫ δ_{Xᘁ}⁻¹`. -/
theorem mapDoubleRightDualIso_inv (X : C) :
    (F.mapDoubleRightDualIso X).inv =
      ((F.mapRightDualIso X).hom)ᘁ ≫ (F.mapRightDualIso Xᘁ).inv := by
  simp [mapDoubleRightDualIso]

/-- Through the bidual comparison `κ_X`, the evaluation of `((F.obj X)ᘁ, (F.obj X)ᘁᘁ)` is the image
of the evaluation of `(Xᘁ, Xᘁᘁ)`, after identifying `(F.obj X)ᘁ` with `F.obj Xᘁ` along `δ_X`. -/
@[reassoc]
theorem mapDoubleRightDualIso_hom_whiskerRight_evaluation (X : C) :
    (F.mapDoubleRightDualIso X).hom ▷ (F.obj X)ᘁ ≫ ε_ (F.obj X)ᘁ (F.obj X)ᘁᘁ =
      F.obj Xᘁᘁ ◁ (F.mapRightDualIso X).inv ≫ μ F Xᘁᘁ Xᘁ ≫ F.map (ε_ Xᘁ Xᘁᘁ) ≫ η F := by
  rw [mapDoubleRightDualIso_hom, comp_whiskerRight, Category.assoc,
    rightAdjointMate_comp_evaluation, ← whisker_exchange_assoc,
    mapRightDualIso_hom_whiskerRight_evaluation]

/-- Naturality of the bidual comparison: it intertwines the image of the double mate of `f` with
the double mate of the image of `f`. -/
@[reassoc]
theorem mapDoubleRightDualIso_hom_naturality {X Y : C} (f : X ⟶ Y) :
    F.map (fᘁᘁ) ≫ (F.mapDoubleRightDualIso Y).hom =
      (F.mapDoubleRightDualIso X).hom ≫ (F.map f)ᘁᘁ := by
  rw [mapDoubleRightDualIso_hom, mapDoubleRightDualIso_hom, mapRightDualIso_hom_naturality_assoc,
    Category.assoc, ← comp_rightAdjointMate, ← comp_rightAdjointMate,
    mapRightDualIso_inv_naturality]

/-- For the identity functor, the bidual comparison is the identity. -/
@[simp]
theorem mapDoubleRightDualIso_id (X : C) : (𝟭 C).mapDoubleRightDualIso X = Iso.refl _ := by
  ext
  simp [mapDoubleRightDualIso_hom]

/-- For a composite `F ⋙ G`, the bidual comparison is the image under `G` of the bidual comparison
for `F`, followed by the bidual comparison for `G`: `κ^{F ⋙ G}_X = G.map κ^F_X ≫ κ^G_{F X}`. -/
@[simp]
theorem mapDoubleRightDualIso_comp {E : Type*} [Category* E] [MonoidalCategory E]
    [RightRigidCategory E] (G : D ⥤ E) [G.Monoidal] (X : C) :
    (F ⋙ G).mapDoubleRightDualIso X =
      G.mapIso (F.mapDoubleRightDualIso X) ≪≫ G.mapDoubleRightDualIso (F.obj X) := by
  ext
  simp only [mapDoubleRightDualIso_hom, mapRightDualIso_comp, Iso.trans_hom, Iso.trans_inv,
    mapIso_hom, mapIso_inv, comp_rightAdjointMate, Functor.map_comp, Category.assoc]
  -- The comparison `δ` of `G` slides past the image of the inverse of that of `F`.
  rw [mapRightDualIso_hom_naturality_assoc]

/-- A monoidal natural isomorphism `α : F ≅ G` intertwines the bidual comparisons:
`α_{Xᘁᘁ} ≫ κ^G_X = κ^F_X ≫ (α_X)ᘁᘁ`. -/
@[reassoc]
theorem _root_.CategoryTheory.Iso.hom_app_comp_mapDoubleRightDualIso_hom {G : C ⥤ D}
    [G.Monoidal] (α : F ≅ G) [α.hom.IsMonoidal] (X : C) :
    α.hom.app Xᘁᘁ ≫ (G.mapDoubleRightDualIso X).hom =
      (F.mapDoubleRightDualIso X).hom ≫ (α.hom.app X)ᘁᘁ := by
  -- The inverse of a monoidal natural isomorphism is monoidal; this instance is stated for
  -- `α.inv`, which instance search does not identify with `α.symm.hom`.
  have : α.symm.hom.IsMonoidal := inferInstanceAs α.inv.IsMonoidal
  have h : (α.hom.app X)ᘁ ≫ (F.mapRightDualIso X).inv =
      (G.mapRightDualIso X).inv ≫ α.inv.app Xᘁ := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact (Iso.hom_app_comp_mapRightDualIso_hom α.symm X).symm
  rw [mapDoubleRightDualIso_hom, mapDoubleRightDualIso_hom, Category.assoc,
    ← comp_rightAdjointMate, h, comp_rightAdjointMate,
    ← Iso.hom_app_comp_mapRightDualIso_hom_assoc]

variable (F)

/-- The bidual comparisons of a strong monoidal functor `F` between right rigid categories, as a
natural isomorphism `doubleRightDualFunctor C ⋙ F ≅ F ⋙ doubleRightDualFunctor D`. -/
noncomputable def mapDoubleRightDualNatIso :
    doubleRightDualFunctor C ⋙ F ≅ F ⋙ doubleRightDualFunctor D :=
  NatIso.ofComponents F.mapDoubleRightDualIso fun f => mapDoubleRightDualIso_hom_naturality f

variable {F}

/-- The components of `F.mapDoubleRightDualNatIso` are the bidual comparisons. -/
@[simp]
theorem mapDoubleRightDualNatIso_hom_app (X : C) :
    F.mapDoubleRightDualNatIso.hom.app X = (F.mapDoubleRightDualIso X).hom :=
  (rfl)

/-- The components of the inverse of `F.mapDoubleRightDualNatIso` are the inverse bidual
comparisons. -/
@[simp]
theorem mapDoubleRightDualNatIso_inv_app (X : C) :
    F.mapDoubleRightDualNatIso.inv.app X = (F.mapDoubleRightDualIso X).inv :=
  (rfl)

end DoubleRightDual

end CategoryTheory.Functor

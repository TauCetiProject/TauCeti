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

Since duals are unique up to unique isomorphism, the image `F.obj Xᘁ` of a right dual of `X` is
canonically isomorphic to the right dual `(F.obj X)ᘁ` of its image
(`CategoryTheory.Functor.mapRightDualIso`), and dually `F.obj (ᘁY) ≅ ᘁ(F.obj Y)` for left duals
(`CategoryTheory.Functor.mapLeftDualIso`). These comparisons are natural with respect to adjoint
mates, are identities for the identity functor, and compose along a composite of functors. They
are the comparisons against which a monoidal functor between pivotal categories is required to
preserve the pivotal structure. They are also natural in the functor: a monoidal natural
transformation `τ : F ⟶ G` satisfies `τ_{Xᘁ} ≫ δ^G_X ≫ (τ_X)ᘁ = δ^F_X`, and dually for left
duals. Moreover, for any exact pairing `(X, Y)` in `C`, the explicit mate of `τ_X` is a two-sided
inverse to `τ_Y`, so every monoidal natural transformation between strong monoidal functors out of
a left or right rigid category is an isomorphism
(`CategoryTheory.NatTrans.isIso_of_leftRigidCategory` and
`CategoryTheory.NatTrans.isIso_of_rightRigidCategory`). Even when `G` is only lax monoidal,
the component of a monoidal natural transformation `F ⟶ G` at one member of an exact pairing
determines its component at the other (`CategoryTheory.NatTrans.app_right_eq_of_exactPairing` and
`CategoryTheory.NatTrans.app_left_eq_of_exactPairing`).

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

A strong monoidal functor `F` *sends a self-duality* `ExactPairing g g` to a self-duality
`ExactPairing V V` along an isomorphism `e : F.obj g ≅ V` when the coevaluation and evaluation of
`V` are the images of those of `g`, transported along `e` and the comparisons of `F`
(`TauCeti.SendsSelfDuality`). This is the condition in universal properties of monoidal
categories presented by self-dual generators.

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
* `CategoryTheory.Functor.mapRightDualIso` and `CategoryTheory.Functor.mapLeftDualIso`: the
  comparisons `F.obj Xᘁ ≅ (F.obj X)ᘁ` and `F.obj (ᘁY) ≅ ᘁ(F.obj Y)`, characterized by
  `CategoryTheory.Functor.mapRightDualIso_hom_whiskerRight_evaluation` and
  `CategoryTheory.Functor.whiskerLeft_mapLeftDualIso_hom_evaluation`, natural with respect to
  mates, and computed for identities and composites;
* `CategoryTheory.NatTrans.app_comp_mapRightDualIso_hom_comp_rightAdjointMate`,
  `CategoryTheory.NatTrans.app_comp_mapLeftDualIso_hom_comp_leftAdjointMate`,
  `CategoryTheory.Iso.hom_app_comp_mapRightDualIso_hom` and
  `CategoryTheory.Iso.hom_app_comp_mapLeftDualIso_hom`: the comparisons are natural with respect to
  monoidal natural transformations and isomorphisms;
* `CategoryTheory.NatTrans.isIso_app_right_of_exactPairing`,
  `CategoryTheory.NatTrans.isIso_app_left_of_exactPairing`,
  `CategoryTheory.NatTrans.isIso_of_rightRigidCategory` and
  `CategoryTheory.NatTrans.isIso_of_leftRigidCategory`: monoidal natural transformations between
  strong monoidal functors are invertible at objects participating in an exact pairing;
* `CategoryTheory.NatTrans.app_right_eq_of_exactPairing` and
  `CategoryTheory.NatTrans.app_left_eq_of_exactPairing`: monoidal natural transformations from a
  strong monoidal functor to a lax monoidal functor are determined on one member of an exact
  pairing by their component on the other;
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
  strong monoidal functor;
* `TauCeti.SendsSelfDuality`: a strong monoidal functor sends one self-duality to another
  along an isomorphism.
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
noncomputable def mapRightDualIso (X : C) [HasRightDual X] [_hFX : HasRightDual (F.obj X)] :
    F.obj Xᘁ ≅ (F.obj X)ᘁ :=
  rightDualIso (F.mapExactPairing X Xᘁ) HasRightDual.exact

variable {F}

/-- Through `F.mapRightDualIso X`, the evaluation of `(F.obj X, (F.obj X)ᘁ)` is the image of the
evaluation of `(X, Xᘁ)`. This characterizes `F.mapRightDualIso X`, by
`CategoryTheory.ExactPairing.rightHom_ext`. -/
@[reassoc]
theorem mapRightDualIso_hom_whiskerRight_evaluation (X : C) [HasRightDual X]
    [_hFX : HasRightDual (F.obj X)] :
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
    (𝟭 C).mapRightDualIso X (_hFX := hX) = Iso.refl _ := by
  ext
  refine ExactPairing.rightHom_ext (X := X) (Y := Xᘁ) ?_
  refine (mapRightDualIso_hom_whiskerRight_evaluation (F := 𝟭 C) X (_hFX := hX)).trans ?_
  simp

/-- For a composite `F ⋙ G`, the comparison between the image of a dual and the dual of an image
is the image under `G` of the comparison for `F`, followed by the comparison for `G`. Only the
objects involved need right duals; that of `G.obj (F.obj X)` is passed explicitly as the right
dual of `(F ⋙ G).obj X`, which instance search does not unfold. -/
@[simp]
theorem mapRightDualIso_comp {E : Type*} [Category* E] [MonoidalCategory E]
    (G : D ⥤ E) [G.Monoidal] (X : C) [HasRightDual X] [HasRightDual (F.obj X)]
    [hGFX : HasRightDual (G.obj (F.obj X))] :
    (F ⋙ G).mapRightDualIso X (_hFX := hGFX) =
      G.mapIso (F.mapRightDualIso X) ≪≫ G.mapRightDualIso (F.obj X) := by
  ext
  refine ExactPairing.rightHom_ext (X := G.obj (F.obj X)) (Y := (G.obj (F.obj X))ᘁ) ?_
  refine (mapRightDualIso_hom_whiskerRight_evaluation (F := F ⋙ G) X (_hFX := hGFX)).trans ?_
  -- Unfold the objects of the composite, so that the evaluation identities of `F` and `G` apply.
  dsimp only [Functor.comp_obj, Iso.trans_hom, Functor.mapIso_hom]
  rw [comp_whiskerRight_assoc, mapRightDualIso_hom_whiskerRight_evaluation, μ_natural_left_assoc,
    ← G.map_comp_assoc, mapRightDualIso_hom_whiskerRight_evaluation]
  simp

variable (F)

/-- The canonical isomorphism `F.obj (ᘁY) ≅ ᘁ(F.obj Y)` between the image of the left dual of `Y`
under a strong monoidal functor and the left dual of `F.obj Y`: both are left duals of `F.obj Y`,
the first through the image pairing `F.mapExactPairing (ᘁY) Y`. -/
noncomputable def mapLeftDualIso (Y : C) [HasLeftDual Y] [_hFY : HasLeftDual (F.obj Y)] :
    F.obj (ᘁY) ≅ ᘁ(F.obj Y) :=
  leftDualIso (F.mapExactPairing (ᘁY) Y) HasLeftDual.exact

variable {F}

/-- Through `F.mapLeftDualIso Y`, the evaluation of `(ᘁ(F.obj Y), F.obj Y)` is the image of the
evaluation of `(ᘁY, Y)`. This characterizes `F.mapLeftDualIso Y`, by
`CategoryTheory.ExactPairing.leftDualHom_ext`. -/
@[reassoc]
theorem whiskerLeft_mapLeftDualIso_hom_evaluation (Y : C) [HasLeftDual Y]
    [_hFY : HasLeftDual (F.obj Y)] :
    F.obj Y ◁ (F.mapLeftDualIso Y).hom ≫ ε_ (ᘁ(F.obj Y)) (F.obj Y) =
      μ F Y (ᘁY) ≫ F.map (ε_ (ᘁY) Y) ≫ η F :=
  ExactPairing.whiskerLeft_leftDualIso_hom_evaluation _ _

/-- Through the inverse of `F.mapLeftDualIso Y`, the coevaluation of `(ᘁ(F.obj Y), F.obj Y)` is
the image of the coevaluation of `(ᘁY, Y)`. -/
@[reassoc]
theorem coevaluation_mapLeftDualIso_inv_whiskerRight (Y : C) [HasLeftDual Y]
    [HasLeftDual (F.obj Y)] :
    η_ (ᘁ(F.obj Y)) (F.obj Y) ≫ (F.mapLeftDualIso Y).inv ▷ F.obj Y =
      ε F ≫ F.map (η_ (ᘁY) Y) ≫ δ F (ᘁY) Y := by
  rw [mapLeftDualIso, ExactPairing.leftDualIso_inv, ExactPairing.coevaluation_comp_leftMate]
  simp

/-- Naturality of `F.mapLeftDualIso`: it intertwines the image of the left mate of `f` with the
left mate of the image of `f`. -/
@[reassoc]
theorem mapLeftDualIso_hom_naturality {X Y : C} [HasLeftDual X] [HasLeftDual Y]
    [HasLeftDual (F.obj X)] [HasLeftDual (F.obj Y)] (f : X ⟶ Y) :
    F.map (ᘁf) ≫ (F.mapLeftDualIso X).hom = (F.mapLeftDualIso Y).hom ≫ ᘁ(F.map f) := by
  refine ExactPairing.leftDualHom_ext (Y := F.obj X) ?_
  -- Both sides evaluate to the image of the evaluation `f ▷ ᘁY ≫ ε_ (ᘁY) Y` of `ᘁf`.
  have h : F.map (X ◁ ᘁf) ≫ F.map (ε_ (ᘁX) X) = F.map (f ▷ ᘁY) ≫ F.map (ε_ (ᘁY) Y) := by
    rw [← F.map_comp, leftAdjointMate_comp_evaluation, F.map_comp]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc,
    whiskerLeft_mapLeftDualIso_hom_evaluation, leftAdjointMate_comp_evaluation,
    whisker_exchange_assoc, μ_natural_left_assoc, μ_natural_right_assoc, reassoc_of% h]

/-- Naturality of the inverse of `F.mapLeftDualIso`. -/
@[reassoc]
theorem mapLeftDualIso_inv_naturality {X Y : C} [HasLeftDual X] [HasLeftDual Y]
    [HasLeftDual (F.obj X)] [HasLeftDual (F.obj Y)] (f : X ⟶ Y) :
    (ᘁF.map f) ≫ (F.mapLeftDualIso X).inv = (F.mapLeftDualIso Y).inv ≫ F.map (ᘁf) := by
  rw [Iso.comp_inv_eq, Category.assoc, mapLeftDualIso_hom_naturality, Iso.inv_hom_id_assoc]

/-- For the identity functor, the comparison between the image of a left dual and the left dual of
an image is the identity. Only `Y` needs a left dual; it is passed explicitly as the left dual of
`(𝟭 C).obj Y`, which instance search does not unfold to `Y`. -/
@[simp]
theorem mapLeftDualIso_id (Y : C) [hY : HasLeftDual Y] :
    (𝟭 C).mapLeftDualIso Y (_hFY := hY) = Iso.refl _ := by
  ext
  refine ExactPairing.leftDualHom_ext (X := ᘁY) (Y := Y) ?_
  refine (whiskerLeft_mapLeftDualIso_hom_evaluation (F := 𝟭 C) Y (_hFY := hY)).trans ?_
  simp

/-- For a composite `F ⋙ G`, the comparison between the image of a left dual and the left dual of
an image is the image under `G` of the comparison for `F`, followed by the comparison for `G`. -/
@[simp]
theorem mapLeftDualIso_comp {E : Type*} [Category* E] [MonoidalCategory E]
    (G : D ⥤ E) [G.Monoidal] (Y : C) [HasLeftDual Y] [HasLeftDual (F.obj Y)]
    [hGFY : HasLeftDual (G.obj (F.obj Y))] :
    (F ⋙ G).mapLeftDualIso Y (_hFY := hGFY) =
      G.mapIso (F.mapLeftDualIso Y) ≪≫ G.mapLeftDualIso (F.obj Y) := by
  ext
  refine ExactPairing.leftDualHom_ext (X := ᘁ(G.obj (F.obj Y))) (Y := G.obj (F.obj Y)) ?_
  refine (whiskerLeft_mapLeftDualIso_hom_evaluation (F := F ⋙ G) Y (_hFY := hGFY)).trans ?_
  dsimp only [Functor.comp_obj, Iso.trans_hom, Functor.mapIso_hom]
  rw [MonoidalCategory.whiskerLeft_comp_assoc, whiskerLeft_mapLeftDualIso_hom_evaluation,
    μ_natural_right_assoc, ← G.map_comp_assoc, whiskerLeft_mapLeftDualIso_hom_evaluation]
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

/-! ### Sending a self-duality along an isomorphism -/

namespace TauCeti

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- A strong monoidal functor `F : D ⥤ C` *sends the self-duality of `g` to the self-duality of
`V` along `e : F.obj g ≅ V`* when the coevaluation and the evaluation of `V` are the images under
`F` of those of `g`, composed with the unit and tensor comparisons of `F` and with `e`. -/
structure SendsSelfDuality {g : D} [ExactPairing g g] (F : D ⥤ C) [F.Monoidal] (V : C)
    [ExactPairing V V] (e : F.obj g ≅ V) : Prop where
  /-- The coevaluation of `g` is sent to the coevaluation of `V`. -/
  coevaluation : ε F ≫ F.map (η_ g g) = η_ V V ≫ (e.inv ⊗ₘ e.inv) ≫ μ F g g
  /-- The evaluation of `g` is sent to the evaluation of `V`. -/
  evaluation : (e.inv ⊗ₘ e.inv) ≫ μ F g g ≫ F.map (ε_ g g) ≫ η F = ε_ V V

end TauCeti

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

/-- A monoidal natural transformation `τ : F ⟶ G` between strong monoidal functors is compatible
with the comparisons between images of left duals and left duals of images:
`τ_{ᘁY} ≫ δ^G_Y ≫ ᘁ(τ_Y) = δ^F_Y` as morphisms `F.obj (ᘁY) ⟶ ᘁ(F.obj Y)`. -/
@[reassoc]
theorem NatTrans.app_comp_mapLeftDualIso_hom_comp_leftAdjointMate (τ : F ⟶ G) [τ.IsMonoidal]
    (Y : C) [HasLeftDual Y] [HasLeftDual (F.obj Y)] [HasLeftDual (G.obj Y)] :
    τ.app (ᘁY) ≫ (G.mapLeftDualIso Y).hom ≫ (ᘁτ.app Y) = (F.mapLeftDualIso Y).hom := by
  have hη : τ.app (𝟙_ C) ≫ η G = η F := by
    rw [← cancel_epi (ε F), IsMonoidal.unit_assoc, ε_η, ε_η]
  refine ExactPairing.leftDualHom_ext (Y := F.obj Y) ?_
  rw [Functor.whiskerLeft_mapLeftDualIso_hom_evaluation]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc, leftAdjointMate_comp_evaluation]
  rw [whisker_exchange_assoc, Functor.whiskerLeft_mapLeftDualIso_hom_evaluation,
    ← tensorHom_def'_assoc, ← IsMonoidal.tensor_assoc, ← τ.naturality_assoc, hη]

/-- A monoidal natural isomorphism `α : F ≅ G` intertwines the comparisons between images of left
duals and left duals of images: `α_{ᘁY} ≫ δ^G_Y = δ^F_Y ≫ ᘁ(α_Y⁻¹)`. -/
@[reassoc]
theorem Iso.hom_app_comp_mapLeftDualIso_hom (α : F ≅ G) [α.hom.IsMonoidal] (Y : C)
    [HasLeftDual Y] [HasLeftDual (F.obj Y)] [HasLeftDual (G.obj Y)] :
    α.hom.app (ᘁY) ≫ (G.mapLeftDualIso Y).hom = (F.mapLeftDualIso Y).hom ≫ (ᘁα.inv.app Y) := by
  rw [← NatTrans.app_comp_mapLeftDualIso_hom_comp_leftAdjointMate α.hom Y, Category.assoc,
    Category.assoc, ← comp_leftAdjointMate, Iso.inv_hom_id_app, leftAdjointMate_id,
    Category.comp_id]

/-- For an exact pairing `(X, Y)` in `C` and a monoidal natural transformation `τ : F ⟶ G` between
strong monoidal functors, the right mate of `τ.app X` with respect to the image pairings is a right
inverse to `τ.app Y`. -/
@[reassoc]
theorem NatTrans.app_comp_rightMate_mapExactPairing (τ : F ⟶ G) [τ.IsMonoidal] (X Y : C)
    [ExactPairing X Y] :
    τ.app Y ≫ ExactPairing.rightMate (F.mapExactPairing X Y) (G.mapExactPairing X Y) (τ.app X) =
      𝟙 (F.obj Y) := by
  have hη : τ.app (𝟙_ C) ≫ η G = η F := by
    rw [← cancel_epi (ε F), IsMonoidal.unit_assoc, ε_η, ε_η]
  let _ : ExactPairing (F.obj X) (F.obj Y) := F.mapExactPairing X Y
  refine ExactPairing.rightHom_ext (X := F.obj X) ?_
  rw [MonoidalCategory.comp_whiskerRight, Category.assoc,
    ExactPairing.rightMate_comp_evaluation, MonoidalCategory.id_whiskerRight, Category.id_comp,
    Functor.mapExactPairing_evaluation, Functor.mapExactPairing_evaluation, ← tensorHom_def_assoc,
    ← IsMonoidal.tensor_assoc, ← τ.naturality_assoc, hη]

/-- For an exact pairing `(X, Y)` in `C` and a monoidal natural transformation `τ : F ⟶ G` between
strong monoidal functors, the right mate of `τ.app X` with respect to the image pairings is a left
inverse to `τ.app Y`. -/
@[reassoc]
theorem NatTrans.rightMate_mapExactPairing_comp_app (τ : F ⟶ G) [τ.IsMonoidal] (X Y : C)
    [ExactPairing X Y] :
    ExactPairing.rightMate (F.mapExactPairing X Y) (G.mapExactPairing X Y) (τ.app X) ≫ τ.app Y =
      𝟙 (G.obj Y) := by
  have hδ : δ F X Y ≫ (τ.app X ⊗ₘ τ.app Y) = τ.app (X ⊗ Y) ≫ δ G X Y := by
    rw [← cancel_epi (μ F X Y), ← cancel_mono (μ G X Y)]
    simp [IsMonoidal.tensor_assoc]
  let _ : ExactPairing (G.obj X) (G.obj Y) := G.mapExactPairing X Y
  refine ExactPairing.rightDualHom_ext (X := G.obj X) ?_
  rw [MonoidalCategory.whiskerLeft_comp, ExactPairing.coevaluation_comp_rightMate_assoc,
    MonoidalCategory.whiskerLeft_id, Category.comp_id, ← tensorHom_def,
    Functor.mapExactPairing_coevaluation, Functor.mapExactPairing_coevaluation]
  simp only [Category.assoc]
  rw [hδ, τ.naturality_assoc, IsMonoidal.unit_assoc]

/-- For an exact pairing `(X, Y)` in `C` and a monoidal natural transformation `τ : F ⟶ G` between
strong monoidal functors, the left mate of `τ.app Y` with respect to the image pairings is a right
inverse to `τ.app X`. -/
@[reassoc]
theorem NatTrans.app_comp_leftMate_mapExactPairing (τ : F ⟶ G) [τ.IsMonoidal] (X Y : C)
    [ExactPairing X Y] :
    τ.app X ≫ ExactPairing.leftMate (F.mapExactPairing X Y) (G.mapExactPairing X Y) (τ.app Y) =
      𝟙 (F.obj X) := by
  have hη : τ.app (𝟙_ C) ≫ η G = η F := by
    rw [← cancel_epi (ε F), IsMonoidal.unit_assoc, ε_η, ε_η]
  let _ : ExactPairing (F.obj X) (F.obj Y) := F.mapExactPairing X Y
  refine ExactPairing.leftDualHom_ext (Y := F.obj Y) ?_
  rw [MonoidalCategory.whiskerLeft_comp, Category.assoc,
    ExactPairing.leftMate_comp_evaluation, MonoidalCategory.whiskerLeft_id, Category.id_comp,
    Functor.mapExactPairing_evaluation, Functor.mapExactPairing_evaluation, ← tensorHom_def'_assoc,
    ← IsMonoidal.tensor_assoc, ← τ.naturality_assoc, hη]

/-- For an exact pairing `(X, Y)` in `C` and a monoidal natural transformation `τ : F ⟶ G` between
strong monoidal functors, the left mate of `τ.app Y` with respect to the image pairings is a left
inverse to `τ.app X`. -/
@[reassoc]
theorem NatTrans.leftMate_mapExactPairing_comp_app (τ : F ⟶ G) [τ.IsMonoidal] (X Y : C)
    [ExactPairing X Y] :
    ExactPairing.leftMate (F.mapExactPairing X Y) (G.mapExactPairing X Y) (τ.app Y) ≫ τ.app X =
      𝟙 (G.obj X) := by
  have hδ : δ F X Y ≫ (τ.app X ⊗ₘ τ.app Y) = τ.app (X ⊗ Y) ≫ δ G X Y := by
    rw [← cancel_epi (μ F X Y), ← cancel_mono (μ G X Y)]
    simp [IsMonoidal.tensor_assoc]
  let _ : ExactPairing (G.obj X) (G.obj Y) := G.mapExactPairing X Y
  refine ExactPairing.leftHom_ext (Y := G.obj Y) ?_
  rw [MonoidalCategory.comp_whiskerRight, ExactPairing.coevaluation_comp_leftMate_assoc,
    MonoidalCategory.id_whiskerRight, Category.comp_id, ← tensorHom_def',
    Functor.mapExactPairing_coevaluation, Functor.mapExactPairing_coevaluation]
  simp only [Category.assoc]
  rw [hδ, τ.naturality_assoc, IsMonoidal.unit_assoc]

/-- A monoidal natural transformation between strong monoidal functors is invertible at the right
member of any exact pairing. -/
theorem NatTrans.isIso_app_right_of_exactPairing (τ : F ⟶ G) [τ.IsMonoidal] (X Y : C)
    [ExactPairing X Y] : IsIso (τ.app Y) :=
  ⟨⟨ExactPairing.rightMate (F.mapExactPairing X Y) (G.mapExactPairing X Y) (τ.app X),
    τ.app_comp_rightMate_mapExactPairing X Y, τ.rightMate_mapExactPairing_comp_app X Y⟩⟩

/-- A monoidal natural transformation between strong monoidal functors is invertible at the left
member of any exact pairing. -/
theorem NatTrans.isIso_app_left_of_exactPairing (τ : F ⟶ G) [τ.IsMonoidal] (X Y : C)
    [ExactPairing X Y] : IsIso (τ.app X) :=
  ⟨⟨ExactPairing.leftMate (F.mapExactPairing X Y) (G.mapExactPairing X Y) (τ.app Y),
    τ.app_comp_leftMate_mapExactPairing X Y, τ.leftMate_mapExactPairing_comp_app X Y⟩⟩

/-- Every monoidal natural transformation between strong monoidal functors out of a right rigid
category is an isomorphism. -/
theorem NatTrans.isIso_of_rightRigidCategory [RightRigidCategory C] (τ : F ⟶ G) [τ.IsMonoidal] :
    IsIso τ := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact fun X => τ.isIso_app_left_of_exactPairing X Xᘁ

/-- Every monoidal natural transformation between strong monoidal functors out of a left rigid
category is an isomorphism. -/
theorem NatTrans.isIso_of_leftRigidCategory [LeftRigidCategory C] (τ : F ⟶ G) [τ.IsMonoidal] :
    IsIso τ := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact fun Y => τ.isIso_app_right_of_exactPairing (ᘁY) Y

section LaxTarget

private theorem comp_coevaluation_lax {H : C ⥤ D} [H.LaxMonoidal] (τ : F ⟶ H) [τ.IsMonoidal]
    (X Y : C) [ExactPairing X Y] :
    ε F ≫ F.map (η_ X Y) ≫ δ F X Y ≫ (τ.app X ⊗ₘ τ.app Y) ≫ μ H X Y =
      ε H ≫ H.map (η_ X Y) := by
  rw [← NatTrans.IsMonoidal.tensor, δ_μ_assoc, τ.naturality, NatTrans.IsMonoidal.unit_assoc]

private theorem comp_evaluation_lax {H : C ⥤ D} [H.LaxMonoidal] (τ : F ⟶ H) [τ.IsMonoidal]
    (X Y : C) [ExactPairing X Y] :
    (τ.app Y ⊗ₘ τ.app X) ≫ μ H Y X ≫ H.map (ε_ X Y) =
      (μ F Y X ≫ F.map (ε_ X Y) ≫ η F) ≫ ε H := by
  rw [← NatTrans.IsMonoidal.tensor_assoc, ← τ.naturality, Category.assoc, Category.assoc,
    ← NatTrans.IsMonoidal.unit (τ := τ), ← Category.assoc (η F), η_ε, Category.id_comp]

/-- If two monoidal natural transformations from a strong monoidal functor `F` to a lax monoidal
functor `H` agree on the left member `X` of an exact pairing `(X, Y)`, then they agree on the right
member `Y`. -/
theorem NatTrans.app_right_eq_of_exactPairing {H : C ⥤ D} [H.LaxMonoidal] {α β : F ⟶ H}
    [α.IsMonoidal] [β.IsMonoidal] (X Y : C) [ExactPairing X Y] (h : α.app X = β.app X) :
    α.app Y = β.app Y := by
  -- Express both `α.app Y` and `β.app Y` as the same snake composite through `α.app Y ⊗ α.app X ⊗
  -- β.app Y`: grouping the right two factors uses `β` on `η_ X Y`, while grouping the left two uses
  -- `α` on `ε_ X Y`.
  have hcoev := comp_coevaluation_lax (F := F) β X Y
  have h₁ :
      (ρ_ (F.obj Y)).inv ≫ F.obj Y ◁ (ε F ≫ F.map (η_ X Y) ≫ δ F X Y) ≫
          (α.app Y ⊗ₘ (β.app X ⊗ₘ β.app Y)) ≫ H.obj Y ◁ μ H X Y ≫ μ H Y (X ⊗ Y) ≫
          H.map ((α_ Y X Y).inv ≫ ε_ X Y ▷ Y ≫ (λ_ Y).hom) =
        α.app Y := by
    rw [tensorHom_def' (α.app Y) (β.app X ⊗ₘ β.app Y)]
    simp only [Category.assoc] at hcoev ⊢
    rw [← whisker_exchange_assoc (α.app Y) (μ H X Y), ← MonoidalCategory.whiskerLeft_comp_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc]
    simp only [Category.assoc, hcoev, MonoidalCategory.whiskerLeft_comp]
    rw [whisker_exchange_assoc, whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc,
      H.map_comp, μ_natural_right_assoc,
      Functor.LaxMonoidal.right_unitality_inv_assoc, ← H.map_comp, ← H.map_comp,
      ExactPairing.coevaluation_evaluation_assoc, Iso.inv_hom_id, Category.comp_id,
      ← H.map_comp, Iso.inv_hom_id, H.map_id, Category.comp_id]
  have h₂ :
      (ρ_ (F.obj Y)).inv ≫ F.obj Y ◁ (ε F ≫ F.map (η_ X Y) ≫ δ F X Y) ≫
          (α.app Y ⊗ₘ (α.app X ⊗ₘ β.app Y)) ≫ H.obj Y ◁ μ H X Y ≫ μ H Y (X ⊗ Y) ≫
          H.map ((α_ Y X Y).inv ≫ ε_ X Y ▷ Y ≫ (λ_ Y).hom) =
        β.app Y := by
    let _ : ExactPairing (F.obj X) (F.obj Y) := F.mapExactPairing X Y
    have hzig :
        (ρ_ (F.obj Y)).inv ≫ F.obj Y ◁ (ε F ≫ F.map (η_ X Y) ≫ δ F X Y) ≫
            (α_ (F.obj Y) (F.obj X) (F.obj Y)).inv ≫
            (μ F Y X ≫ F.map (ε_ X Y) ≫ η F) ▷ F.obj Y =
          (λ_ (F.obj Y)).inv := by
      rw [← Functor.mapExactPairing_coevaluation, ← Functor.mapExactPairing_evaluation,
        ExactPairing.coevaluation_evaluation, Iso.inv_hom_id_assoc]
    rw [H.map_comp, H.map_comp, Functor.LaxMonoidal.associativity_inv_assoc,
      associator_inv_naturality_assoc, tensorHom_comp_whiskerRight_assoc,
      ← μ_natural_left_assoc, tensorHom_comp_whiskerRight_assoc,
      Category.assoc (α.app Y ⊗ₘ α.app X), comp_evaluation_lax (F := F) α X Y,
      tensorHom_def ((μ F Y X ≫ F.map (ε_ X Y) ≫ η F) ≫ ε H) (β.app Y),
      MonoidalCategory.comp_whiskerRight_assoc (μ F Y X ≫ F.map (ε_ X Y) ≫ η F) (ε H)]
    simp only [Category.assoc]
    rw [reassoc_of% hzig, ← tensorHom_def_assoc (ε H) (β.app Y),
      ← Functor.LaxMonoidal.tensorUnit_whiskerLeft_comp_leftUnitor_hom,
      leftUnitor_naturality, Iso.inv_hom_id_assoc]
  rw [← h₁, ← h, h₂]

/-- If two monoidal natural transformations from a strong monoidal functor `F` to a lax monoidal
functor `H` agree on the right member `Y` of an exact pairing `(X, Y)`, then they agree on the left
member `X`. -/
theorem NatTrans.app_left_eq_of_exactPairing {H : C ⥤ D} [H.LaxMonoidal] {α β : F ⟶ H}
    [α.IsMonoidal] [β.IsMonoidal] (X Y : C) [ExactPairing X Y] (h : α.app Y = β.app Y) :
    α.app X = β.app X := by
  -- Dual snake composite through `β.app X ⊗ α.app Y ⊗ α.app X`.
  have hcoev := comp_coevaluation_lax (F := F) β X Y
  have h₁ :
      (λ_ (F.obj X)).inv ≫ (ε F ≫ F.map (η_ X Y) ≫ δ F X Y) ▷ F.obj X ≫
          ((β.app X ⊗ₘ β.app Y) ⊗ₘ α.app X) ≫ μ H X Y ▷ H.obj X ≫ μ H (X ⊗ Y) X ≫
          H.map ((α_ X Y X).hom ≫ X ◁ ε_ X Y ≫ (ρ_ X).hom) =
        α.app X := by
    rw [tensorHom_def (β.app X ⊗ₘ β.app Y) (α.app X)]
    simp only [Category.assoc] at hcoev ⊢
    rw [whisker_exchange_assoc (μ H X Y) (α.app X), ← MonoidalCategory.comp_whiskerRight_assoc,
      ← MonoidalCategory.comp_whiskerRight_assoc]
    simp only [Category.assoc, hcoev, MonoidalCategory.comp_whiskerRight]
    rw [← whisker_exchange_assoc, ← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc,
      H.map_comp, μ_natural_left_assoc,
      Functor.LaxMonoidal.left_unitality_inv_assoc, ← H.map_comp, ← H.map_comp,
      ExactPairing.evaluation_coevaluation_assoc, Iso.inv_hom_id, Category.comp_id,
      ← H.map_comp, Iso.inv_hom_id, H.map_id, Category.comp_id]
  have h₂ :
      (λ_ (F.obj X)).inv ≫ (ε F ≫ F.map (η_ X Y) ≫ δ F X Y) ▷ F.obj X ≫
          ((β.app X ⊗ₘ α.app Y) ⊗ₘ α.app X) ≫ μ H X Y ▷ H.obj X ≫ μ H (X ⊗ Y) X ≫
          H.map ((α_ X Y X).hom ≫ X ◁ ε_ X Y ≫ (ρ_ X).hom) =
        β.app X := by
    let _ : ExactPairing (F.obj X) (F.obj Y) := F.mapExactPairing X Y
    have hzig :
        (λ_ (F.obj X)).inv ≫ (ε F ≫ F.map (η_ X Y) ≫ δ F X Y) ▷ F.obj X ≫
            (α_ (F.obj X) (F.obj Y) (F.obj X)).hom ≫
            F.obj X ◁ (μ F Y X ≫ F.map (ε_ X Y) ≫ η F) =
          (ρ_ (F.obj X)).inv := by
      rw [← Functor.mapExactPairing_coevaluation, ← Functor.mapExactPairing_evaluation,
        ExactPairing.evaluation_coevaluation, Iso.inv_hom_id_assoc]
    rw [H.map_comp, H.map_comp, Functor.LaxMonoidal.associativity_assoc,
      associator_naturality_assoc, tensorHom_comp_whiskerLeft_assoc,
      ← μ_natural_right_assoc, tensorHom_comp_whiskerLeft_assoc,
      Category.assoc (α.app Y ⊗ₘ α.app X), comp_evaluation_lax (F := F) α X Y,
      tensorHom_def' (β.app X) ((μ F Y X ≫ F.map (ε_ X Y) ≫ η F) ≫ ε H),
      MonoidalCategory.whiskerLeft_comp_assoc (F.obj X) (μ F Y X ≫ F.map (ε_ X Y) ≫ η F) (ε H)]
    simp only [Category.assoc]
    rw [reassoc_of% hzig, ← tensorHom_def'_assoc (β.app X) (ε H),
      ← Functor.LaxMonoidal.whiskerRight_tensorUnit_comp_rightUnitor_hom,
      rightUnitor_naturality, Iso.inv_hom_id_assoc]
  rw [← h₁, ← h, h₂]

end LaxTarget

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

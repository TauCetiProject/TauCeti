/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.Tensor
public import TauCeti.CategoryTheory.Monoidal.Rigid.LeftDualFunctor

/-!
# Left and right duals in a pivotal category

In a rigid monoidal category the left dual `ᘁX` and the right dual `Xᘁ` of an object need not be
isomorphic. A pivotal structure `φ_X : X ≅ Xᘁᘁ` makes `X` a right dual of `Xᘁ`
(`TauCeti.pivotalExactPairing`), so `Xᘁ` becomes a second left dual of `X`, and comparing it with
the chosen left dual gives an isomorphism `ᘁX ≅ Xᘁ`. These isomorphisms are natural in `X` and
compatible with the unit and tensor comparisons, so they identify the left and right dual functors
`C ⥤ (Cᵒᵖ)ᴹᵒᵖ` as monoidal functors. Conversely the identification determines the pivotal
structure: `φ_X` is the right mate of the comparison `Xᘁ ≅ ᘁX`.

The same observation shows that a pivotal structure needs only right duals to make sense. If `C`
is merely right rigid, an isomorphism `X ≅ Xᘁᘁ` for every `X` makes `Xᘁ` a left dual of `X`, so `C`
is rigid; when the isomorphisms form a monoidal natural isomorphism `𝟭 C ≅ doubleRightDualFunctor C`
they are a pivotal structure for that rigid structure (`TauCeti.pivotalCategoryOfRightRigid`),
whose left duals are the right duals, and the comparison `ᘁX ≅ Xᘁ` for it is the identity.

## Main declarations

* `TauCeti.leftDualIsoRightDual`: the isomorphism `ᘁX ≅ Xᘁ` in a pivotal category, characterized
  by `TauCeti.whiskerLeft_leftDualIsoRightDual_hom_comp_evaluation` and
  `TauCeti.rightMate_leftDualIsoRightDual_inv`, natural by
  `TauCeti.leftAdjointMate_comp_leftDualIsoRightDual_hom`, and compatible with the unit and tensor
  comparisons by `TauCeti.leftDualIsoRightDual_unit_inv` and
  `TauCeti.leftDualIsoRightDual_tensor_inv`;
* `TauCeti.dualFunctorIso`: the natural isomorphism `leftDualFunctor C ≅ rightDualFunctor C`,
  monoidal by `TauCeti.dualFunctorIso_isMonoidal`;
* `TauCeti.leftDualIsoRightDual_pivotalCategoryOfRightRigid`: for the pivotal structure
  `TauCeti.pivotalCategoryOfRightRigid` built from a monoidal trivialization of the double right
  dual functor of a right rigid category, left and right duals are identified by the identity.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.7
* [leanprover-community/mathlib4#42150](https://github.com/leanprover-community/mathlib4/pull/42150),
  for the names `leftDualIsoRightDual` and `dualFunctorIso`
-/

public section

open CategoryTheory MonoidalCategory MonoidalOpposite Opposite ExactPairing
open Functor.LaxMonoidal Functor.OplaxMonoidal

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section Pivotal

variable [RigidCategory C] [PivotalCategory C]

/-- In a pivotal category, the left dual `ᘁX` is isomorphic to the right dual `Xᘁ`: both are left
duals of `X`, the latter through the pivotal pairing `pivotalExactPairing X`, and the component is
the comparison `leftDualIso` between them. -/
noncomputable def leftDualIsoRightDual (X : C) : (ᘁX) ≅ Xᘁ :=
  leftDualIso HasLeftDual.exact (pivotalExactPairing X)

/-- The isomorphism `ᘁX ≅ Xᘁ` is the left mate of `𝟙 X` from the chosen left dual of `X` to the
pivotal one. -/
theorem leftDualIsoRightDual_hom (X : C) :
    (leftDualIsoRightDual X).hom = leftMate (pivotalExactPairing X) HasLeftDual.exact (𝟙 X) :=
  leftDualIso_hom _ _

/-- The inverse of the isomorphism `ᘁX ≅ Xᘁ` is the left mate of `𝟙 X` from the pivotal left dual
of `X` to the chosen one. -/
theorem leftDualIsoRightDual_inv (X : C) :
    (leftDualIsoRightDual X).inv = leftMate HasLeftDual.exact (pivotalExactPairing X) (𝟙 X) :=
  leftDualIso_inv _ _

/-- The characteristic property of `leftDualIsoRightDual X`: it carries the evaluation of the
pivotal pairing, `φ_X ▷ Xᘁ ≫ ε_ Xᘁ Xᘁᘁ`, to the evaluation `ε_ (ᘁX) X` of the left dual. -/
@[reassoc]
theorem whiskerLeft_leftDualIsoRightDual_hom_comp_evaluation (X : C) :
    X ◁ (leftDualIsoRightDual X).hom ≫ (pivotalIsoApp X).hom ▷ Xᘁ ≫ ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) =
      ε_ (ᘁX) X := by
  rw [← pivotalExactPairing_evaluation, leftDualIsoRightDual_hom, leftMate_comp_evaluation,
    id_whiskerRight, Category.id_comp]

/-- The coevaluation of the left dual, followed by `leftDualIsoRightDual X`, is the coevaluation of
the pivotal pairing, `η_ Xᘁ Xᘁᘁ ≫ Xᘁ ◁ φ_X⁻¹`. -/
@[reassoc]
theorem coevaluation_comp_leftDualIsoRightDual_hom_whiskerRight (X : C) :
    η_ (ᘁX) X ≫ (leftDualIsoRightDual X).hom ▷ X =
      η_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) ≫ Xᘁ ◁ (pivotalIsoApp X).inv := by
  rw [← pivotalExactPairing_coevaluation, leftDualIsoRightDual_hom, coevaluation_comp_leftMate,
    MonoidalCategory.whiskerLeft_id, Category.comp_id]

/-- **The pivotal structure is determined by the identification of left and right duals**: the
component `φ_X : X ⟶ Xᘁᘁ` is the right mate of the comparison `Xᘁ ⟶ ᘁX`, taken with respect to the
pairings `(Xᘁ, Xᘁᘁ)` and `(ᘁX, X)`. -/
theorem rightMate_leftDualIsoRightDual_inv (X : C) :
    rightMate HasRightDual.exact HasLeftDual.exact (leftDualIsoRightDual X).inv =
      (pivotalIsoApp X).hom :=
  rightHom_ext (X := Xᘁ) (by
    rw [rightMate_comp_evaluation, ← whiskerLeft_leftDualIsoRightDual_hom_comp_evaluation,
      whiskerLeft_inv_hom_assoc])

/-- **Naturality of `leftDualIsoRightDual`**: it intertwines the left adjoint mate `ᘁf` with the
right adjoint mate `fᘁ`. -/
@[reassoc]
theorem leftAdjointMate_comp_leftDualIsoRightDual_hom {X Y : C} (f : X ⟶ Y) :
    (ᘁf) ≫ (leftDualIsoRightDual X).hom = (leftDualIsoRightDual Y).hom ≫ fᘁ := by
  refine @leftDualHom_ext C _ _ Xᘁ X (ᘁY) (pivotalExactPairing X) _ _ ?_
  rw [pivotalExactPairing_evaluation, MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerLeft_leftDualIsoRightDual_hom_comp_evaluation, leftAdjointMate_comp_evaluation,
    MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerLeft_rightAdjointMate_comp_pivotalIsoApp_hom_whiskerRight, whisker_exchange_assoc,
    whiskerLeft_leftDualIsoRightDual_hom_comp_evaluation]

/-- Naturality of the inverse of `leftDualIsoRightDual`: it intertwines the right adjoint mate
`fᘁ` with the left adjoint mate `ᘁf`. -/
@[reassoc]
theorem rightAdjointMate_comp_leftDualIsoRightDual_inv {X Y : C} (f : X ⟶ Y) :
    fᘁ ≫ (leftDualIsoRightDual X).inv = (leftDualIsoRightDual Y).inv ≫ (ᘁf) := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
    leftAdjointMate_comp_leftDualIsoRightDual_hom]

/-- The comparison at the unit: the inverse of `leftDualIsoRightDual (𝟙_ C)`, followed by the
identification of the left dual of `𝟙_ C` with `𝟙_ C`, is the identification of the right dual of
`𝟙_ C` with `𝟙_ C`. -/
theorem leftDualIsoRightDual_unit_inv :
    (leftDualIsoRightDual (𝟙_ C)).inv ≫
        (leftDualIso (LeftRigidCategory.leftDual (𝟙_ C)).exact exactPairingUnit).hom =
      (rightDualIso (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).hom := by
  rw [leftDualIsoRightDual_inv, leftDualIso_hom, ← comp_leftMate, Category.comp_id]
  -- Both sides are now maps out of `(𝟙_ C)ᘁ` into the left dual `𝟙_ C` of `𝟙_ C`; compare them
  -- after evaluation, where the pivotal component `φ_𝟙` is the unit comparison of the double dual.
  refine (@leftDualHom_ext C _ _ (𝟙_ C) (𝟙_ C) _ exactPairingUnit _ _ ?_).symm
  rw [leftMate_comp_evaluation, pivotalExactPairing_evaluation, pivotalIsoApp_unit_hom,
    doubleRightDualFunctor_ε]
  -- `φ_𝟙` is a composite of two right mates; evaluate them one after the other.
  simp only [comp_whiskerRight, Category.assoc, rightMate_comp_evaluation, rightDualIso_hom,
    rightDualIso_inv]
  rw [← whisker_exchange_assoc, rightMate_comp_evaluation]
  simp

/-- The comparison at a tensor product: `leftDualIsoRightDual (X ⊗ Y)` is the reversed tensor
product of the comparisons at `Y` and at `X`, up to the tensor comparisons of the left and right
duals. -/
theorem leftDualIsoRightDual_tensor_inv (X Y : C) :
    (leftDualIsoRightDual (X ⊗ Y)).inv ≫ (leftDualTensorIso X Y).hom =
      (rightDualTensorIso X Y).hom ≫
        ((leftDualIsoRightDual Y).inv ⊗ₘ (leftDualIsoRightDual X).inv) := by
  -- All four maps are left mates of identities between left duals of `X ⊗ Y`, and so are the
  -- two composites.
  rw [leftDualIsoRightDual_inv, leftDualIsoRightDual_inv, leftDualIsoRightDual_inv,
    leftDualTensorIso, leftDualIso_hom, rightDualTensorIso_hom_eq_leftMate,
    ← leftMate_tensorHom, ← comp_leftMate, ← comp_leftMate]
  simp only [tensorHom_id, id_whiskerRight, Category.comp_id]

variable (C) in
/-- In a pivotal category, the left and right dual functors `C ⥤ (Cᵒᵖ)ᴹᵒᵖ` are naturally
isomorphic. As both functors are contravariant, the component at `X` is the inverse
`Xᘁ ⟶ ᘁX` of `leftDualIsoRightDual X`, seen in `(Cᵒᵖ)ᴹᵒᵖ`. -/
noncomputable def dualFunctorIso : leftDualFunctor C ≅ rightDualFunctor C :=
  NatIso.ofComponents (fun X => (mopFunctor Cᵒᵖ).mapIso (leftDualIsoRightDual X).symm.op)
    fun {X Y} f => by
      -- Composition in `(Cᵒᵖ)ᴹᵒᵖ` is that of `C` in the reverse order, by definition, so after
      -- removing the wrappers the naturality square is definitionally the identity in `C`.
      apply Quiver.Hom.unmop_inj
      apply Quiver.Hom.unop_inj
      exact (rightAdjointMate_comp_leftDualIsoRightDual_inv f).symm

/-- The components of `dualFunctorIso C` are the inverses of `leftDualIsoRightDual`. -/
@[simp]
theorem dualFunctorIso_hom_app (X : C) :
    (dualFunctorIso C).hom.app X = (leftDualIsoRightDual X).inv.op.mop :=
  (rfl)

/-- The components of the inverse of `dualFunctorIso C` are the morphisms
`leftDualIsoRightDual`. -/
@[simp]
theorem dualFunctorIso_inv_app (X : C) :
    (dualFunctorIso C).inv.app X = (leftDualIsoRightDual X).hom.op.mop :=
  (rfl)

/-! As for `dualFunctorIso`, after `Quiver.Hom.unmop_inj` and `Quiver.Hom.unop_inj` the coherence
conditions below are definitionally the identities `leftDualIsoRightDual_unit_inv` and
`leftDualIsoRightDual_tensor_inv` in `C`, since composition and tensor products in `(Cᵒᵖ)ᴹᵒᵖ`
are those of `C` in the reverse order. -/

/-- The natural isomorphism between the left and right dual functors is monoidal. -/
instance dualFunctorIso_isMonoidal : NatTrans.IsMonoidal (dualFunctorIso C).hom where
  unit := by
    rw [leftDualFunctor_ε, rightDualFunctor_ε, dualFunctorIso_hom_app]
    apply Quiver.Hom.unmop_inj
    apply Quiver.Hom.unop_inj
    exact leftDualIsoRightDual_unit_inv (C := C)
  tensor X Y := by
    rw [leftDualFunctor_μ, rightDualFunctor_μ, dualFunctorIso_hom_app, dualFunctorIso_hom_app,
      dualFunctorIso_hom_app]
    apply Quiver.Hom.unmop_inj
    apply Quiver.Hom.unop_inj
    exact leftDualIsoRightDual_tensor_inv X Y

end Pivotal

section RightRigid

variable [RightRigidCategory C]

/-- For the pivotal structure built from a monoidal trivialization of the double right dual, the
left duals are the right duals, and `leftDualIsoRightDual` is the identity. -/
theorem leftDualIsoRightDual_pivotalCategoryOfRightRigid (φ : 𝟭 C ≅ doubleRightDualFunctor C)
    [NatTrans.IsMonoidal φ.hom] (X : C) :
    @leftDualIsoRightDual C _ _ (rigidCategoryOfIsoDoubleRightDual φ.app)
      (pivotalCategoryOfRightRigid φ) X = Iso.refl _ := by
  let := rigidCategoryOfIsoDoubleRightDual φ.app
  let := pivotalCategoryOfRightRigid φ
  rw [leftDualIsoRightDual, pivotalExactPairing_def,
    pivotalIsoApp_pivotalCategoryOfRightRigid]
  exact leftDualIso_id (C := C) _

end RightRigid

end TauCeti

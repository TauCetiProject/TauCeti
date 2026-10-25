/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import TauCeti.CategoryTheory.Monoidal.Rigid.DualFunctor

/-!
# Pivotal categories

A *pivotal structure* on a rigid monoidal category `C` is a monoidal natural isomorphism
`φ : 𝟭 C ≅ doubleRightDualFunctor C` from the identity functor to the double right dual functor
`X ↦ Xᘁᘁ`. Monoidality is Mathlib's `NatTrans.IsMonoidal`, taken with respect to the strong
monoidal structure on `doubleRightDualFunctor C`; a bare natural isomorphism to the double dual
is not a pivotal structure. A pivotal structure is what makes the left and right categorical
traces of an endomorphism, and the left and right dimensions of an object, definable.

Unwinding the definition, the components `φ_X : X ≅ Xᘁᘁ` are natural in `X`, so that the double
mate of a morphism is its conjugate by `φ`, and they are compatible with the unit and tensor
comparisons of the double right dual functor. The classical definition of Freyd and Yetter adds a
further axiom `φ_{Xᘁ} = (φ_X⁻¹)ᘁ`. This axiom is redundant: it follows from monoidality, because
the double right dual functor carries the evaluation of `(X, Xᘁ)` to the evaluation of
`(Xᘁᘁ, Xᘁᘁᘁ)`.

Through `φ_X`, the object `X` becomes a right dual of `Xᘁ`, so in a pivotal category every right
dual is also a left dual. The same observation shows that a pivotal structure needs only right
duals to make sense: in a right rigid category, a monoidal natural isomorphism
`𝟭 C ≅ doubleRightDualFunctor C` makes `Xᘁ` a left dual of `X`, and is then a pivotal structure
for the resulting rigid structure.

## Main declarations

* `TauCeti.PivotalCategory`: a pivotal structure on a rigid monoidal category, with fields
  `pivotalIso` and the instance `pivotalIso_isMonoidal`;
* `TauCeti.pivotalIsoApp`: the component `φ_X : X ≅ Xᘁᘁ`;
* `TauCeti.pivotalIsoApp_hom_naturality` and `TauCeti.rightAdjointMate_rightAdjointMate`: the
  double mate `fᘁᘁ` of `f : X ⟶ Y` is `φ_X⁻¹ ≫ f ≫ φ_Y`;
* `TauCeti.pivotalIsoApp_unit_hom`, `TauCeti.pivotalIsoApp_unit_inv` and
  `TauCeti.pivotalIsoApp_tensor_hom`: monoidality of `φ`, in components;
* `TauCeti.pivotalIsoApp_rightDual`: the Freyd–Yetter identity `φ_{Xᘁ} = (φ_X⁻¹)ᘁ`, with its
  inverse form `TauCeti.pivotalIsoApp_rightDual_inv`;
* `TauCeti.pivotalExactPairing`: the exact pairing `ExactPairing Xᘁ X` obtained from `φ_X`, whose
  evaluation is dinatural by
  `TauCeti.whiskerLeft_rightAdjointMate_comp_pivotalIsoApp_hom_whiskerRight`;
* `TauCeti.pivotalCategoryOfRightRigid`: a monoidal trivialization of the double right dual
  functor of a right rigid category is a pivotal structure for the rigid structure
  `TauCeti.rigidCategoryOfIsoDoubleRightDual`, whose left duals are the right duals.

## References

* [P. Freyd, D. Yetter, *Braided compact closed categories with applications to low-dimensional
  topology*][freydyetter1989]
* [P. Selinger, *A survey of graphical languages for monoidal categories*][selinger2011],
  Lemma 4.11, for the redundancy of the Freyd–Yetter axiom
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.7
* [leanprover-community/mathlib4#42150](https://github.com/leanprover-community/mathlib4/pull/42150),
  for the names `PivotalCategory`, `pivotalIso`, `pivotalExactPairing` and
  `rightAdjointMate_rightAdjointMate`
-/

public section

open CategoryTheory MonoidalCategory ExactPairing Functor.LaxMonoidal Functor.OplaxMonoidal

universe v u

namespace TauCeti

/-- A *pivotal structure* on a rigid monoidal category `C`: a monoidal natural isomorphism
`𝟭 C ≅ doubleRightDualFunctor C` from the identity functor to the double right dual functor. -/
@[ext]
class PivotalCategory (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C] where
  /-- The pivotal isomorphism, with components `X ≅ Xᘁᘁ`. -/
  pivotalIso : 𝟭 C ≅ doubleRightDualFunctor C
  /-- The pivotal isomorphism is a monoidal natural transformation. -/
  pivotalIso_isMonoidal : NatTrans.IsMonoidal pivotalIso.hom := by infer_instance

attribute [instance] PivotalCategory.pivotalIso_isMonoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

open PivotalCategory

section Pivotal

variable [RigidCategory C] [PivotalCategory C]

/-- The component `φ_X : X ≅ Xᘁᘁ` of the pivotal structure. -/
noncomputable def pivotalIsoApp (X : C) : X ≅ ((Xᘁ : C)ᘁ : C) :=
  pivotalIso.app X

/-- The components of the pivotal isomorphism are the morphisms `(pivotalIsoApp X).hom`. -/
@[simp]
theorem pivotalIso_hom_app (X : C) : (pivotalIso (C := C)).hom.app X = (pivotalIsoApp X).hom :=
  (rfl)

/-- The components of the inverse of the pivotal isomorphism are the morphisms
`(pivotalIsoApp X).inv`. -/
@[simp]
theorem pivotalIso_inv_app (X : C) : (pivotalIso (C := C)).inv.app X = (pivotalIsoApp X).inv :=
  (rfl)

/-- Naturality of the pivotal isomorphism. -/
@[reassoc]
theorem pivotalIsoApp_hom_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (pivotalIsoApp Y).hom = (pivotalIsoApp X).hom ≫ fᘁᘁ :=
  pivotalIso.hom.naturality f

/-- Naturality of the inverse of the pivotal isomorphism. -/
@[reassoc]
theorem pivotalIsoApp_inv_naturality {X Y : C} (f : X ⟶ Y) :
    fᘁᘁ ≫ (pivotalIsoApp Y).inv = (pivotalIsoApp X).inv ≫ f :=
  pivotalIso.inv.naturality f

/-- In a pivotal category, the double mate `fᘁᘁ` of `f : X ⟶ Y` is the conjugate
`φ_X⁻¹ ≫ f ≫ φ_Y` of `f` by the pivotal isomorphism. -/
theorem rightAdjointMate_rightAdjointMate {X Y : C} (f : X ⟶ Y) :
    fᘁᘁ = (pivotalIsoApp X).inv ≫ f ≫ (pivotalIsoApp Y).hom := by
  rw [pivotalIsoApp_hom_naturality, Iso.inv_hom_id_assoc]

/-- The component of the pivotal isomorphism at the unit is the unit comparison of the double
right dual functor. -/
theorem pivotalIsoApp_unit_hom :
    (pivotalIsoApp (𝟙_ C)).hom = ε (doubleRightDualFunctor C) :=
  -- The unit comparison of the identity functor is the identity.
  (Category.id_comp _).symm.trans (NatTrans.IsMonoidal.unit (τ := (pivotalIso (C := C)).hom))

/-- The inverse of the component of the pivotal isomorphism at the unit is the inverse unit
comparison of the double right dual functor. -/
theorem pivotalIsoApp_unit_inv :
    (pivotalIsoApp (𝟙_ C)).inv = η (doubleRightDualFunctor C) :=
  Iso.inv_ext ((congrArg (· ≫ η (doubleRightDualFunctor C)) pivotalIsoApp_unit_hom).trans
    (Functor.Monoidal.ε_η _))

/-- The component of the pivotal isomorphism at a tensor product is the tensor product of the
components, followed by the tensor comparison of the double right dual functor. -/
theorem pivotalIsoApp_tensor_hom (X Y : C) :
    (pivotalIsoApp (X ⊗ Y)).hom =
      ((pivotalIsoApp X).hom ⊗ₘ (pivotalIsoApp Y).hom) ≫ μ (doubleRightDualFunctor C) X Y :=
  -- The tensor comparison of the identity functor is the identity.
  (Category.id_comp _).symm.trans (NatTrans.IsMonoidal.tensor (τ := (pivotalIso (C := C)).hom) X Y)

/-- The tensor product of the components of the pivotal isomorphism at `Xᘁ` and at `X` carries the
evaluation of `(Xᘁᘁ, Xᘁᘁᘁ)` back to the evaluation of `(X, Xᘁ)`. -/
@[reassoc]
theorem pivotalIsoApp_tensorHom_comp_evaluation (X : C) :
    ((pivotalIsoApp Xᘁ).hom ⊗ₘ (pivotalIsoApp X).hom) ≫
      ε_ ((Xᘁ : C)ᘁ : C) (((Xᘁ : C)ᘁ : C)ᘁ : C) = ε_ X Xᘁ := by
  -- The statements below mix `Xᘁᘁ` with `(doubleRightDualFunctor C).obj X`, which agree only up
  -- to unfolding, so they are chained by `Eq.trans` rather than by rewriting.
  have h₁ : μ (doubleRightDualFunctor C) Xᘁ X ≫ (doubleRightDualFunctor C).map (ε_ X Xᘁ) =
      ε_ ((Xᘁ : C)ᘁ : C) (((Xᘁ : C)ᘁ : C)ᘁ : C) ≫ ε (doubleRightDualFunctor C) := by
    rw [doubleRightDualFunctor_map_evaluation, Functor.Monoidal.μ_δ_assoc]
    rfl
  rw [← cancel_mono (ε (doubleRightDualFunctor C)), Category.assoc]
  refine (congrArg (_ ≫ ·) h₁.symm).trans ((Category.assoc _ _ _).symm.trans ?_)
  refine (congrArg (· ≫ _) (pivotalIsoApp_tensor_hom Xᘁ X).symm).trans ?_
  exact (pivotalIsoApp_hom_naturality (ε_ X Xᘁ)).symm.trans
    (congrArg (_ ≫ ·) pivotalIsoApp_unit_hom)

/-- **The Freyd–Yetter identity**: the component of the pivotal isomorphism at `Xᘁ` is the mate
of the inverse of its component at `X`. -/
theorem pivotalIsoApp_rightDual (X : C) :
    (pivotalIsoApp Xᘁ).hom = ((pivotalIsoApp X).inv)ᘁ := by
  refine rightHom_ext (X := ((Xᘁ : C)ᘁ : C)) ?_
  rw [rightAdjointMate_comp_evaluation]
  -- Cancel the isomorphism `Xᘁ ◁ φ_X` on the left; on the right it cancels against `φ_X⁻¹`.
  rw [← cancel_epi (Xᘁ ◁ (pivotalIsoApp X).hom), whiskerLeft_hom_inv_assoc]
  -- The left side is the evaluation calculation `(φ_{Xᘁ} ⊗ φ_X) ≫ ε = ε`.
  rw [whisker_exchange_assoc, ← tensorHom_def_assoc]
  exact pivotalIsoApp_tensorHom_comp_evaluation X

/-- The inverse form of the Freyd–Yetter identity: the inverse of the component of the pivotal
isomorphism at `Xᘁ` is the mate of its component at `X`. -/
theorem pivotalIsoApp_rightDual_inv (X : C) :
    (pivotalIsoApp Xᘁ).inv = ((pivotalIsoApp X).hom)ᘁ :=
  Iso.inv_ext (by
    rw [pivotalIsoApp_rightDual, ← comp_rightAdjointMate, Iso.hom_inv_id, rightAdjointMate_id])

/-- In a pivotal category, `X` is a right dual of `Xᘁ`: the pairing of `Xᘁ` with its right dual
`Xᘁᘁ`, transported along `φ_X : X ≅ Xᘁᘁ`. -/
@[instance_reducible]
noncomputable def pivotalExactPairing (X : C) : ExactPairing Xᘁ X :=
  exactPairingCongrRight (pivotalIsoApp X)

/-- The pivotal pairing is the right transport of the chosen pairing along the pivotal
isomorphism. -/
theorem pivotalExactPairing_def (X : C) :
    pivotalExactPairing X = exactPairingCongrRight (pivotalIsoApp X) :=
  (rfl)

/-- The evaluation `X ⊗ Xᘁ ⟶ 𝟙_ C` of `pivotalExactPairing X`. -/
theorem pivotalExactPairing_evaluation (X : C) :
    @ExactPairing.evaluation C _ _ Xᘁ X (pivotalExactPairing X) =
      (pivotalIsoApp X).hom ▷ Xᘁ ≫ ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) :=
  exactPairingCongrRight_evaluation _

/-- The coevaluation `𝟙_ C ⟶ Xᘁ ⊗ X` of `pivotalExactPairing X`. -/
theorem pivotalExactPairing_coevaluation (X : C) :
    @ExactPairing.coevaluation C _ _ Xᘁ X (pivotalExactPairing X) =
      η_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) ≫ Xᘁ ◁ (pivotalIsoApp X).inv :=
  exactPairingCongrRight_coevaluation _

/-- The evaluation of the pivotal pairing is dinatural: for `f : X ⟶ Y`, pairing `X` with `Yᘁ`
through `fᘁ` or through `f` gives the same morphism. -/
@[reassoc]
theorem whiskerLeft_rightAdjointMate_comp_pivotalIsoApp_hom_whiskerRight {X Y : C} (f : X ⟶ Y) :
    X ◁ fᘁ ≫ (pivotalIsoApp X).hom ▷ Xᘁ ≫ ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) =
      f ▷ Yᘁ ≫ (pivotalIsoApp Y).hom ▷ Yᘁ ≫ ε_ (Yᘁ : C) ((Yᘁ : C)ᘁ : C) := by
  rw [whisker_exchange_assoc, ← rightAdjointMate_comp_evaluation, ← comp_whiskerRight_assoc,
    ← pivotalIsoApp_hom_naturality, comp_whiskerRight_assoc]

end Pivotal

section RightRigid

variable [RightRigidCategory C]

/-- A monoidal trivialization `φ : 𝟭 C ≅ doubleRightDualFunctor C` of the double right dual
functor of a right rigid category is a pivotal structure, for the rigid structure whose left
duals are the right duals, paired with `X` through `φ`. -/
@[instance_reducible]
noncomputable def pivotalCategoryOfRightRigid (φ : 𝟭 C ≅ doubleRightDualFunctor C)
    [NatTrans.IsMonoidal φ.hom] :
    @PivotalCategory C _ _ (rigidCategoryOfIsoDoubleRightDual φ.app) :=
  @PivotalCategory.mk C _ _ (rigidCategoryOfIsoDoubleRightDual φ.app) φ ‹_›

/-- The components of the pivotal structure built from a monoidal trivialization `φ` of the double
right dual are the components of `φ`. -/
theorem pivotalIsoApp_pivotalCategoryOfRightRigid (φ : 𝟭 C ≅ doubleRightDualFunctor C)
    [NatTrans.IsMonoidal φ.hom] (X : C) :
    @pivotalIsoApp C _ _ (rigidCategoryOfIsoDoubleRightDual φ.app)
      (pivotalCategoryOfRightRigid φ) X = φ.app X :=
  Iso.ext (@pivotalIso_hom_app C _ _ (rigidCategoryOfIsoDoubleRightDual φ.app)
    (pivotalCategoryOfRightRigid φ) X).symm

end RightRigid

end TauCeti

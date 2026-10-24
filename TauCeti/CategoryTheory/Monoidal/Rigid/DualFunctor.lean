/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Functor
public import TauCeti.CategoryTheory.Monoidal.Opposite
public import TauCeti.CategoryTheory.Monoidal.Rigid.Mate

/-!
# The right dual functor is a monoidal equivalence, and the double right dual functor

Mathlib's `CategoryTheory.rightDualFunctor C : C ⥤ (Cᵒᵖ)ᴹᵒᵖ` sends an object `X` of a right rigid
monoidal category to its right dual `Xᘁ` and a morphism `f` to its right adjoint mate `fᘁ`. Its
target is the monoidal opposite of the opposite category: the functor is contravariant, and it
reverses the order of tensor products, since `(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ` (Mathlib's
`CategoryTheory.rightDualTensorIso`).

This file makes `rightDualFunctor C` a strong monoidal functor. Its tensor comparison is
`rightDualTensorIso` and its unit comparison is the identification `(𝟙_ C)ᘁ ≅ 𝟙_ C` of the
right dual of the unit with the unit, through the self-pairing `exactPairingUnit`. The
coherence conditions are first proved in `C`, for arbitrary objects with right duals, as
identities between mates; there the comparisons are mates of identities and every coherence
morphism is a mate of a coherence morphism (`TauCeti.CategoryTheory.Monoidal.Rigid.Mate`).

In a rigid monoidal category, the right dual functor is also an equivalence of categories. Full
faithfulness follows because taking a left adjoint mate undoes taking a right adjoint mate, while
essential surjectivity follows because every object is the right dual of its left dual. Together
with the strong monoidal structure, this makes the right dual functor a monoidal equivalence.

Applying the right dual functor twice gives the double right dual functor `C ⥤ C`, sending `X`
to `Xᘁᘁ` and `f` to `fᘁᘁ`. Its second application goes through the opposite monoidal opposite
of the right dual functor (`CategoryTheory.Functor.op` followed by
`CategoryTheory.Functor.opMop`), so the double right dual functor is a composite of strong
monoidal functors and inherits a strong monoidal structure. This monoidal structure is what makes
a monoidal natural isomorphism from the identity functor to the double right dual functor, a
pivotal structure, expressible with Mathlib's `NatTrans.IsMonoidal`. In a rigid monoidal category
the double right dual functor is a monoidal autoequivalence.

## Main declarations

* `TauCeti.rightDualTensorIso_hom_naturality`: naturality of `rightDualTensorIso`;
* `TauCeti.rightDualTensorIso_associativity`, `TauCeti.rightDualTensorIso_leftUnitality` and
  `TauCeti.rightDualTensorIso_rightUnitality`: its compatibility with the associator and the
  unitors;
* `TauCeti.rightDualTensorIso_hom_whiskerRight_evaluation`,
  `TauCeti.rightDualTensorIso_inv_whiskerRight_evaluation` and
  `TauCeti.coevaluation_comp_whiskerLeft_rightDualTensorIso_hom`: it carries the evaluation and
  coevaluation of `(X ⊗ Y, (X ⊗ Y)ᘁ)` to those of the tensor product pairing;
* `TauCeti.rightDualFunctorCoreMonoidal` and the instance `TauCeti.rightDualFunctorMonoidal`: the
  strong monoidal structure on `rightDualFunctor C`, with structure morphisms given by
  `TauCeti.rightDualFunctor_ε`, `TauCeti.rightDualFunctor_η`, `TauCeti.rightDualFunctor_μ` and
  `TauCeti.rightDualFunctor_δ`;
* `TauCeti.rightDualFunctorFullyFaithful`: the explicit full-faithfulness structure whose preimage
  operation takes left adjoint mates;
* `TauCeti.rightDualFunctorIsEquivalence`: right duality is an equivalence; together with its
  `Functor.Monoidal` instance, it is a monoidal equivalence;
* `TauCeti.doubleRightDualFunctor` and the instance `TauCeti.doubleRightDualFunctorMonoidal`: the
  strong monoidal double right dual functor, with structure morphisms given by
  `TauCeti.doubleRightDualFunctor_ε`, `TauCeti.doubleRightDualFunctor_η`,
  `TauCeti.doubleRightDualFunctor_μ` and `TauCeti.doubleRightDualFunctor_δ`;
* `TauCeti.doubleRightDualFunctor_map_evaluation` and
  `TauCeti.doubleRightDualFunctor_map_coevaluation`: the double right dual functor carries the
  evaluation and coevaluation of `(X, Xᘁ)` to those of `(Xᘁᘁ, Xᘁᘁᘁ)`;
* `TauCeti.rigidCategoryOfIsoDoubleRightDual`: a right rigid category with isomorphisms
  `X ≅ Xᘁᘁ` is rigid, with left duals described by
  `TauCeti.rigidCategoryOfIsoDoubleRightDual_evaluation` and
  `TauCeti.rigidCategoryOfIsoDoubleRightDual_coevaluation`;
* `TauCeti.doubleRightDualFunctorIsEquivalence`: in a rigid monoidal category, the double right
  dual functor is an equivalence, hence a monoidal autoequivalence.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §2.10
-/

public section

open CategoryTheory MonoidalCategory MonoidalOpposite Opposite ExactPairing

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The comparison `(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ` is natural in `X` and `Y`. -/
@[reassoc]
theorem rightDualTensorIso_hom_naturality {X X' Y Y' : C} [HasRightDual X] [HasRightDual X']
    [HasRightDual Y] [HasRightDual Y'] [HasRightDual (X ⊗ Y)] [HasRightDual (X' ⊗ Y')]
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g)ᘁ ≫ (rightDualTensorIso X Y).hom = (rightDualTensorIso X' Y').hom ≫ (gᘁ ⊗ₘ fᘁ) := by
  simp only [rightDualTensorIso, rightDualIso_hom, rightAdjointMate_eq_rightMate,
    ← rightMate_tensorHom, ← comp_rightMate, Category.id_comp, Category.comp_id]

/-- The comparison `(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ` is compatible with the associators: the two ways of
identifying `(X ⊗ Y ⊗ Z)ᘁ` with `Zᘁ ⊗ Yᘁ ⊗ Xᘁ` agree. -/
@[reassoc]
theorem rightDualTensorIso_associativity (X Y Z : C) [HasRightDual X] [HasRightDual Y]
    [HasRightDual Z] [HasRightDual (X ⊗ Y)] [HasRightDual (Y ⊗ Z)] [HasRightDual ((X ⊗ Y) ⊗ Z)]
    [HasRightDual (X ⊗ Y ⊗ Z)] :
    ((α_ X Y Z).hom)ᘁ ≫ (rightDualTensorIso (X ⊗ Y) Z).hom ≫ Zᘁ ◁ (rightDualTensorIso X Y).hom =
      (rightDualTensorIso X (Y ⊗ Z)).hom ≫ (rightDualTensorIso Y Z).hom ▷ Xᘁ ≫
        (α_ Zᘁ Yᘁ Xᘁ).hom := by
  simp only [rightDualTensorIso, rightDualIso_hom, rightAdjointMate_eq_rightMate]
  rw [← rightMate_whiskerRight _ _ (HasRightDual.exact (X := Z)),
    ← rightMate_whiskerLeft _ _ (HasRightDual.exact (X := X)),
    ← rightMate_associator_hom (HasRightDual.exact (X := X)) (HasRightDual.exact (X := Y))
      (HasRightDual.exact (X := Z)),
    ← comp_rightMate, ← comp_rightMate, ← comp_rightMate, ← comp_rightMate]
  simp

/-- The mate `Xᘁ ⟶ (𝟙_ C ⊗ X)ᘁ` of the left unitor of `X`, followed by the comparison
`(𝟙_ C ⊗ X)ᘁ ≅ Xᘁ ⊗ (𝟙_ C)ᘁ` and the identification of `(𝟙_ C)ᘁ` with `𝟙_ C`, is the inverse
right unitor `Xᘁ ⟶ Xᘁ ⊗ 𝟙_ C` of `Xᘁ`. -/
theorem rightDualTensorIso_leftUnitality (X : C) [HasRightDual X] [HasRightDual (𝟙_ C)]
    [HasRightDual (𝟙_ C ⊗ X)] :
    (ρ_ Xᘁ).inv = ((λ_ X).hom)ᘁ ≫ (rightDualTensorIso (𝟙_ C) X).hom ≫
      Xᘁ ◁ (rightDualIso HasRightDual.exact exactPairingUnit).hom := by
  simp only [rightDualTensorIso, rightDualIso_hom, rightAdjointMate_eq_rightMate]
  rw [← rightMate_whiskerRight _ _ (HasRightDual.exact (X := X)),
    ← rightMate_leftUnitor_hom (HasRightDual.exact (X := X)), ← comp_rightMate, ← comp_rightMate]
  simp

/-- The mate `Xᘁ ⟶ (X ⊗ 𝟙_ C)ᘁ` of the right unitor of `X`, followed by the comparison
`(X ⊗ 𝟙_ C)ᘁ ≅ (𝟙_ C)ᘁ ⊗ Xᘁ` and the identification of `(𝟙_ C)ᘁ` with `𝟙_ C`, is the inverse
left unitor `Xᘁ ⟶ 𝟙_ C ⊗ Xᘁ` of `Xᘁ`. -/
theorem rightDualTensorIso_rightUnitality (X : C) [HasRightDual X] [HasRightDual (𝟙_ C)]
    [HasRightDual (X ⊗ 𝟙_ C)] :
    (λ_ Xᘁ).inv = ((ρ_ X).hom)ᘁ ≫ (rightDualTensorIso X (𝟙_ C)).hom ≫
      (rightDualIso HasRightDual.exact exactPairingUnit).hom ▷ Xᘁ := by
  simp only [rightDualTensorIso, rightDualIso_hom, rightAdjointMate_eq_rightMate]
  rw [← rightMate_whiskerLeft _ _ (HasRightDual.exact (X := X)),
    ← rightMate_rightUnitor_hom (HasRightDual.exact (X := X)), ← comp_rightMate, ← comp_rightMate]
  simp

section Evaluation

variable (X Y : C) [HasRightDual X] [HasRightDual Y] [HasRightDual (X ⊗ Y)]

/-- Through the comparison `(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ`, the evaluation of the tensor product pairing
of `(X, Xᘁ)` and `(Y, Yᘁ)` is the evaluation of `(X ⊗ Y, (X ⊗ Y)ᘁ)`. -/
@[reassoc]
theorem rightDualTensorIso_hom_whiskerRight_evaluation :
    (rightDualTensorIso X Y).hom ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ) = ε_ (X ⊗ Y) (X ⊗ Y)ᘁ := by
  rw [rightDualTensorIso, rightDualIso_hom_whiskerRight_evaluation]

/-- Through the comparison `(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ`, the evaluation of `(X ⊗ Y, (X ⊗ Y)ᘁ)` is the
evaluation of the tensor product pairing of `(X, Xᘁ)` and `(Y, Yᘁ)`. -/
@[reassoc]
theorem rightDualTensorIso_inv_whiskerRight_evaluation :
    (rightDualTensorIso X Y).inv ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) (X ⊗ Y)ᘁ = ε_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ) := by
  rw [← rightDualTensorIso_hom_whiskerRight_evaluation, ← comp_whiskerRight_assoc,
    Iso.inv_hom_id, id_whiskerRight, Category.id_comp]

/-- Through the comparison `(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ`, the coevaluation of `(X ⊗ Y, (X ⊗ Y)ᘁ)` is the
coevaluation of the tensor product pairing of `(X, Xᘁ)` and `(Y, Yᘁ)`. -/
@[reassoc]
theorem coevaluation_comp_whiskerLeft_rightDualTensorIso_hom :
    η_ (X ⊗ Y) (X ⊗ Y)ᘁ ≫ (X ⊗ Y) ◁ (rightDualTensorIso X Y).hom = η_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ) := by
  rw [rightDualTensorIso, rightDualIso_hom, coevaluation_comp_rightMate, id_whiskerRight,
    Category.comp_id]

end Evaluation

variable (C) [RightRigidCategory C]

/-! In `(Cᵒᵖ)ᴹᵒᵖ`, composition and tensor products are those of `C` in the reverse order, by
definition. So after `Quiver.Hom.unmop_inj` and `Quiver.Hom.unop_inj`, each coherence condition
for `rightDualFunctor C` is definitionally the corresponding identity in `C` proved above, up to
reassociating the composites. -/

/-- The right dual functor `C ⥤ (Cᵒᵖ)ᴹᵒᵖ` of a right rigid monoidal category is strong
monoidal: the tensor comparison is `rightDualTensorIso` and the unit comparison identifies the
right dual of the unit with the unit. -/
noncomputable def rightDualFunctorCoreMonoidal : (rightDualFunctor C).CoreMonoidal where
  εIso := (mopFunctor _).mapIso
    (rightDualIso (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).op
  μIso X Y := (mopFunctor _).mapIso (rightDualTensorIso X Y).op
  μIso_hom_natural_left f X' := by
    apply Quiver.Hom.unmop_inj
    apply Quiver.Hom.unop_inj
    have h : (rightDualTensorIso _ X').hom ≫ (X'ᘁ : C) ◁ fᘁ =
        (f ▷ X')ᘁ ≫ (rightDualTensorIso _ X').hom := by
      simpa using (rightDualTensorIso_hom_naturality f (𝟙 X')).symm
    exact h
  μIso_hom_natural_right X' f := by
    apply Quiver.Hom.unmop_inj
    apply Quiver.Hom.unop_inj
    have h : (rightDualTensorIso X' _).hom ≫ fᘁ ▷ (X'ᘁ : C) =
        (X' ◁ f)ᘁ ≫ (rightDualTensorIso X' _).hom := by
      simpa using (rightDualTensorIso_hom_naturality (𝟙 X') f).symm
    exact h
  associativity X Y Z := by
    apply Quiver.Hom.unmop_inj
    apply Quiver.Hom.unop_inj
    exact (Category.assoc _ _ _).trans
      ((rightDualTensorIso_associativity X Y Z).trans (Category.assoc _ _ _).symm)
  left_unitality X := by
    apply Quiver.Hom.unmop_inj
    apply Quiver.Hom.unop_inj
    -- The unit comparison uses the rigid structure's right dual of `𝟙_ C`, not `hasRightDualUnit`.
    exact (@rightDualTensorIso_leftUnitality C _ _ X _ (RightRigidCategory.rightDual _) _).trans
      (Category.assoc _ _ _).symm
  right_unitality X := by
    apply Quiver.Hom.unmop_inj
    apply Quiver.Hom.unop_inj
    -- The unit comparison uses the rigid structure's right dual of `𝟙_ C`, not `hasRightDualUnit`.
    exact (@rightDualTensorIso_rightUnitality C _ _ X _ (RightRigidCategory.rightDual _) _).trans
      (Category.assoc _ _ _).symm

/-- The right dual functor of a right rigid monoidal category is strong monoidal. -/
noncomputable instance rightDualFunctorMonoidal : (rightDualFunctor C).Monoidal :=
  (rightDualFunctorCoreMonoidal C).toMonoidal

open Functor.LaxMonoidal Functor.OplaxMonoidal

/-- The unit comparison of the right dual functor is the identification of the right dual of the
unit with the unit. -/
@[simp]
theorem rightDualFunctor_ε :
    ε (rightDualFunctor C) =
      (rightDualIso (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).hom.op.mop :=
  (rfl)

/-- The inverse unit comparison of the right dual functor. -/
@[simp]
theorem rightDualFunctor_η :
    η (rightDualFunctor C) =
      (rightDualIso (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).inv.op.mop :=
  (rfl)

/-- The tensor comparison of the right dual functor is `rightDualTensorIso`. -/
@[simp]
theorem rightDualFunctor_μ (X Y : C) :
    μ (rightDualFunctor C) X Y = (rightDualTensorIso X Y).hom.op.mop :=
  (rfl)

/-- The inverse tensor comparison of the right dual functor. -/
@[simp]
theorem rightDualFunctor_δ (X Y : C) :
    δ (rightDualFunctor C) X Y = (rightDualTensorIso X Y).inv.op.mop :=
  (rfl)

end TauCeti

namespace TauCeti

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

section RightRigid

variable [RightRigidCategory C]

/-- The right dual functor is fully faithful. Its inverse on each hom-set takes left adjoint
mates. -/
def rightDualFunctorFullyFaithful : (rightDualFunctor C).FullyFaithful where
  preimage {X Y} f := by
    -- Expose the object formula through the two opposite-category wrappers so the left mate has
    -- the original objects `X` and `Y` as its endpoints.
    change mop (op Xᘁ) ⟶ mop (op Yᘁ) at f
    exact leftAdjointMate f.unmop.unop
  map_preimage {X Y} f := by
    -- Expose both the object and morphism formulas before cancelling the wrapper constructors.
    change mop (op Xᘁ) ⟶ mop (op Yᘁ) at f
    simp only [rightDualFunctor_map]
    apply Quiver.Hom.unmop_inj
    apply Quiver.Hom.unop_inj
    exact rightAdjointMate_leftAdjointMate f.unmop.unop
  preimage_map f := leftAdjointMate_rightAdjointMate f

/-- The preimage operation for the full faithfulness of the right dual functor takes left adjoint
mates. -/
@[simp]
theorem rightDualFunctorFullyFaithful_preimage {X Y : C}
    (f : mop (op Xᘁ) ⟶ mop (op Yᘁ)) :
    (rightDualFunctorFullyFaithful C).preimage f = leftAdjointMate f.unmop.unop := by
  rfl

/-- The right dual functor of a right rigid monoidal category is faithful. -/
instance rightDualFunctorFaithful : (rightDualFunctor C).Faithful :=
  (rightDualFunctorFullyFaithful C).faithful

/-- The right dual functor of a right rigid monoidal category is full. -/
instance rightDualFunctorFull : (rightDualFunctor C).Full :=
  (rightDualFunctorFullyFaithful C).full

end RightRigid

section Rigid

variable [RigidCategory C]

/-- The right dual functor of a rigid monoidal category is an equivalence of categories. -/
instance rightDualFunctorIsEquivalence : (rightDualFunctor C).IsEquivalence where
  essSurj :=
    { mem_essImage := fun X =>
        ⟨ᘁ(X.unmop.unop),
          ⟨(mopFunctor (Cᵒᵖ)).mapIso
            (rightDualIso (RightRigidCategory.rightDual (ᘁ(X.unmop.unop))).exact
              (LeftRigidCategory.leftDual (X.unmop.unop)).exact).symm.op⟩⟩ }

end Rigid

end TauCeti

namespace TauCeti

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

section DoubleRightDual

variable [RightRigidCategory C]

-- The name and the assembly through `Functor.opMop` follow
-- https://github.com/leanprover-community/mathlib4/pull/42145.
/-- The double right dual functor `C ⥤ C` of a right rigid monoidal category, sending `X` to
`Xᘁᘁ` and `f` to `fᘁᘁ`. It applies the right dual functor `C ⥤ (Cᵒᵖ)ᴹᵒᵖ` twice, the second
time through its opposite monoidal opposite, and returns to `C` by removing the wrappers. -/
@[expose]
noncomputable def doubleRightDualFunctor : C ⥤ C :=
  rightDualFunctor C ⋙ (rightDualFunctor C).op.opMop ⋙ (opMopOpMopEquivalence C).functor

/-- The double right dual functor is strong monoidal, as the composite of the strong monoidal
right dual functor, its opposite monoidal opposite, and the removal of the wrappers. -/
noncomputable instance doubleRightDualFunctorMonoidal : (doubleRightDualFunctor C).Monoidal :=
  inferInstanceAs
    (rightDualFunctor C ⋙ (rightDualFunctor C).op.opMop ⋙
      (opMopOpMopEquivalence C).functor).Monoidal

variable {C}

/-- The double right dual functor sends `X` to `Xᘁᘁ`. -/
@[simp]
theorem doubleRightDualFunctor_obj (X : C) :
    (doubleRightDualFunctor C).obj X = ((Xᘁ : C)ᘁ : C) :=
  (rfl)

/-- The double right dual functor sends `f` to `fᘁᘁ`. -/
@[simp]
theorem doubleRightDualFunctor_map {X Y : C} (f : X ⟶ Y) :
    (doubleRightDualFunctor C).map f = fᘁᘁ :=
  (rfl)

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable (C)

/-! The structure morphisms of a composite of monoidal functors are composites of the structure
morphisms of its factors (`Functor.LaxMonoidal.comp_μ` and its relatives). Those of the right dual
functor and of its opposite monoidal opposite are, after removing the wrappers, the morphisms of
`C` displayed below, while those of the removal of the wrappers are identities. -/

/-- The unit comparison `𝟙_ C ⟶ (𝟙_ C)ᘁᘁ` of the double right dual functor: identify `𝟙_ C` with
`(𝟙_ C)ᘁ`, then take the mate of the identification of `(𝟙_ C)ᘁ` with `𝟙_ C`. The pairings are
explicit because `(𝟙_ C)ᘁ` is the dual chosen by the rigid structure, which need not be Mathlib's
`hasRightDualUnit`. -/
theorem doubleRightDualFunctor_ε :
    ε (doubleRightDualFunctor C) =
      (rightDualIso (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).inv ≫
        rightMate HasRightDual.exact (RightRigidCategory.rightDual (𝟙_ C)).exact
          (rightDualIso (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).hom :=
  (Category.id_comp _ =≫ _).trans
    (_ ≫= @rightAdjointMate_eq_rightMate C _ _ _ _ _ (RightRigidCategory.rightDual (𝟙_ C)) _)

/-- The inverse unit comparison `(𝟙_ C)ᘁᘁ ⟶ 𝟙_ C` of the double right dual functor. -/
theorem doubleRightDualFunctor_η :
    η (doubleRightDualFunctor C) =
      rightMate (RightRigidCategory.rightDual (𝟙_ C)).exact HasRightDual.exact
          (rightDualIso (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).inv ≫
        (rightDualIso (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).hom :=
  (_ ≫= Category.comp_id _).trans
    (@rightAdjointMate_eq_rightMate C _ _ _ _ (RightRigidCategory.rightDual (𝟙_ C)) _ _ =≫ _)

/-- The tensor comparison `Xᘁᘁ ⊗ Yᘁᘁ ⟶ (X ⊗ Y)ᘁᘁ` of the double right dual functor: identify
`Xᘁᘁ ⊗ Yᘁᘁ` with `(Yᘁ ⊗ Xᘁ)ᘁ`, then take the mate of the comparison `(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ`. -/
theorem doubleRightDualFunctor_μ (X Y : C) :
    μ (doubleRightDualFunctor C) X Y =
      (rightDualTensorIso Yᘁ Xᘁ).inv ≫ ((rightDualTensorIso X Y).hom)ᘁ :=
  (Functor.LaxMonoidal.comp_μ _ _ X Y).trans
    ((Functor.LaxMonoidal.comp_μ _ _ _ _ =≫ _).trans (Category.id_comp _ =≫ _))

/-- The inverse tensor comparison `(X ⊗ Y)ᘁᘁ ⟶ Xᘁᘁ ⊗ Yᘁᘁ` of the double right dual functor. -/
theorem doubleRightDualFunctor_δ (X Y : C) :
    δ (doubleRightDualFunctor C) X Y =
      ((rightDualTensorIso X Y).inv)ᘁ ≫ (rightDualTensorIso Yᘁ Xᘁ).hom :=
  (Functor.OplaxMonoidal.comp_δ _ _ X Y).trans
    (_ ≫= (Functor.OplaxMonoidal.comp_δ _ _ _ _).trans (Category.comp_id _))

variable {C}

/-- The double right dual functor carries the evaluation of `(X, Xᘁ)` to the evaluation of
`(Xᘁᘁ, Xᘁᘁᘁ)`, up to its tensor and unit comparisons. -/
theorem doubleRightDualFunctor_map_evaluation (X : C) :
    (doubleRightDualFunctor C).map (ε_ X Xᘁ) =
      δ (doubleRightDualFunctor C) Xᘁ X ≫ ε_ ((Xᘁ : C)ᘁ : C) (((Xᘁ : C)ᘁ : C)ᘁ : C) ≫
        ε (doubleRightDualFunctor C) := by
  -- The same identity with the structure maps unfolded and the objects written as iterated duals
  -- rather than through the functor, so that the mates below compose. The dual of `𝟙_ C` must be
  -- the one chosen by the rigid structure.
  have key : ((rightDualTensorIso Xᘁ Xᘁᘁ).inv ≫ ((rightDualTensorIso Xᘁ X).hom)ᘁ) ≫
      (@rightAdjointMate C _ _ _ _ _ (RightRigidCategory.rightDual (𝟙_ C)) (ε_ X Xᘁ))ᘁ ≫
        rightMate (RightRigidCategory.rightDual (𝟙_ C)).exact HasRightDual.exact
          (rightDualIso (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).inv ≫
        (rightDualIso (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).hom =
      ε_ ((Xᘁ : C)ᘁ : C) (((Xᘁ : C)ᘁ : C)ᘁ : C) := by
    simp only [rightDualTensorIso, rightDualIso_hom, rightDualIso_inv,
      rightAdjointMate_eq_rightMate, ← comp_rightMate, Category.id_comp, Category.comp_id,
      rightMate_evaluation, rightMate_coevaluation]
  have h : μ (doubleRightDualFunctor C) Xᘁ X ≫ (doubleRightDualFunctor C).map (ε_ X Xᘁ) ≫
      η (doubleRightDualFunctor C) = ε_ ((Xᘁ : C)ᘁ : C) (((Xᘁ : C)ᘁ : C)ᘁ : C) := by
    rw [doubleRightDualFunctor_μ, doubleRightDualFunctor_η, doubleRightDualFunctor_map]
    exact key
  calc
    _ = δ (doubleRightDualFunctor C) Xᘁ X ≫ (μ (doubleRightDualFunctor C) Xᘁ X ≫
          (doubleRightDualFunctor C).map (ε_ X Xᘁ) ≫ η (doubleRightDualFunctor C)) ≫
        ε (doubleRightDualFunctor C) := by
      simp only [Category.assoc, Functor.Monoidal.δ_μ_assoc, Functor.Monoidal.η_ε,
        Category.comp_id]
    _ = _ := by rw [h]

/-- The double right dual functor carries the coevaluation of `(X, Xᘁ)` to the coevaluation of
`(Xᘁᘁ, Xᘁᘁᘁ)`, up to its unit and tensor comparisons. -/
theorem doubleRightDualFunctor_map_coevaluation (X : C) :
    (doubleRightDualFunctor C).map (η_ X Xᘁ) =
      η (doubleRightDualFunctor C) ≫ η_ ((Xᘁ : C)ᘁ : C) (((Xᘁ : C)ᘁ : C)ᘁ : C) ≫
        μ (doubleRightDualFunctor C) X Xᘁ := by
  -- As in `doubleRightDualFunctor_map_evaluation`, the dual of `𝟙_ C` must be the one chosen by
  -- the rigid structure.
  have key : ((rightDualIso (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).inv ≫
        rightMate HasRightDual.exact (RightRigidCategory.rightDual (𝟙_ C)).exact
          (rightDualIso (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).hom) ≫
      (@rightAdjointMate C _ _ _ _ (RightRigidCategory.rightDual (𝟙_ C)) _ (η_ X Xᘁ))ᘁ ≫
        ((rightDualTensorIso X Xᘁ).inv)ᘁ ≫ (rightDualTensorIso Xᘁᘁ Xᘁ).hom =
      η_ ((Xᘁ : C)ᘁ : C) (((Xᘁ : C)ᘁ : C)ᘁ : C) := by
    simp only [rightDualTensorIso, rightDualIso_hom, rightDualIso_inv,
      rightAdjointMate_eq_rightMate, ← comp_rightMate, Category.id_comp, Category.comp_id,
      rightMate_evaluation, rightMate_coevaluation]
  have h : ε (doubleRightDualFunctor C) ≫ (doubleRightDualFunctor C).map (η_ X Xᘁ) ≫
      δ (doubleRightDualFunctor C) X Xᘁ = η_ ((Xᘁ : C)ᘁ : C) (((Xᘁ : C)ᘁ : C)ᘁ : C) := by
    rw [doubleRightDualFunctor_ε, doubleRightDualFunctor_δ, doubleRightDualFunctor_map]
    exact key
  calc
    _ = η (doubleRightDualFunctor C) ≫ (ε (doubleRightDualFunctor C) ≫
          (doubleRightDualFunctor C).map (η_ X Xᘁ) ≫ δ (doubleRightDualFunctor C) X Xᘁ) ≫
        μ (doubleRightDualFunctor C) X Xᘁ := by
      simp only [Category.assoc, Functor.Monoidal.η_ε_assoc, Functor.Monoidal.δ_μ,
        Category.comp_id]
    _ = _ := by
      rw [h]
      -- The two sides differ only in how the intermediate objects are written.
      rfl

/-- A right rigid category in which every object `X` is isomorphic to its double right dual
`(doubleRightDualFunctor C).obj X = Xᘁᘁ` is rigid: transporting the pairing of `Xᘁ` with `Xᘁᘁ`
along the isomorphism makes `Xᘁ` a left dual of `X`. Not an instance, as the left duals depend on
the chosen isomorphisms. -/
@[expose, instance_reducible]
noncomputable def rigidCategoryOfIsoDoubleRightDual
    (φ : ∀ X : C, X ≅ (doubleRightDualFunctor C).obj X) : RigidCategory C where
  toRightRigidCategory := ‹_›
  leftDual X :=
    { leftDual := Xᘁ
      exact := @exactPairingCongrRight C _ _ Xᘁ X ((Xᘁ : C)ᘁ : C) HasRightDual.exact (φ X) }

/-- The evaluation `X ⊗ Xᘁ ⟶ 𝟙_ C` of the left dual of `X` in
`rigidCategoryOfIsoDoubleRightDual φ`: the evaluation of `(Xᘁ, Xᘁᘁ)` precomposed with `φ X`. -/
@[simp, reassoc]
theorem rigidCategoryOfIsoDoubleRightDual_evaluation
    (φ : ∀ X : C, X ≅ (doubleRightDualFunctor C).obj X) (X : C) :
    letI := rigidCategoryOfIsoDoubleRightDual φ
    ε_ (ᘁX) X = (φ X).hom ▷ Xᘁ ≫ ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) :=
  exactPairingCongrRight_evaluation _

/-- The coevaluation `𝟙_ C ⟶ Xᘁ ⊗ X` of the left dual of `X` in
`rigidCategoryOfIsoDoubleRightDual φ`: the coevaluation of `(Xᘁ, Xᘁᘁ)` followed by the inverse
of `φ X`. -/
@[simp, reassoc]
theorem rigidCategoryOfIsoDoubleRightDual_coevaluation
    (φ : ∀ X : C, X ≅ (doubleRightDualFunctor C).obj X) (X : C) :
    letI := rigidCategoryOfIsoDoubleRightDual φ
    η_ (ᘁX) X = η_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) ≫ Xᘁ ◁ (φ X).inv :=
  exactPairingCongrRight_coevaluation _

end DoubleRightDual

/-- The double right dual functor of a rigid monoidal category is an equivalence of categories;
with its `Functor.Monoidal` instance, it is a monoidal autoequivalence. -/
instance doubleRightDualFunctorIsEquivalence [RigidCategory C] :
    (doubleRightDualFunctor C).IsEquivalence :=
  inferInstanceAs
    (rightDualFunctor C ⋙ (rightDualFunctor C).op.opMop ⋙
      (opMopOpMopEquivalence C).functor).IsEquivalence

end TauCeti

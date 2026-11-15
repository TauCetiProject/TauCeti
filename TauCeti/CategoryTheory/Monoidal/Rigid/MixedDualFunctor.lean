/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import TauCeti.CategoryTheory.Monoidal.Rigid.DualFunctor
public import TauCeti.CategoryTheory.Monoidal.Rigid.LeftDualFunctor

/-!
# The mixed double duals are trivial

In a rigid monoidal category `C`, composing the right dual functor with the left dual functor, in
either order, gives a strong monoidal endofunctor of `C`:

* `leftDualRightDualFunctor C`, sending `X` to the left dual `ᘁ(Xᘁ)` of its right dual, and
  `f` to `ᘁ(fᘁ)`;
* `rightDualLeftDualFunctor C`, sending `X` to the right dual `(ᘁX)ᘁ` of its left dual, and
  `f` to `(ᘁf)ᘁ`.

Both are assembled like the double right dual functor: the second dual functor is applied through
its opposite monoidal opposite, and the result is returned to `C` by removing the wrappers. The
duals involved are the ones chosen by the rigid structure.

Since `X` is a left dual of `Xᘁ` and a right dual of `ᘁX`, comparing it with the chosen duals
gives isomorphisms `ᘁ(Xᘁ) ≅ X` and `(ᘁX)ᘁ ≅ X`. These are natural in `X` and compatible with the
unit and tensor comparisons, so both mixed composites are trivialized by monoidal natural
isomorphisms

```text
leftDualRightDualFunctor C ≅ 𝟭 C,      rightDualLeftDualFunctor C ≅ 𝟭 C.
```

These are the functorial and monoidal forms of Mathlib's object-level identities
`CategoryTheory.leftDual_rightDual : ᘁXᘁ = X` and `CategoryTheory.rightDual_leftDual : (ᘁX)ᘁ = X`,
which hold for the duals `CategoryTheory.hasLeftDualRightDual` and
`CategoryTheory.hasRightDualLeftDual` rather than for the duals chosen by a rigid structure. They
contrast with the double right dual functor `X ↦ Xᘁᘁ`, which need not be isomorphic to the identity:
a trivialization of the double right dual is the extra datum of a pivotal structure.

## Main declarations

* `TauCeti.leftDualRightDualFunctor` and its strong monoidal structure
  `TauCeti.leftDualRightDualFunctorMonoidal`, with structure morphisms
  `TauCeti.leftDualRightDualFunctor_ε` and `TauCeti.leftDualRightDualFunctor_μ` written as left
  mates;
* `TauCeti.leftDualRightDualIso`: the natural isomorphism `ᘁ(Xᘁ) ≅ X`, monoidal by
  `TauCeti.leftDualRightDualIso_isMonoidal`;
* `TauCeti.rightDualLeftDualFunctor` and its strong monoidal structure
  `TauCeti.rightDualLeftDualFunctorMonoidal`, with structure morphisms
  `TauCeti.rightDualLeftDualFunctor_ε` and `TauCeti.rightDualLeftDualFunctor_μ` written as
  right mates;
* `TauCeti.rightDualLeftDualIso`: the natural isomorphism `(ᘁX)ᘁ ≅ X`, monoidal by
  `TauCeti.rightDualLeftDualIso_isMonoidal`.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §2.10
* [leanprover-community/mathlib4#42145](https://github.com/leanprover-community/mathlib4/pull/42145),
  for the assembly of the double right dual functor through `Functor.opMop`, which both mixed
  composites adapt
-/

public section

open CategoryTheory MonoidalCategory MonoidalOpposite Opposite ExactPairing
open Functor.LaxMonoidal Functor.OplaxMonoidal

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-! Throughout, the duals of `Xᘁ` and of `ᘁX` are the ones chosen by the rigid structure, which
are not found by instance search: Mathlib's instances `hasLeftDualRightDual` and
`hasRightDualLeftDual` take precedence and give `X` itself. So these duals are written out as
`(LeftRigidCategory.leftDual Xᘁ).leftDual` and `(RightRigidCategory.rightDual (ᘁX)).rightDual`,
and the pairings are passed explicitly. -/

section LeftDualRightDual

variable (C) in
/-- The functor `C ⥤ C` of a rigid monoidal category sending `X` to the left dual `ᘁ(Xᘁ)` of its
right dual and `f` to `ᘁ(fᘁ)`. It applies the right dual functor and then the left dual functor,
the latter through its opposite monoidal opposite, and returns to `C` by removing the
wrappers. -/
@[expose]
noncomputable def leftDualRightDualFunctor : C ⥤ C :=
  rightDualFunctor C ⋙ (leftDualFunctor C).op.opMop ⋙ (opMopOpMopEquivalence C).functor

variable (C) in
/-- The functor `X ↦ ᘁ(Xᘁ)` is strong monoidal, as a composite of strong monoidal functors. -/
noncomputable instance leftDualRightDualFunctorMonoidal :
    (leftDualRightDualFunctor C).Monoidal :=
  inferInstanceAs
    (rightDualFunctor C ⋙ (leftDualFunctor C).op.opMop ⋙
      (opMopOpMopEquivalence C).functor).Monoidal

/-- The functor `leftDualRightDualFunctor C` sends `X` to the chosen left dual of `Xᘁ`. -/
@[simp]
theorem leftDualRightDualFunctor_obj (X : C) :
    (leftDualRightDualFunctor C).obj X = (LeftRigidCategory.leftDual Xᘁ).leftDual :=
  (rfl)

/-- The functor `leftDualRightDualFunctor C` sends `f` to the left mate `ᘁ(fᘁ)` of its right
mate. -/
@[simp]
theorem leftDualRightDualFunctor_map {X Y : C} (f : X ⟶ Y) :
    (leftDualRightDualFunctor C).map f =
      leftMate (LeftRigidCategory.leftDual Yᘁ).exact (LeftRigidCategory.leftDual Xᘁ).exact (fᘁ) :=
  leftAdjointMate_eq_leftMate _

variable (C) in
/-- The unit comparison `𝟙_ C ⟶ ᘁ((𝟙_ C)ᘁ)` of `leftDualRightDualFunctor C` is the left mate of
the identification of `(𝟙_ C)ᘁ` with `𝟙_ C`. The right dual of `𝟙_ C` is explicit because it is
the one chosen by the rigid structure, which need not be Mathlib's `hasRightDualUnit`. -/
theorem leftDualRightDualFunctor_ε :
    ε (leftDualRightDualFunctor C) =
      leftMate (LeftRigidCategory.leftDual (RightRigidCategory.rightDual (𝟙_ C)).rightDual).exact
        exactPairingUnit (rightDualIso (RightRigidCategory.rightDual (𝟙_ C)).exact
          exactPairingUnit).hom := by
  have h : ε (leftDualRightDualFunctor C) =
      (leftDualIso (LeftRigidCategory.leftDual (𝟙_ C)).exact exactPairingUnit).inv ≫
        leftMate (LeftRigidCategory.leftDual (RightRigidCategory.rightDual (𝟙_ C)).rightDual).exact
          (LeftRigidCategory.leftDual (𝟙_ C)).exact
          (rightDualIso (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).hom := by
    refine (comp_ε _ _).trans ?_
    rw [comp_ε, Functor.opMop_ε, Functor.op_ε, leftDualFunctor_η, rightDualFunctor_ε,
      opMopOpMopEquivalence_functor_ε]
    -- Removing the wrappers is the identity on morphisms, and the second dual functor sends a
    -- morphism to its adjoint mate, by definition.
    exact (Category.id_comp _ =≫ _).trans (_ ≫= leftAdjointMate_eq_leftMate _)
  rw [h, leftDualIso_inv, ← comp_leftMate, Category.comp_id]

/-- The tensor comparison `ᘁ(Xᘁ) ⊗ ᘁ(Yᘁ) ⟶ ᘁ((X ⊗ Y)ᘁ)` of `leftDualRightDualFunctor C` is the left
mate of the comparison `(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ`, taken with respect to the tensor product pairing. -/
theorem leftDualRightDualFunctor_μ (X Y : C) :
    μ (leftDualRightDualFunctor C) X Y =
      leftMate (LeftRigidCategory.leftDual (X ⊗ Y)ᘁ).exact
        (tensor : ExactPairing ((LeftRigidCategory.leftDual Xᘁ).leftDual ⊗
          (LeftRigidCategory.leftDual Yᘁ).leftDual) (Yᘁ ⊗ Xᘁ)) (rightDualTensorIso X Y).hom := by
  have h : μ (leftDualRightDualFunctor C) X Y =
      (@leftDualTensorIso C _ _ Yᘁ Xᘁ (LeftRigidCategory.leftDual _)
        (LeftRigidCategory.leftDual _) (LeftRigidCategory.leftDual _)).inv ≫
        leftMate (LeftRigidCategory.leftDual (X ⊗ Y)ᘁ).exact
          (LeftRigidCategory.leftDual (Yᘁ ⊗ Xᘁ)).exact (rightDualTensorIso X Y).hom := by
    refine (comp_μ _ _ X Y).trans ?_
    rw [comp_μ, Functor.opMop_μ, Functor.op_μ, leftDualFunctor_δ, rightDualFunctor_μ,
      opMopOpMopEquivalence_functor_μ]
    -- Removing the wrappers is the identity on morphisms, and the second dual functor sends a
    -- morphism to its adjoint mate, by definition.
    exact (Category.id_comp _ =≫ _).trans (_ ≫= leftAdjointMate_eq_leftMate _)
  rw [h, leftDualTensorIso, leftDualIso_inv, ← comp_leftMate, Category.comp_id]

/-- Naturality of the comparisons `ᘁ(Xᘁ) ≅ X`, with the objects written through the chosen
duals. -/
private theorem leftMate_rightAdjointMate_comp_leftDualIso_hom {X Y : C} (f : X ⟶ Y) :
    leftMate (LeftRigidCategory.leftDual Yᘁ).exact (LeftRigidCategory.leftDual Xᘁ).exact (fᘁ) ≫
        (leftDualIso (LeftRigidCategory.leftDual Yᘁ).exact HasRightDual.exact).hom =
      (leftDualIso (LeftRigidCategory.leftDual Xᘁ).exact HasRightDual.exact).hom ≫ f := by
  -- Write `f` as the left mate of `fᘁ` with respect to the pairings `(X, Xᘁ)` and `(Y, Yᘁ)`;
  -- then both sides are left mates of `fᘁ`.
  have hf : f = leftMate (HasRightDual.exact (X := Y)) (HasRightDual.exact (X := X)) (fᘁ) :=
    (leftAdjointMate_rightAdjointMate f).symm.trans (leftAdjointMate_eq_leftMate _)
  conv_rhs => rw [hf]
  rw [leftDualIso_hom, leftDualIso_hom, ← comp_leftMate, ← comp_leftMate, Category.comp_id,
    Category.id_comp]

variable (C) in
/-- In a rigid monoidal category, the left dual `ᘁ(Xᘁ)` of the right dual of `X` is naturally
isomorphic to `X`: both are left duals of `Xᘁ`, and the component is the comparison
`leftDualIso` between them. -/
noncomputable def leftDualRightDualIso : leftDualRightDualFunctor C ≅ 𝟭 C :=
  NatIso.ofComponents
    (fun X => leftDualIso (LeftRigidCategory.leftDual Xᘁ).exact HasRightDual.exact)
    fun f => (leftDualRightDualFunctor_map f =≫ _).trans
      (leftMate_rightAdjointMate_comp_leftDualIso_hom f)

/-- The components of `leftDualRightDualIso C` are the comparisons between the chosen left dual of
`Xᘁ` and `X`. -/
@[simp]
theorem leftDualRightDualIso_hom_app (X : C) :
    (leftDualRightDualIso C).hom.app X =
      (leftDualIso (LeftRigidCategory.leftDual Xᘁ).exact HasRightDual.exact).hom :=
  (rfl)

/-- The components of the inverse of `leftDualRightDualIso C`. -/
@[simp]
theorem leftDualRightDualIso_inv_app (X : C) :
    (leftDualRightDualIso C).inv.app X =
      (leftDualIso (LeftRigidCategory.leftDual Xᘁ).exact HasRightDual.exact).inv :=
  (rfl)

/-- The isomorphism `ᘁ(Xᘁ) ≅ X` is monoidal, so the functor `X ↦ ᘁ(Xᘁ)` is trivialized as a
monoidal functor. -/
instance leftDualRightDualIso_isMonoidal :
    NatTrans.IsMonoidal (leftDualRightDualIso C).hom where
  -- After the structure morphisms are written as left mates, both conditions compose two left
  -- mates; the composite is the left mate of a comparison between two right duals, which is an
  -- identity. The steps through `Eq.trans` let the intermediate objects, written through the
  -- functor or through the chosen duals, be identified up to definitional equality.
  unit := by
    refine (leftDualRightDualFunctor_ε C =≫ _).trans ?_
    simp only [leftDualRightDualIso_hom_app, leftDualIso_hom]
    refine (comp_leftMate _ _ _ _ _).symm.trans ?_
    simp only [Category.id_comp, leftMate_rightDualIso_hom, leftMate_id]
    exact Functor.LaxMonoidal.id_ε.symm
  tensor X Y := by
    refine (leftDualRightDualFunctor_μ X Y =≫ _).trans ?_
    simp only [leftDualRightDualIso_hom_app, leftDualIso_hom]
    refine (comp_leftMate _ _ _ _ _).symm.trans ?_
    rw [Category.id_comp, Functor.LaxMonoidal.id_μ, Category.comp_id]
    refine Eq.trans ?_ (leftMate_tensorHom _ _ _ _ _ _)
    rw [tensorHom_id, id_whiskerRight, rightDualTensorIso]
    exact leftMate_rightDualIso_hom _ _ _

end LeftDualRightDual

section RightDualLeftDual

variable (C) in
/-- The functor `C ⥤ C` of a rigid monoidal category sending `X` to the right dual `(ᘁX)ᘁ` of its
left dual and `f` to `(ᘁf)ᘁ`. It applies the left dual functor and then the right dual functor,
the latter through its opposite monoidal opposite, and returns to `C` by removing the
wrappers. -/
@[expose]
noncomputable def rightDualLeftDualFunctor : C ⥤ C :=
  leftDualFunctor C ⋙ (rightDualFunctor C).op.opMop ⋙ (opMopOpMopEquivalence C).functor

variable (C) in
/-- The functor `X ↦ (ᘁX)ᘁ` is strong monoidal, as a composite of strong monoidal functors. -/
noncomputable instance rightDualLeftDualFunctorMonoidal :
    (rightDualLeftDualFunctor C).Monoidal :=
  inferInstanceAs
    (leftDualFunctor C ⋙ (rightDualFunctor C).op.opMop ⋙
      (opMopOpMopEquivalence C).functor).Monoidal

/-- The functor `rightDualLeftDualFunctor C` sends `X` to the chosen right dual of `ᘁX`. -/
@[simp]
theorem rightDualLeftDualFunctor_obj (X : C) :
    (rightDualLeftDualFunctor C).obj X = (RightRigidCategory.rightDual (ᘁX)).rightDual :=
  (rfl)

/-- The functor `rightDualLeftDualFunctor C` sends `f` to the right mate `(ᘁf)ᘁ` of its left
mate. -/
@[simp]
theorem rightDualLeftDualFunctor_map {X Y : C} (f : X ⟶ Y) :
    (rightDualLeftDualFunctor C).map f =
      rightMate (RightRigidCategory.rightDual (ᘁY)).exact
        (RightRigidCategory.rightDual (ᘁX)).exact (ᘁf) :=
  rightAdjointMate_eq_rightMate _

variable (C) in
/-- The unit comparison `𝟙_ C ⟶ (ᘁ(𝟙_ C))ᘁ` of `rightDualLeftDualFunctor C` is the right mate of
the identification of `ᘁ(𝟙_ C)` with `𝟙_ C`. -/
theorem rightDualLeftDualFunctor_ε :
    ε (rightDualLeftDualFunctor C) =
      rightMate (RightRigidCategory.rightDual (LeftRigidCategory.leftDual (𝟙_ C)).leftDual).exact
        exactPairingUnit (leftDualIso (LeftRigidCategory.leftDual (𝟙_ C)).exact
          exactPairingUnit).hom := by
  have h : ε (rightDualLeftDualFunctor C) =
      (rightDualIso (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).inv ≫
        rightMate (RightRigidCategory.rightDual (LeftRigidCategory.leftDual (𝟙_ C)).leftDual).exact
          (RightRigidCategory.rightDual (𝟙_ C)).exact
          (leftDualIso (LeftRigidCategory.leftDual (𝟙_ C)).exact exactPairingUnit).hom := by
    refine (comp_ε _ _).trans ?_
    rw [comp_ε, Functor.opMop_ε, Functor.op_ε, rightDualFunctor_η, leftDualFunctor_ε,
      opMopOpMopEquivalence_functor_ε]
    -- Removing the wrappers is the identity on morphisms, and the second dual functor sends a
    -- morphism to its adjoint mate, by definition.
    exact (Category.id_comp _ =≫ _).trans (_ ≫= rightAdjointMate_eq_rightMate _)
  rw [h, rightDualIso_inv, ← comp_rightMate, Category.comp_id]

/-- The tensor comparison `(ᘁX)ᘁ ⊗ (ᘁY)ᘁ ⟶ (ᘁ(X ⊗ Y))ᘁ` of `rightDualLeftDualFunctor C` is the
right mate of the comparison `ᘁ(X ⊗ Y) ≅ ᘁY ⊗ ᘁX`, taken with respect to the tensor product
pairing. -/
theorem rightDualLeftDualFunctor_μ (X Y : C) :
    μ (rightDualLeftDualFunctor C) X Y =
      rightMate (RightRigidCategory.rightDual (ᘁ(X ⊗ Y))).exact
        (tensor : ExactPairing ((ᘁY : C) ⊗ (ᘁX : C))
          ((RightRigidCategory.rightDual (ᘁX)).rightDual ⊗
            (RightRigidCategory.rightDual (ᘁY)).rightDual)) (leftDualTensorIso X Y).hom := by
  have h : μ (rightDualLeftDualFunctor C) X Y =
      (@rightDualTensorIso C _ _ (ᘁY) (ᘁX) (RightRigidCategory.rightDual _)
        (RightRigidCategory.rightDual _) (RightRigidCategory.rightDual _)).inv ≫
        rightMate (RightRigidCategory.rightDual (ᘁ(X ⊗ Y))).exact
          (RightRigidCategory.rightDual ((ᘁY : C) ⊗ (ᘁX : C))).exact
          (leftDualTensorIso X Y).hom := by
    refine (comp_μ _ _ X Y).trans ?_
    rw [comp_μ, Functor.opMop_μ, Functor.op_μ, rightDualFunctor_δ, leftDualFunctor_μ,
      opMopOpMopEquivalence_functor_μ]
    -- Removing the wrappers is the identity on morphisms, and the second dual functor sends a
    -- morphism to its adjoint mate, by definition.
    exact (Category.id_comp _ =≫ _).trans (_ ≫= rightAdjointMate_eq_rightMate _)
  rw [h, rightDualTensorIso, rightDualIso_inv, ← comp_rightMate, Category.comp_id]

/-- Naturality of the comparisons `(ᘁX)ᘁ ≅ X`, with the objects written through the chosen
duals. -/
private theorem rightMate_leftAdjointMate_comp_rightDualIso_hom {X Y : C} (f : X ⟶ Y) :
    rightMate (RightRigidCategory.rightDual (ᘁY)).exact
        (RightRigidCategory.rightDual (ᘁX)).exact (ᘁf) ≫
        (rightDualIso (RightRigidCategory.rightDual (ᘁY)).exact HasLeftDual.exact).hom =
      (rightDualIso (RightRigidCategory.rightDual (ᘁX)).exact HasLeftDual.exact).hom ≫ f := by
  -- Write `f` as the right mate of `ᘁf` with respect to the pairings `(ᘁX, X)` and `(ᘁY, Y)`;
  -- then both sides are right mates of `ᘁf`.
  have hf : f = rightMate (HasLeftDual.exact (Y := Y)) (HasLeftDual.exact (Y := X)) (ᘁf) :=
    (rightAdjointMate_leftAdjointMate f).symm.trans (rightAdjointMate_eq_rightMate _)
  conv_rhs => rw [hf]
  rw [rightDualIso_hom, rightDualIso_hom, ← comp_rightMate, ← comp_rightMate, Category.comp_id,
    Category.id_comp]

variable (C) in
/-- In a rigid monoidal category, the right dual `(ᘁX)ᘁ` of the left dual of `X` is naturally
isomorphic to `X`: both are right duals of `ᘁX`, and the component is the comparison
`rightDualIso` between them. -/
noncomputable def rightDualLeftDualIso : rightDualLeftDualFunctor C ≅ 𝟭 C :=
  NatIso.ofComponents
    (fun X => rightDualIso (RightRigidCategory.rightDual (ᘁX)).exact HasLeftDual.exact)
    fun f => (rightDualLeftDualFunctor_map f =≫ _).trans
      (rightMate_leftAdjointMate_comp_rightDualIso_hom f)

/-- The components of `rightDualLeftDualIso C` are the comparisons between the chosen right dual
of `ᘁX` and `X`. -/
@[simp]
theorem rightDualLeftDualIso_hom_app (X : C) :
    (rightDualLeftDualIso C).hom.app X =
      (rightDualIso (RightRigidCategory.rightDual (ᘁX)).exact HasLeftDual.exact).hom :=
  (rfl)

/-- The components of the inverse of `rightDualLeftDualIso C`. -/
@[simp]
theorem rightDualLeftDualIso_inv_app (X : C) :
    (rightDualLeftDualIso C).inv.app X =
      (rightDualIso (RightRigidCategory.rightDual (ᘁX)).exact HasLeftDual.exact).inv :=
  (rfl)

/-- The isomorphism `(ᘁX)ᘁ ≅ X` is monoidal, so the functor `X ↦ (ᘁX)ᘁ` is trivialized as a
monoidal functor. -/
instance rightDualLeftDualIso_isMonoidal :
    NatTrans.IsMonoidal (rightDualLeftDualIso C).hom where
  -- The mirror of `leftDualRightDualIso_isMonoidal`, with right mates in place of left mates.
  unit := by
    refine (rightDualLeftDualFunctor_ε C =≫ _).trans ?_
    simp only [rightDualLeftDualIso_hom_app, rightDualIso_hom]
    refine (comp_rightMate _ _ _ _ _).symm.trans ?_
    simp only [Category.id_comp, rightMate_leftDualIso_hom, rightMate_id]
    exact Functor.LaxMonoidal.id_ε.symm
  tensor X Y := by
    refine (rightDualLeftDualFunctor_μ X Y =≫ _).trans ?_
    simp only [rightDualLeftDualIso_hom_app, rightDualIso_hom]
    refine (comp_rightMate _ _ _ _ _).symm.trans ?_
    rw [Category.id_comp, Functor.LaxMonoidal.id_μ, Category.comp_id]
    refine Eq.trans ?_ (rightMate_tensorHom _ _ _ _ _ _)
    rw [tensorHom_id, id_whiskerRight, leftDualTensorIso]
    exact rightMate_leftDualIso_hom _ _ _

end RightDualLeftDual

end TauCeti

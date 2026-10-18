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
# The left dual functor and the double left dual functor

Mathlib's `CategoryTheory.leftDualFunctor C : C ⥤ (Cᵒᵖ)ᴹᵒᵖ` sends an object `X` of a left rigid
monoidal category to its left dual `ᘁX` and a morphism `f` to its left adjoint mate `ᘁf`. Like
the right dual functor, it is contravariant and reverses the order of tensor products, since
`ᘁ(X ⊗ Y) ≅ ᘁY ⊗ ᘁX` (Mathlib's `CategoryTheory.leftDualTensorIso`).

This file is the left-handed mirror of `TauCeti.CategoryTheory.Monoidal.Rigid.DualFunctor`. It
makes `leftDualFunctor C` a strong monoidal functor, with tensor comparison `leftDualTensorIso`
and unit comparison the identification `ᘁ(𝟙_ C) ≅ 𝟙_ C` through the self-pairing
`exactPairingUnit`. The coherence conditions are proved in `C`, for arbitrary objects with left
duals, as identities between left mates (`CategoryTheory.ExactPairing.leftMate`).

In a rigid monoidal category, the left dual functor is also an equivalence of categories: taking
a right adjoint mate undoes taking a left adjoint mate, and every object is the left dual of its
right dual. Together with the strong monoidal structure, this makes the left dual functor a
monoidal equivalence. Having both dual functors monoidal is what is needed to compare the left
and right double duals as monoidal functors.

Applying the left dual functor twice gives the double left dual functor `C ⥤ C`, sending `X`
to `ᘁ(ᘁX)` and `f` to `ᘁ(ᘁf)`. As for the double right dual functor, the second application
goes through the opposite monoidal opposite of the left dual functor. The resulting functor is
strong monoidal, and in a rigid monoidal category it is a monoidal autoequivalence. In a rigid
monoidal category the double left and double right dual functors are mutually inverse
autoequivalences (EGNO §2.10); a pivotal structure trivializes the double right dual, hence both,
but in general neither need be isomorphic to the identity.

## Main declarations

* `TauCeti.leftDualTensorIso_hom_naturality`: naturality of `leftDualTensorIso`;
* `TauCeti.leftDualTensorIso_associativity`, `TauCeti.leftDualTensorIso_leftUnitality` and
  `TauCeti.leftDualTensorIso_rightUnitality`: its compatibility with the associator and the
  unitors;
* `TauCeti.leftDualFunctorCoreMonoidal` and the instance `TauCeti.leftDualFunctorMonoidal`: the
  strong monoidal structure on `leftDualFunctor C`, with structure morphisms given by
  `TauCeti.leftDualFunctor_ε`, `TauCeti.leftDualFunctor_η`, `TauCeti.leftDualFunctor_μ` and
  `TauCeti.leftDualFunctor_δ`;
* `TauCeti.leftDualFunctorFullyFaithful`: the explicit full-faithfulness structure whose preimage
  operation takes right adjoint mates;
* `TauCeti.leftDualFunctorIsEquivalence`: left duality is an equivalence; together with its
  `Functor.Monoidal` instance, it is a monoidal equivalence.
* `TauCeti.doubleLeftDualFunctor` and the instance `TauCeti.doubleLeftDualFunctorMonoidal`: the
  strong monoidal double left dual functor, with structure morphisms given by
  `TauCeti.doubleLeftDualFunctor_ε`, `TauCeti.doubleLeftDualFunctor_η`,
  `TauCeti.doubleLeftDualFunctor_μ` and `TauCeti.doubleLeftDualFunctor_δ`;
* `TauCeti.doubleLeftDualFunctorIsEquivalence`: in a rigid monoidal category, the double left
  dual functor is an equivalence, hence a monoidal autoequivalence.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §2.10
-/

public section

open CategoryTheory MonoidalCategory MonoidalOpposite Opposite ExactPairing

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The comparison `ᘁ(X ⊗ Y) ≅ ᘁY ⊗ ᘁX` is natural in `X` and `Y`. -/
@[reassoc]
theorem leftDualTensorIso_hom_naturality {X X' Y Y' : C} [HasLeftDual X] [HasLeftDual X']
    [HasLeftDual Y] [HasLeftDual Y'] [HasLeftDual (X ⊗ Y)] [HasLeftDual (X' ⊗ Y')]
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (ᘁ(f ⊗ₘ g)) ≫ (leftDualTensorIso X Y).hom = (leftDualTensorIso X' Y').hom ≫ ((ᘁg) ⊗ₘ (ᘁf)) := by
  simp only [leftDualTensorIso, leftDualIso_hom, leftAdjointMate_eq_leftMate,
    ← leftMate_tensorHom, ← comp_leftMate, Category.id_comp, Category.comp_id]

/-- The comparison `ᘁ(X ⊗ Y) ≅ ᘁY ⊗ ᘁX` is compatible with the associators: the two ways of
identifying `ᘁ(X ⊗ Y ⊗ Z)` with `ᘁZ ⊗ ᘁY ⊗ ᘁX` agree. -/
@[reassoc]
theorem leftDualTensorIso_associativity (X Y Z : C) [HasLeftDual X] [HasLeftDual Y]
    [HasLeftDual Z] [HasLeftDual (X ⊗ Y)] [HasLeftDual (Y ⊗ Z)] [HasLeftDual ((X ⊗ Y) ⊗ Z)]
    [HasLeftDual (X ⊗ Y ⊗ Z)] :
    (ᘁ(α_ X Y Z).hom) ≫ (leftDualTensorIso (X ⊗ Y) Z).hom ≫ (ᘁZ) ◁ (leftDualTensorIso X Y).hom =
      (leftDualTensorIso X (Y ⊗ Z)).hom ≫ (leftDualTensorIso Y Z).hom ▷ (ᘁX) ≫
        (α_ (ᘁZ) (ᘁY) (ᘁX)).hom := by
  simp only [leftDualTensorIso, leftDualIso_hom, leftAdjointMate_eq_leftMate]
  rw [← leftMate_whiskerRight _ _ (HasLeftDual.exact (Y := Z)),
    ← leftMate_whiskerLeft _ _ (HasLeftDual.exact (Y := X)),
    ← leftMate_associator_hom (HasLeftDual.exact (Y := X)) (HasLeftDual.exact (Y := Y))
      (HasLeftDual.exact (Y := Z)),
    ← comp_leftMate, ← comp_leftMate, ← comp_leftMate, ← comp_leftMate]
  simp

/-- The left mate `ᘁX ⟶ ᘁ(𝟙_ C ⊗ X)` of the left unitor of `X`, followed by the comparison
`ᘁ(𝟙_ C ⊗ X) ≅ ᘁX ⊗ ᘁ(𝟙_ C)` and the identification of `ᘁ(𝟙_ C)` with `𝟙_ C`, is the inverse
right unitor `ᘁX ⟶ ᘁX ⊗ 𝟙_ C` of `ᘁX`. -/
theorem leftDualTensorIso_leftUnitality (X : C) [HasLeftDual X] [HasLeftDual (𝟙_ C)]
    [HasLeftDual (𝟙_ C ⊗ X)] :
    (ρ_ (ᘁX)).inv = (ᘁ(λ_ X).hom) ≫ (leftDualTensorIso (𝟙_ C) X).hom ≫
      (ᘁX) ◁ (leftDualIso HasLeftDual.exact exactPairingUnit).hom := by
  simp only [leftDualTensorIso, leftDualIso_hom, leftAdjointMate_eq_leftMate]
  rw [← leftMate_whiskerRight _ _ (HasLeftDual.exact (Y := X)),
    ← leftMate_leftUnitor_hom (HasLeftDual.exact (Y := X)), ← comp_leftMate, ← comp_leftMate]
  simp

/-- The left mate `ᘁX ⟶ ᘁ(X ⊗ 𝟙_ C)` of the right unitor of `X`, followed by the comparison
`ᘁ(X ⊗ 𝟙_ C) ≅ ᘁ(𝟙_ C) ⊗ ᘁX` and the identification of `ᘁ(𝟙_ C)` with `𝟙_ C`, is the inverse
left unitor `ᘁX ⟶ 𝟙_ C ⊗ ᘁX` of `ᘁX`. -/
theorem leftDualTensorIso_rightUnitality (X : C) [HasLeftDual X] [HasLeftDual (𝟙_ C)]
    [HasLeftDual (X ⊗ 𝟙_ C)] :
    (λ_ (ᘁX)).inv = (ᘁ(ρ_ X).hom) ≫ (leftDualTensorIso X (𝟙_ C)).hom ≫
      (leftDualIso HasLeftDual.exact exactPairingUnit).hom ▷ (ᘁX) := by
  simp only [leftDualTensorIso, leftDualIso_hom, leftAdjointMate_eq_leftMate]
  rw [← leftMate_whiskerLeft _ _ (HasLeftDual.exact (Y := X)),
    ← leftMate_rightUnitor_hom (HasLeftDual.exact (Y := X)), ← comp_leftMate, ← comp_leftMate]
  simp

variable (C) [LeftRigidCategory C]

/-! In `(Cᵒᵖ)ᴹᵒᵖ`, composition and tensor products are those of `C` in the reverse order, by
definition. So after `Quiver.Hom.unmop_inj` and `Quiver.Hom.unop_inj`, each coherence condition
for `leftDualFunctor C` is definitionally the corresponding identity in `C` proved above, up to
reassociating the composites. -/

/-- The left dual functor `C ⥤ (Cᵒᵖ)ᴹᵒᵖ` of a left rigid monoidal category is strong
monoidal: the tensor comparison is `leftDualTensorIso` and the unit comparison identifies the
left dual of the unit with the unit. -/
noncomputable def leftDualFunctorCoreMonoidal : (leftDualFunctor C).CoreMonoidal where
  εIso := (mopFunctor _).mapIso
    (leftDualIso (LeftRigidCategory.leftDual (𝟙_ C)).exact exactPairingUnit).op
  μIso X Y := (mopFunctor _).mapIso (leftDualTensorIso X Y).op
  μIso_hom_natural_left f X' := by
    apply Quiver.Hom.unmop_inj
    apply Quiver.Hom.unop_inj
    have h : (leftDualTensorIso _ X').hom ≫ (ᘁX' : C) ◁ (ᘁf) =
        (ᘁ(f ▷ X')) ≫ (leftDualTensorIso _ X').hom := by
      simpa using (leftDualTensorIso_hom_naturality f (𝟙 X')).symm
    exact h
  μIso_hom_natural_right X' f := by
    apply Quiver.Hom.unmop_inj
    apply Quiver.Hom.unop_inj
    have h : (leftDualTensorIso X' _).hom ≫ (ᘁf) ▷ (ᘁX' : C) =
        (ᘁ(X' ◁ f)) ≫ (leftDualTensorIso X' _).hom := by
      simpa using (leftDualTensorIso_hom_naturality (𝟙 X') f).symm
    exact h
  associativity X Y Z := by
    apply Quiver.Hom.unmop_inj
    apply Quiver.Hom.unop_inj
    exact (Category.assoc _ _ _).trans
      ((leftDualTensorIso_associativity X Y Z).trans (Category.assoc _ _ _).symm)
  left_unitality X := by
    apply Quiver.Hom.unmop_inj
    apply Quiver.Hom.unop_inj
    -- The unit comparison uses the rigid structure's left dual of `𝟙_ C`, not `hasLeftDualUnit`.
    exact (@leftDualTensorIso_leftUnitality C _ _ X _ (LeftRigidCategory.leftDual _) _).trans
      (Category.assoc _ _ _).symm
  right_unitality X := by
    apply Quiver.Hom.unmop_inj
    apply Quiver.Hom.unop_inj
    -- The unit comparison uses the rigid structure's left dual of `𝟙_ C`, not `hasLeftDualUnit`.
    exact (@leftDualTensorIso_rightUnitality C _ _ X _ (LeftRigidCategory.leftDual _) _).trans
      (Category.assoc _ _ _).symm

/-- The left dual functor of a left rigid monoidal category is strong monoidal. -/
noncomputable instance leftDualFunctorMonoidal : (leftDualFunctor C).Monoidal :=
  (leftDualFunctorCoreMonoidal C).toMonoidal

open Functor.LaxMonoidal Functor.OplaxMonoidal

/-- The unit comparison of the left dual functor is the identification of the left dual of the
unit with the unit. -/
@[simp]
theorem leftDualFunctor_ε :
    ε (leftDualFunctor C) =
      (leftDualIso (LeftRigidCategory.leftDual (𝟙_ C)).exact exactPairingUnit).hom.op.mop :=
  (rfl)

/-- The inverse unit comparison of the left dual functor. -/
@[simp]
theorem leftDualFunctor_η :
    η (leftDualFunctor C) =
      (leftDualIso (LeftRigidCategory.leftDual (𝟙_ C)).exact exactPairingUnit).inv.op.mop :=
  (rfl)

/-- The tensor comparison of the left dual functor is `leftDualTensorIso`. -/
@[simp]
theorem leftDualFunctor_μ (X Y : C) :
    μ (leftDualFunctor C) X Y = (leftDualTensorIso X Y).hom.op.mop :=
  (rfl)

/-- The inverse tensor comparison of the left dual functor. -/
@[simp]
theorem leftDualFunctor_δ (X Y : C) :
    δ (leftDualFunctor C) X Y = (leftDualTensorIso X Y).inv.op.mop :=
  (rfl)

/-- The left dual functor is fully faithful. Its inverse on each hom-set takes right adjoint
mates. -/
def leftDualFunctorFullyFaithful : (leftDualFunctor C).FullyFaithful where
  preimage {X Y} f := by
    -- Expose the object formula through the two opposite-category wrappers so the right mate has
    -- the original objects `X` and `Y` as its endpoints.
    change mop (op (ᘁX)) ⟶ mop (op (ᘁY)) at f
    exact rightAdjointMate f.unmop.unop
  map_preimage {X Y} f := by
    -- Expose both the object and morphism formulas before cancelling the wrapper constructors.
    change mop (op (ᘁX)) ⟶ mop (op (ᘁY)) at f
    simp only [leftDualFunctor_map]
    apply Quiver.Hom.unmop_inj
    apply Quiver.Hom.unop_inj
    exact leftAdjointMate_rightAdjointMate f.unmop.unop
  preimage_map f := rightAdjointMate_leftAdjointMate f

/-- The preimage operation for the full faithfulness of the left dual functor takes right adjoint
mates. -/
@[simp]
theorem leftDualFunctorFullyFaithful_preimage {X Y : C}
    (f : mop (op (ᘁX)) ⟶ mop (op (ᘁY))) :
    (leftDualFunctorFullyFaithful C).preimage f = rightAdjointMate f.unmop.unop := by
  rfl

/-- The left dual functor of a left rigid monoidal category is faithful. -/
instance leftDualFunctorFaithful : (leftDualFunctor C).Faithful :=
  (leftDualFunctorFullyFaithful C).faithful

/-- The left dual functor of a left rigid monoidal category is full. -/
instance leftDualFunctorFull : (leftDualFunctor C).Full :=
  (leftDualFunctorFullyFaithful C).full

end TauCeti

namespace TauCeti

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- The left dual functor of a rigid monoidal category is an equivalence of categories. -/
instance leftDualFunctorIsEquivalence : (leftDualFunctor C).IsEquivalence where
  essSurj :=
    { mem_essImage := fun X =>
        ⟨(X.unmop.unop)ᘁ,
          ⟨(mopFunctor (Cᵒᵖ)).mapIso
            (leftDualIso (LeftRigidCategory.leftDual ((X.unmop.unop)ᘁ)).exact
              (RightRigidCategory.rightDual (X.unmop.unop)).exact).symm.op⟩⟩ }

end TauCeti

namespace TauCeti

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

section DoubleLeftDual

variable [LeftRigidCategory C]

/-- The double left dual functor `C ⥤ C` of a left rigid monoidal category, sending `X` to
`ᘁ(ᘁX)` and `f` to `ᘁ(ᘁf)`. It applies the left dual functor twice, the second time through its
opposite monoidal opposite, and returns to `C` by removing the wrappers. -/
@[expose]
noncomputable def doubleLeftDualFunctor : C ⥤ C :=
  leftDualFunctor C ⋙ (leftDualFunctor C).op.opMop ⋙ (opMopOpMopEquivalence C).functor

/-- The double left dual functor is strong monoidal, as the composite of the strong monoidal
left dual functor, its opposite monoidal opposite, and the removal of the wrappers. -/
noncomputable instance doubleLeftDualFunctorMonoidal : (doubleLeftDualFunctor C).Monoidal :=
  inferInstanceAs
    (leftDualFunctor C ⋙ (leftDualFunctor C).op.opMop ⋙
      (opMopOpMopEquivalence C).functor).Monoidal

variable {C}

/-- The double left dual functor sends `X` to `ᘁ(ᘁX)`. -/
@[simp]
theorem doubleLeftDualFunctor_obj (X : C) :
    (doubleLeftDualFunctor C).obj X = (ᘁ(ᘁX) : C) :=
  (rfl)

/-- The double left dual functor sends `f` to `ᘁ(ᘁf)`. -/
@[simp]
theorem doubleLeftDualFunctor_map {X Y : C} (f : X ⟶ Y) :
    (doubleLeftDualFunctor C).map f = ᘁ(ᘁf) :=
  (rfl)

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable (C)

/-! The structure morphisms of a composite of monoidal functors are composites of the structure
morphisms of its factors (`Functor.LaxMonoidal.comp_μ` and its relatives). Those of the left dual
functor and of its opposite monoidal opposite are, after removing the wrappers, the morphisms of
`C` displayed below, while those of the removal of the wrappers are identities. -/

/-- The unit comparison `𝟙_ C ⟶ ᘁ(ᘁ(𝟙_ C))` of the double left dual functor: identify `𝟙_ C` with
`ᘁ(𝟙_ C)`, then take the mate of the identification of `ᘁ(𝟙_ C)` with `𝟙_ C`. The pairings are
explicit because `ᘁ(𝟙_ C)` is the dual chosen by the rigid structure, which need not be Mathlib's
`hasLeftDualUnit`. -/
theorem doubleLeftDualFunctor_ε :
    ε (doubleLeftDualFunctor C) =
      (leftDualIso (LeftRigidCategory.leftDual (𝟙_ C)).exact exactPairingUnit).inv ≫
        leftMate HasLeftDual.exact (LeftRigidCategory.leftDual (𝟙_ C)).exact
          (leftDualIso (LeftRigidCategory.leftDual (𝟙_ C)).exact exactPairingUnit).hom :=
  (Category.id_comp _ =≫ _).trans
    (_ ≫= leftAdjointMate_eq_leftMate _)

/-- The inverse unit comparison `ᘁ(ᘁ(𝟙_ C)) ⟶ 𝟙_ C` of the double left dual functor. -/
theorem doubleLeftDualFunctor_η :
    η (doubleLeftDualFunctor C) =
      leftMate (LeftRigidCategory.leftDual (𝟙_ C)).exact HasLeftDual.exact
          (leftDualIso (LeftRigidCategory.leftDual (𝟙_ C)).exact exactPairingUnit).inv ≫
        (leftDualIso (LeftRigidCategory.leftDual (𝟙_ C)).exact exactPairingUnit).hom :=
  (_ ≫= Category.comp_id _).trans
    (leftAdjointMate_eq_leftMate _ =≫ _)

/-- The tensor comparison `ᘁ(ᘁX) ⊗ ᘁ(ᘁY) ⟶ ᘁ(ᘁ(X ⊗ Y))` of the double left dual functor:
identify `ᘁ(ᘁX) ⊗ ᘁ(ᘁY)` with `ᘁ(ᘁY ⊗ ᘁX)`, then take the mate of the comparison
`ᘁ(X ⊗ Y) ≅ ᘁY ⊗ ᘁX`. -/
theorem doubleLeftDualFunctor_μ (X Y : C) :
    μ (doubleLeftDualFunctor C) X Y =
      (leftDualTensorIso (ᘁY) (ᘁX)).inv ≫ ᘁ((leftDualTensorIso X Y).hom) :=
  (Functor.LaxMonoidal.comp_μ _ _ X Y).trans
    ((Functor.LaxMonoidal.comp_μ _ _ _ _ =≫ _).trans (Category.id_comp _ =≫ _))

/-- The inverse tensor comparison `ᘁ(ᘁ(X ⊗ Y)) ⟶ ᘁ(ᘁX) ⊗ ᘁ(ᘁY)` of the double left dual
functor. -/
theorem doubleLeftDualFunctor_δ (X Y : C) :
    δ (doubleLeftDualFunctor C) X Y =
      (ᘁ((leftDualTensorIso X Y).inv) :
        (ᘁ(ᘁ(X ⊗ Y) : C) : C) ⟶ (ᘁ((ᘁY : C) ⊗ (ᘁX : C)) : C)) ≫
        (leftDualTensorIso (ᘁY) (ᘁX)).hom :=
  (Functor.OplaxMonoidal.comp_δ _ _ X Y).trans
    (_ ≫= (Functor.OplaxMonoidal.comp_δ _ _ _ _).trans (Category.comp_id _))

end DoubleLeftDual

/-- The double left dual functor of a rigid monoidal category is an equivalence of categories;
with its `Functor.Monoidal` instance, it is a monoidal autoequivalence. -/
instance doubleLeftDualFunctorIsEquivalence [RigidCategory C] :
    (doubleLeftDualFunctor C).IsEquivalence :=
  inferInstanceAs
    (leftDualFunctor C ⋙ (leftDualFunctor C).op.opMop ⋙
      (opMopOpMopEquivalence C).functor).IsEquivalence

end TauCeti

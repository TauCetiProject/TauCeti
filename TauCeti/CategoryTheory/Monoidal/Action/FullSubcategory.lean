/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Action.LinearFunctor
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Restricting a monoidal left action to a full subcategory

Let a monoidal category `C` act on the left on a category `D`, and let `P : ObjectProperty D`
be stable under the action: `P d` implies `P (c ⊙ₗ d)` for every `c : C`. Then the action
restricts to the full subcategory `P.FullSubcategory`, with the same action on objects and
morphisms and with structure isomorphisms lifted from `D`. For a group `G`, an action of
`Discrete G` is a categorical group action, and this restricts it to any invariant full
subcategory, for instance a full subcategory of modules cut out by a condition that the
action preserves. Stable properties are closed under `⊓` and `isoClosure`, and the essential
image of a left-linear functor is stable. If the action functors on a preadditive category `D`
are additive or `R`-linear, so are the restricted ones.

The comparison functors of full subcategories are then equivariant, in the sense of Mathlib's
`Functor.LeftLinear`:

* the inclusion `P.ι : P.FullSubcategory ⥤ D`, with identity lineators;
* the inclusion `ObjectProperty.ιOfLE h : P.FullSubcategory ⥤ Q.FullSubcategory` for
  `h : P ≤ Q`, with identity lineators; it compares restricting to `P` directly with
  restricting first to `Q`;
* the lift `P.lift F hF` of a (lax, oplax or strong) left-linear functor `F` whose values
  satisfy `P`, with the lineators of `F` (which need not be identities). In particular the
  corestriction `F.toEssImage` of a left-linear functor to its essential image is left-linear,
  again with the lineators of `F`.

This follows Mathlib's construction of the monoidal structure on a full subcategory
(`CategoryTheory.ObjectProperty.fullMonoidalSubcategory`).

## Main declarations

* `CategoryTheory.ObjectProperty.IsStableUnderLeftAction`: the property `P` is stable under
  the left action of `C`;
* `CategoryTheory.ObjectProperty.fullSubcategoryMonoidalLeftAction`: the restricted action of
  `C` on `P.FullSubcategory`.
-/

public section

namespace CategoryTheory.ObjectProperty

open MonoidalCategory MonoidalLeftAction Functor.LaxLeftLinear Functor.OplaxLeftLinear

variable {C : Type*} [Category* C] [MonoidalCategory C] {D : Type*} [Category* D]
  [MonoidalLeftAction C D]

variable (C) in
/-- A property `P` of objects of `D` is stable under the left action of `C` on `D` if
`P d` implies `P (c ⊙ₗ d)` for all `c : C` and `d : D`. -/
class IsStableUnderLeftAction (P : ObjectProperty D) : Prop where
  prop_actionObj (c : C) (d : D) (hd : P d) : P (c ⊙ₗ d)

lemma prop_actionObj (P : ObjectProperty D) [P.IsStableUnderLeftAction C] (c : C) {d : D}
    (hd : P d) : P (c ⊙ₗ d) :=
  IsStableUnderLeftAction.prop_actionObj c d hd

instance (P Q : ObjectProperty D) [P.IsStableUnderLeftAction C]
    [Q.IsStableUnderLeftAction C] : (P ⊓ Q).IsStableUnderLeftAction C where
  prop_actionObj c _ hd := ⟨P.prop_actionObj c hd.1, Q.prop_actionObj c hd.2⟩

instance : (⊤ : ObjectProperty D).IsStableUnderLeftAction C where
  prop_actionObj _ _ _ := trivial

/-- The closure under isomorphisms of a property stable under the action is stable. -/
instance (P : ObjectProperty D) [P.IsStableUnderLeftAction C] :
    P.isoClosure.IsStableUnderLeftAction C where
  prop_actionObj c _ := by
    rintro ⟨Y, hY, ⟨e⟩⟩
    exact ⟨c ⊙ₗ Y, P.prop_actionObj c hY, ⟨(actionLeft D c).mapIso e⟩⟩

/-- The essential image of a left-linear functor is stable under the action. -/
instance {E : Type*} [Category* E] [MonoidalLeftAction C E] (F : E ⥤ D) [F.LeftLinear C] :
    F.essImage.IsStableUnderLeftAction C where
  prop_actionObj c _ := by
    rintro ⟨X, ⟨e⟩⟩
    exact ⟨c ⊙ₗ X, ⟨(Functor.LeftLinear.μₗIso F c X).symm ≪≫ (actionLeft D c).mapIso e⟩⟩

variable (P : ObjectProperty D) [P.IsStableUnderLeftAction C]

/-- The data of the left action of `C` on a full subcategory `P.FullSubcategory` of objects
stable under the action, computed in `D`. -/
@[simps]
instance fullSubcategoryMonoidalLeftActionStruct :
    MonoidalLeftActionStruct C P.FullSubcategory where
  actionObj c X := ⟨c ⊙ₗ X.obj, P.prop_actionObj c X.property⟩
  actionHomLeft f X := homMk (f ⊵ₗ X.obj)
  actionHomRight c _ _ f := homMk (c ⊴ₗ f.hom)
  actionHom f g := homMk (f ⊙ₗₘ g.hom)
  actionAssocIso c c' X := P.isoMk (αₗ c c' X.obj)
  actionUnitIso X := P.isoMk (λₗ X.obj)

/-- A left action of `C` on `D` restricts to a left action on the full subcategory of objects
satisfying a property `P` that is stable under the action. -/
instance fullSubcategoryMonoidalLeftAction : MonoidalLeftAction C P.FullSubcategory where
  actionHom_def := by intros; ext; exact MonoidalLeftAction.actionHom_def _ _
  actionAssocIso_hom_naturality := by
    intros; ext; exact MonoidalLeftAction.actionAssocIso_hom_naturality _ _ _

/-- The inclusion of a full subcategory stable under the action is left-linear, with
identity lineators. -/
instance leftLinearι : P.ι.LeftLinear C where
  μₗ _ _ := 𝟙 _
  δₗ _ _ := 𝟙 _
  μₗ_comp_δₗ _ _ := Category.id_comp _
  δₗ_comp_μₗ _ _ := Category.id_comp _

@[simp] lemma ι_μₗ (c : C) (X : P.FullSubcategory) : μₗ P.ι c X = 𝟙 _ := rfl
@[simp] lemma ι_δₗ (c : C) (X : P.FullSubcategory) : δₗ P.ι c X = 𝟙 _ := rfl

section Linear

variable [Preadditive D] (c : C)

/-- If the action of `c` on `D` is additive, so is its restriction to `P.FullSubcategory`. -/
instance [(actionLeft D c).Additive] : (actionLeft P.FullSubcategory c).Additive where
  map_add := by intros; ext; exact (actionLeft D c).map_add

/-- If the action of `c` on `D` is `R`-linear, so is its restriction to `P.FullSubcategory`. -/
instance (R : Type*) [Semiring R] [Linear R D] [(actionLeft D c).Linear R] :
    (actionLeft P.FullSubcategory c).Linear R where
  map_smul _ _ := by ext; exact (actionLeft D c).map_smul _ _

end Linear

section ιOfLE

variable {P} {Q : ObjectProperty D} [Q.IsStableUnderLeftAction C] (h : P ≤ Q)

/-- For stable properties `P ≤ Q`, the inclusion `P.FullSubcategory ⥤ Q.FullSubcategory`
is left-linear with identity lineators: restricting the action to `P` agrees with restricting
it first to `Q` and then to `P`. -/
instance leftLinearιOfLE : (ιOfLE h).LeftLinear C where
  μₗ _ _ := 𝟙 _
  δₗ _ _ := 𝟙 _
  μₗ_comp_δₗ _ _ := Category.id_comp _
  δₗ_comp_μₗ _ _ := Category.id_comp _

@[simp] lemma ιOfLE_μₗ (c : C) (X : P.FullSubcategory) : μₗ (ιOfLE h) c X = 𝟙 _ := rfl
@[simp] lemma ιOfLE_δₗ (c : C) (X : P.FullSubcategory) : δₗ (ιOfLE h) c X = 𝟙 _ := rfl

end ιOfLE

section lift

variable {E : Type*} [Category* E] [MonoidalLeftAction C E] (F : E ⥤ D) (hF : ∀ X, P (F.obj X))

/-- The lift through `P.FullSubcategory` of a lax left-linear functor is lax left-linear, with
the lineators of `F`. -/
instance laxLeftLinearLift [F.LaxLeftLinear C] : (P.lift F hF).LaxLeftLinear C where
  μₗ c X := homMk (μₗ F c X)
  μₗ_naturality_left f X := by ext; exact μₗ_naturality_left F f X
  μₗ_naturality_right c _ _ f := by ext; exact μₗ_naturality_right F c f
  μₗ_associativity c c' X := by ext; exact μₗ_associativity F c c' X
  μₗ_unitality X := by ext; exact μₗ_unitality F X

@[simp]
lemma lift_μₗ_hom [F.LaxLeftLinear C] (c : C) (X : E) :
    (μₗ (P.lift F hF) c X).hom = μₗ F c X :=
  rfl

/-- The lift through `P.FullSubcategory` of an oplax left-linear functor is oplax left-linear,
with the lineators of `F`. -/
instance oplaxLeftLinearLift [F.OplaxLeftLinear C] : (P.lift F hF).OplaxLeftLinear C where
  δₗ c X := homMk (δₗ F c X)
  δₗ_naturality_left f X := by ext; exact δₗ_naturality_left F f X
  δₗ_naturality_right c _ _ f := by ext; exact δₗ_naturality_right F c f
  δₗ_associativity c c' X := by ext; exact δₗ_associativity F c c' X
  δₗ_unitality_inv X := by ext; exact δₗ_unitality_inv F X

@[simp]
lemma lift_δₗ_hom [F.OplaxLeftLinear C] (c : C) (X : E) :
    (δₗ (P.lift F hF) c X).hom = δₗ F c X :=
  rfl

/-- The lift through `P.FullSubcategory` of a left-linear functor is left-linear, with the
lineators of `F`. -/
instance leftLinearLift [F.LeftLinear C] : (P.lift F hF).LeftLinear C where
  μₗ_comp_δₗ c X := by ext; exact Functor.LeftLinear.μₗ_comp_δₗ F c X
  δₗ_comp_μₗ c X := by ext; exact Functor.LeftLinear.δₗ_comp_μₗ F c X

end lift

end CategoryTheory.ObjectProperty

namespace CategoryTheory.Functor

open MonoidalCategory MonoidalLeftAction Functor.LaxLeftLinear Functor.OplaxLeftLinear

variable {C : Type*} [Category* C] [MonoidalCategory C] {D : Type*} [Category* D]
  [MonoidalLeftAction C D] {E : Type*} [Category* E] [MonoidalLeftAction C E]

/-- The corestriction `F.toEssImage` of a left-linear functor to its essential image is
left-linear, with the lineators of `F`. -/
instance leftLinearToEssImage (F : E ⥤ D) [F.LeftLinear C] : F.toEssImage.LeftLinear C :=
  inferInstanceAs ((F.essImage.lift F F.obj_mem_essImage).LeftLinear C)

@[simp]
lemma toEssImage_μₗ_hom (F : E ⥤ D) [F.LeftLinear C] (c : C) (X : E) :
    (μₗ F.toEssImage c X).hom = μₗ F c X :=
  rfl

@[simp]
lemma toEssImage_δₗ_hom (F : E ⥤ D) [F.LeftLinear C] (c : C) (X : E) :
    (δₗ F.toEssImage c X).hom = δₗ F c X :=
  rfl

end CategoryTheory.Functor

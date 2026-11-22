/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Center

/-!
# The centre of a lax monoidal functor

Let `F : C ⥤ D` be a lax monoidal functor between monoidal categories. A half-braiding relative
to `F` on an object `X : D` is a family of isomorphisms `β U : X ⊗ F.obj U ≅ F.obj U ⊗ X`,
natural in `U : C`, which is compatible with the tensorator `μ` and the unit `ε` of `F`: moving
`X` past `F.obj (U ⊗ U')` is moving it past `F.obj U'` and then past `F.obj U`, and moving it past
`F.obj (𝟙_ C)` is trivial. The centre `Functor.RelativeCenter F` of `F` (the relative centre
`Z(F)` of Gainutdinov–Haferkamp–Schweigert) has as objects the pairs of an object of `D` and a
half-braiding relative to `F` on it, and as morphisms the morphisms of `D` commuting with the
half-braidings.

For `F` the identity functor the half-braidings relative to `F` are Mathlib's `HalfBraiding`s,
which satisfy the compatibility with the unit automatically. For a lax monoidal functor whose unit
`ε` is not invertible, this compatibility is an additional condition.

Following Mathlib's `Center`, this file makes `Functor.RelativeCenter F` a monoidal category,
with tensor product computed in `D`: the half-braiding `RelativeHalfBraiding.tensor` of `X ⊗ Y`
moves `Y` and then `X`, and the unit is `𝟙_ D` with the half-braiding
`RelativeHalfBraiding.tensorUnit` given by the unitors. The forgetful functor
`Functor.RelativeCenter.forget F` to `D` is faithful, reflects isomorphisms and is monoidal, with
identity tensorator and unit. Nothing here uses rigidity, linearity or a strong monoidal
structure on `F`.

The relative centre is where the coefficients of Davydov–Yetter cohomology of a tensor functor
live; for fusion categories of nonzero global dimension the vanishing of this cohomology is
Ocneanu rigidity.

## Main declarations

* `CategoryTheory.Functor.RelativeHalfBraiding`: a half-braiding relative to `F`;
* `CategoryTheory.Functor.RelativeCenter`: the centre of `F`, with its `MonoidalCategory`
  instance;
* `CategoryTheory.Functor.RelativeCenter.forget`: the faithful monoidal forgetful functor to `D`.

## References

* A. M. Gainutdinov, J. Haferkamp, C. Schweigert, *Davydov–Yetter cohomology, comonads and
  Ocneanu rigidity*, Adv. Math. 414 (2023), arXiv:1910.06094, Definitions 3.1 and 3.2.
* The construction follows Mathlib's `CategoryTheory.Center`, by Kim Morrison.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal

namespace Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

variable (F : C ⥤ D) [F.LaxMonoidal]

/-- A half-braiding relative to a lax monoidal functor `F : C ⥤ D` on an object `X : D` is a
family of isomorphisms `X ⊗ F.obj U ≅ F.obj U ⊗ X`, natural in `U : C` and compatible with the
tensorator and the unit of `F`. -/
structure RelativeHalfBraiding (X : D) where
  /-- The family of isomorphisms `X ⊗ F.obj U ≅ F.obj U ⊗ X`. -/
  β : ∀ U, X ⊗ F.obj U ≅ F.obj U ⊗ X
  /-- Moving `X` past `F.obj (U ⊗ U')` is moving it past `F.obj U'` and then past `F.obj U`. -/
  monoidal : ∀ U U', X ◁ μ F U U' ≫ (β (U ⊗ U')).hom =
      (α_ _ _ _).inv ≫ (β U).hom ▷ F.obj U' ≫ (α_ _ _ _).hom ≫ F.obj U ◁ (β U').hom ≫
        (α_ _ _ _).inv ≫ μ F U U' ▷ X := by
    cat_disch
  /-- Moving `X` past `F.obj (𝟙_ C)` is trivial. -/
  unit : X ◁ ε F ≫ (β (𝟙_ C)).hom = (ρ_ X).hom ≫ (λ_ X).inv ≫ ε F ▷ X := by
    cat_disch
  /-- The isomorphisms `β U` are natural in `U`. -/
  naturality : ∀ {U U'} (f : U ⟶ U'),
      X ◁ F.map f ≫ (β U').hom = (β U).hom ≫ F.map f ▷ X := by
    cat_disch

attribute [reassoc] RelativeHalfBraiding.monoidal RelativeHalfBraiding.unit

attribute [reassoc (attr := simp)] RelativeHalfBraiding.naturality

namespace RelativeHalfBraiding

variable {F}

/-- The half-braiding relative to `F` on `X ⊗ Y` built from half-braidings on `X` and `Y`: it
moves `Y` and then `X`. -/
def tensor {X Y : D} (bX : F.RelativeHalfBraiding X) (bY : F.RelativeHalfBraiding Y) :
    F.RelativeHalfBraiding (X ⊗ Y) where
  β U := α_ _ _ _ ≪≫ MonoidalCategory.whiskerLeftIso X (bY.β U) ≪≫ (α_ _ _ _).symm ≪≫
    MonoidalCategory.whiskerRightIso (bX.β U) Y ≪≫ α_ _ _ _
  monoidal U U' := by
    simp only [Iso.trans_hom, MonoidalCategory.whiskerLeftIso_hom, Iso.symm_hom,
      MonoidalCategory.whiskerRightIso_hom]
    calc
      _ = 𝟙 _ ⊗≫ X ◁ (Y ◁ μ F U U' ≫ (bY.β (U ⊗ U')).hom) ⊗≫
            (bX.β (U ⊗ U')).hom ▷ Y ⊗≫ 𝟙 _ := by monoidal
      _ = 𝟙 _ ⊗≫ X ◁ (bY.β U).hom ▷ F.obj U' ⊗≫ X ◁ F.obj U ◁ (bY.β U').hom ⊗≫
            (X ◁ μ F U U' ≫ (bX.β (U ⊗ U')).hom) ▷ Y ⊗≫ 𝟙 _ := by
        rw [bY.monoidal]; monoidal
      _ = 𝟙 _ ⊗≫ X ◁ (bY.β U).hom ▷ F.obj U' ⊗≫
            ((X ⊗ F.obj U) ◁ (bY.β U').hom ≫ (bX.β U).hom ▷ (F.obj U' ⊗ Y)) ⊗≫
            F.obj U ◁ (bX.β U').hom ▷ Y ⊗≫ μ F U U' ▷ X ▷ Y ⊗≫ 𝟙 _ := by
        rw [bX.monoidal]; monoidal
      _ = _ := by rw [whisker_exchange]; monoidal
  unit := by
    simp only [Iso.trans_hom, MonoidalCategory.whiskerLeftIso_hom, Iso.symm_hom,
      MonoidalCategory.whiskerRightIso_hom]
    calc
      _ = 𝟙 _ ⊗≫ X ◁ (Y ◁ ε F ≫ (bY.β (𝟙_ C)).hom) ⊗≫ (bX.β (𝟙_ C)).hom ▷ Y ⊗≫ 𝟙 _ := by
        monoidal
      _ = 𝟙 _ ⊗≫ (X ◁ ε F ≫ (bX.β (𝟙_ C)).hom) ▷ Y ⊗≫ 𝟙 _ := by
        rw [bY.unit]; monoidal
      _ = _ := by rw [bX.unit]; monoidal
  naturality {U U'} f := by
    simp only [Iso.trans_hom, MonoidalCategory.whiskerLeftIso_hom, Iso.symm_hom,
      MonoidalCategory.whiskerRightIso_hom]
    calc
      _ = 𝟙 _ ⊗≫ X ◁ (Y ◁ F.map f ≫ (bY.β U').hom) ⊗≫ (bX.β U').hom ▷ Y ⊗≫ 𝟙 _ := by
        monoidal
      _ = 𝟙 _ ⊗≫ X ◁ (bY.β U).hom ⊗≫ (X ◁ F.map f ≫ (bX.β U').hom) ▷ Y ⊗≫ 𝟙 _ := by
        rw [bY.naturality]; monoidal
      _ = _ := by rw [bX.naturality]; monoidal

@[simp]
theorem tensor_β_hom {X Y : D} (bX : F.RelativeHalfBraiding X) (bY : F.RelativeHalfBraiding Y)
    (U : C) :
    ((bX.tensor bY).β U).hom =
      (α_ _ _ _).hom ≫ X ◁ (bY.β U).hom ≫ (α_ _ _ _).inv ≫ (bX.β U).hom ▷ Y ≫ (α_ _ _ _).hom :=
  rfl

@[simp]
theorem tensor_β_inv {X Y : D} (bX : F.RelativeHalfBraiding X) (bY : F.RelativeHalfBraiding Y)
    (U : C) :
    ((bX.tensor bY).β U).inv =
      (α_ _ _ _).inv ≫ (bX.β U).inv ▷ Y ≫ (α_ _ _ _).hom ≫ X ◁ (bY.β U).inv ≫ (α_ _ _ _).inv := by
  simp [tensor]

variable (F) in
/-- The half-braiding relative to `F` on the unit object `𝟙_ D`, given by the unitors. -/
def tensorUnit : F.RelativeHalfBraiding (𝟙_ D) where
  β U := λ_ (F.obj U) ≪≫ (ρ_ (F.obj U)).symm
  monoidal U U' := by
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [id_whiskerLeft_assoc, Iso.inv_hom_id_assoc]
    monoidal
  unit := by
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [id_whiskerLeft_assoc, Iso.inv_hom_id_assoc]
    monoidal
  naturality f := by
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [id_whiskerLeft_assoc, Iso.inv_hom_id_assoc]
    monoidal

@[simp]
theorem tensorUnit_β_hom (U : C) :
    ((tensorUnit F).β U).hom = (λ_ (F.obj U)).hom ≫ (ρ_ (F.obj U)).inv :=
  rfl

@[simp]
theorem tensorUnit_β_inv (U : C) :
    ((tensorUnit F).β U).inv = (ρ_ (F.obj U)).hom ≫ (λ_ (F.obj U)).inv :=
  rfl

end RelativeHalfBraiding

/-- The centre of a lax monoidal functor `F : C ⥤ D`, also called the relative centre `Z(F)`: its
objects are pairs of an object of `D` and a half-braiding relative to `F` on it. -/
structure RelativeCenter where
  /-- The underlying object of `D`. -/
  obj : D
  /-- The half-braiding relative to `F` on the underlying object. -/
  halfBraiding : F.RelativeHalfBraiding obj

namespace RelativeCenter

variable {F}

/-- A morphism in the centre of `F`: a morphism of `D` between the underlying objects which
commutes with the half-braidings. -/
@[ext]
structure Hom (X Y : F.RelativeCenter) where
  /-- The underlying morphism of `D`. -/
  f : X.obj ⟶ Y.obj
  /-- The underlying morphism commutes with the half-braidings. -/
  comm : ∀ U, f ▷ F.obj U ≫ (Y.halfBraiding.β U).hom =
      (X.halfBraiding.β U).hom ≫ F.obj U ◁ f := by
    cat_disch

attribute [reassoc (attr := simp)] Hom.comm

instance : Quiver F.RelativeCenter where
  Hom := Hom

@[ext]
theorem ext {X Y : F.RelativeCenter} (f g : X ⟶ Y) (w : f.f = g.f) : f = g :=
  Hom.ext w

instance : Category F.RelativeCenter where
  id X := { f := 𝟙 X.obj }
  comp f g := { f := f.f ≫ g.f }

@[simp]
theorem id_f (X : F.RelativeCenter) : Hom.f (𝟙 X) = 𝟙 X.obj :=
  rfl

@[simp]
theorem comp_f {X Y Z : F.RelativeCenter} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).f = f.f ≫ g.f :=
  rfl

/-- An isomorphism in the centre of `F` built from a morphism whose underlying morphism is an
isomorphism. -/
@[simps]
noncomputable def isoMk {X Y : F.RelativeCenter} (f : X ⟶ Y) [IsIso f.f] : X ≅ Y where
  hom := f
  inv := ⟨CategoryTheory.inv f.f, fun U ↦ by
    simp [← cancel_epi (f.f ▷ F.obj U), ← comp_whiskerRight_assoc,
      ← MonoidalCategory.whiskerLeft_comp]⟩

instance isIso_of_f_isIso {X Y : F.RelativeCenter} (f : X ⟶ Y) [IsIso f.f] : IsIso f :=
  (isoMk f).isIso_hom

/-- Auxiliary definition for the `MonoidalCategory` instance on the centre of `F`: the tensor
product of the underlying objects, with the half-braiding `RelativeHalfBraiding.tensor`. -/
abbrev tensorObj (X Y : F.RelativeCenter) : F.RelativeCenter :=
  ⟨X.obj ⊗ Y.obj, X.halfBraiding.tensor Y.halfBraiding⟩

@[reassoc]
theorem whiskerLeft_comm (X : F.RelativeCenter) {Y₁ Y₂ : F.RelativeCenter} (f : Y₁ ⟶ Y₂)
    (U : C) :
    (X.obj ◁ f.f) ▷ F.obj U ≫ ((tensorObj X Y₂).halfBraiding.β U).hom =
      ((tensorObj X Y₁).halfBraiding.β U).hom ≫ F.obj U ◁ X.obj ◁ f.f := by
  simp only [RelativeHalfBraiding.tensor_β_hom]
  calc
    _ = 𝟙 _ ⊗≫ X.obj ◁ (f.f ▷ F.obj U ≫ (Y₂.halfBraiding.β U).hom) ⊗≫
          (X.halfBraiding.β U).hom ▷ Y₂.obj ⊗≫ 𝟙 _ := by
      monoidal
    _ = 𝟙 _ ⊗≫ X.obj ◁ (Y₁.halfBraiding.β U).hom ⊗≫
          ((X.obj ⊗ F.obj U) ◁ f.f ≫ (X.halfBraiding.β U).hom ▷ Y₂.obj) ⊗≫ 𝟙 _ := by
      rw [f.comm]; monoidal
    _ = _ := by rw [whisker_exchange]; monoidal

/-- Auxiliary definition for the `MonoidalCategory` instance on the centre of `F`. -/
def whiskerLeft (X : F.RelativeCenter) {Y₁ Y₂ : F.RelativeCenter} (f : Y₁ ⟶ Y₂) :
    tensorObj X Y₁ ⟶ tensorObj X Y₂ where
  f := X.obj ◁ f.f
  comm U := whiskerLeft_comm X f U

@[reassoc]
theorem whiskerRight_comm {X₁ X₂ : F.RelativeCenter} (f : X₁ ⟶ X₂) (Y : F.RelativeCenter)
    (U : C) :
    f.f ▷ Y.obj ▷ F.obj U ≫ ((tensorObj X₂ Y).halfBraiding.β U).hom =
      ((tensorObj X₁ Y).halfBraiding.β U).hom ≫ F.obj U ◁ f.f ▷ Y.obj := by
  simp only [RelativeHalfBraiding.tensor_β_hom]
  calc
    _ = 𝟙 _ ⊗≫ (f.f ▷ (Y.obj ⊗ F.obj U) ≫ X₂.obj ◁ (Y.halfBraiding.β U).hom) ⊗≫
          (X₂.halfBraiding.β U).hom ▷ Y.obj ⊗≫ 𝟙 _ := by
      monoidal
    _ = 𝟙 _ ⊗≫ X₁.obj ◁ (Y.halfBraiding.β U).hom ⊗≫
          (f.f ▷ F.obj U ≫ (X₂.halfBraiding.β U).hom) ▷ Y.obj ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; monoidal
    _ = _ := by rw [f.comm]; monoidal

/-- Auxiliary definition for the `MonoidalCategory` instance on the centre of `F`. -/
def whiskerRight {X₁ X₂ : F.RelativeCenter} (f : X₁ ⟶ X₂) (Y : F.RelativeCenter) :
    tensorObj X₁ Y ⟶ tensorObj X₂ Y where
  f := f.f ▷ Y.obj
  comm U := whiskerRight_comm f Y U

/-- Auxiliary definition for the `MonoidalCategory` instance on the centre of `F`. -/
def tensorHom {X₁ Y₁ X₂ Y₂ : F.RelativeCenter} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂ where
  f := f.f ⊗ₘ g.f
  comm U := by
    rw [tensorHom_def, comp_whiskerRight_assoc, whiskerLeft_comm, whiskerRight_comm_assoc,
      MonoidalCategory.whiskerLeft_comp]

/-- Auxiliary definition for the `MonoidalCategory` instance on the centre of `F`: the unit
object `𝟙_ D`, with the half-braiding `RelativeHalfBraiding.tensorUnit`. -/
abbrev tensorUnit : F.RelativeCenter :=
  ⟨𝟙_ D, RelativeHalfBraiding.tensorUnit F⟩

/-- Auxiliary definition for the `MonoidalCategory` instance on the centre of `F`. -/
def associator (X Y Z : F.RelativeCenter) :
    tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) where
  hom := ⟨(α_ X.obj Y.obj Z.obj).hom, fun U ↦ by
    simp only [RelativeHalfBraiding.tensor_β_hom]; monoidal⟩
  inv := ⟨(α_ X.obj Y.obj Z.obj).inv, fun U ↦ by
    simp only [RelativeHalfBraiding.tensor_β_hom]; monoidal⟩
  hom_inv_id := by ext; exact (α_ X.obj Y.obj Z.obj).hom_inv_id
  inv_hom_id := by ext; exact (α_ X.obj Y.obj Z.obj).inv_hom_id

/-- Auxiliary definition for the `MonoidalCategory` instance on the centre of `F`. -/
def leftUnitor (X : F.RelativeCenter) : tensorObj tensorUnit X ≅ X where
  hom := ⟨(λ_ X.obj).hom, fun U ↦ by
    simp only [RelativeHalfBraiding.tensor_β_hom, RelativeHalfBraiding.tensorUnit_β_hom]
    monoidal⟩
  inv := ⟨(λ_ X.obj).inv, fun U ↦ by
    simp only [RelativeHalfBraiding.tensor_β_hom, RelativeHalfBraiding.tensorUnit_β_hom]
    monoidal⟩
  hom_inv_id := by ext; exact (λ_ X.obj).hom_inv_id
  inv_hom_id := by ext; exact (λ_ X.obj).inv_hom_id

/-- Auxiliary definition for the `MonoidalCategory` instance on the centre of `F`. -/
def rightUnitor (X : F.RelativeCenter) : tensorObj X tensorUnit ≅ X where
  hom := ⟨(ρ_ X.obj).hom, fun U ↦ by
    simp only [RelativeHalfBraiding.tensor_β_hom, RelativeHalfBraiding.tensorUnit_β_hom]
    monoidal⟩
  inv := ⟨(ρ_ X.obj).inv, fun U ↦ by
    simp only [RelativeHalfBraiding.tensor_β_hom, RelativeHalfBraiding.tensorUnit_β_hom]
    monoidal⟩
  hom_inv_id := by ext; exact (ρ_ X.obj).hom_inv_id
  inv_hom_id := by ext; exact (ρ_ X.obj).inv_hom_id

section

attribute [local simp] associator_naturality leftUnitor_naturality rightUnitor_naturality pentagon

attribute [local simp] RelativeCenter.associator RelativeCenter.leftUnitor
  RelativeCenter.rightUnitor RelativeCenter.whiskerLeft RelativeCenter.whiskerRight
  RelativeCenter.tensorHom

/-- The centre of a lax monoidal functor is a monoidal category, with tensor product, unit and
structure isomorphisms computed in the target. -/
instance : MonoidalCategory F.RelativeCenter where
  tensorObj X Y := tensorObj X Y
  tensorHom f g := tensorHom f g
  tensorHom_def := by intros; ext; simp [tensorHom_def]
  whiskerLeft X _ _ f := whiskerLeft X f
  whiskerRight f Y := whiskerRight f Y
  tensorUnit := tensorUnit
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

end

@[simp]
theorem tensor_obj (X Y : F.RelativeCenter) : (X ⊗ Y).obj = X.obj ⊗ Y.obj :=
  rfl

@[simp]
theorem tensor_halfBraiding (X Y : F.RelativeCenter) :
    (X ⊗ Y).halfBraiding = X.halfBraiding.tensor Y.halfBraiding :=
  rfl

@[simp]
theorem whiskerLeft_f (X : F.RelativeCenter) {Y₁ Y₂ : F.RelativeCenter} (f : Y₁ ⟶ Y₂) :
    (X ◁ f).f = X.obj ◁ f.f :=
  rfl

@[simp]
theorem whiskerRight_f {X₁ X₂ : F.RelativeCenter} (f : X₁ ⟶ X₂) (Y : F.RelativeCenter) :
    (f ▷ Y).f = f.f ▷ Y.obj :=
  rfl

@[simp]
theorem tensor_f {X₁ Y₁ X₂ Y₂ : F.RelativeCenter} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g).f = f.f ⊗ₘ g.f :=
  rfl

@[simp]
theorem tensorUnit_obj : (𝟙_ F.RelativeCenter).obj = 𝟙_ D :=
  rfl

@[simp]
theorem tensorUnit_halfBraiding :
    (𝟙_ F.RelativeCenter).halfBraiding = RelativeHalfBraiding.tensorUnit F :=
  rfl

@[simp]
theorem associator_hom_f (X Y Z : F.RelativeCenter) :
    Hom.f (α_ X Y Z).hom = (α_ X.obj Y.obj Z.obj).hom :=
  rfl

@[simp]
theorem associator_inv_f (X Y Z : F.RelativeCenter) :
    Hom.f (α_ X Y Z).inv = (α_ X.obj Y.obj Z.obj).inv :=
  rfl

@[simp]
theorem leftUnitor_hom_f (X : F.RelativeCenter) : Hom.f (λ_ X).hom = (λ_ X.obj).hom :=
  rfl

@[simp]
theorem leftUnitor_inv_f (X : F.RelativeCenter) : Hom.f (λ_ X).inv = (λ_ X.obj).inv :=
  rfl

@[simp]
theorem rightUnitor_hom_f (X : F.RelativeCenter) : Hom.f (ρ_ X).hom = (ρ_ X.obj).hom :=
  rfl

@[simp]
theorem rightUnitor_inv_f (X : F.RelativeCenter) : Hom.f (ρ_ X).inv = (ρ_ X.obj).inv :=
  rfl

section

variable (F)

/-- The forgetful functor from the centre of `F` to the target of `F`. -/
@[simps]
def forget : F.RelativeCenter ⥤ D where
  obj X := X.obj
  map f := f.f

/-- The forgetful functor from the centre of `F` is monoidal, with identity tensorator and unit. -/
instance : (forget F).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _
      μIso_hom_natural_left _ _ := (Category.comp_id _).trans (Category.id_comp _).symm
      μIso_hom_natural_right _ _ := (Category.comp_id _).trans (Category.id_comp _).symm
      -- The remaining laws are those of `D`, up to the identity tensorator and unit, whose
      -- whiskerings are only identities up to unfolding `forget`.
      associativity X Y Z := by
        have h : 𝟙 _ ▷ Z.obj ≫ 𝟙 _ ≫ (α_ X.obj Y.obj Z.obj).hom =
            (α_ X.obj Y.obj Z.obj).hom ≫ X.obj ◁ 𝟙 _ ≫ 𝟙 _ := by
          simp
        exact h
      left_unitality X := by
        have h : (λ_ X.obj).hom = 𝟙 (𝟙_ D) ▷ X.obj ≫ 𝟙 _ ≫ (λ_ X.obj).hom := by simp
        exact h
      right_unitality X := by
        have h : (ρ_ X.obj).hom = X.obj ◁ 𝟙 (𝟙_ D) ≫ 𝟙 _ ≫ (ρ_ X.obj).hom := by simp
        exact h }

@[simp] lemma forget_ε : ε (forget F) = 𝟙 _ := rfl
@[simp] lemma forget_η : OplaxMonoidal.η (forget F) = 𝟙 _ := rfl

variable {F}

@[simp] lemma forget_μ (X Y : F.RelativeCenter) : μ (forget F) X Y = 𝟙 _ := rfl
@[simp] lemma forget_δ (X Y : F.RelativeCenter) : OplaxMonoidal.δ (forget F) X Y = 𝟙 _ := rfl

/-- The forgetful functor from the centre of `F` is faithful. -/
instance : (forget F).Faithful where
  map_injective h := ext _ _ h

/-- The forgetful functor from the centre of `F` reflects isomorphisms. -/
instance : (forget F).ReflectsIsomorphisms where
  reflects f i := by
    have : IsIso f.f := i
    exact isIso_of_f_isIso f

end

end RelativeCenter

end Functor

end CategoryTheory

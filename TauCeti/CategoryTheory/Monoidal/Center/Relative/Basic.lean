/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# The centre of a lax monoidal functor

Let `F : C ⥤ D` be a lax monoidal functor between monoidal categories. A half-braiding relative
to `F` on an object `X : D` is a family of isomorphisms `β U : X ⊗ F.obj U ≅ F.obj U ⊗ X`,
natural in `U : C`, which is compatible with the tensorator `μ` and the unit `ε` of `F`: applying
`μ` and then moving `X` past `F.obj (U ⊗ U')` agrees with moving `X` past `F.obj U` and then past
`F.obj U'` and then applying `μ`, and applying `ε` and then moving `X` past `F.obj (𝟙_ C)` agrees,
up to unitors, with applying `ε` on the other side of `X`. Since `μ` and `ε` need not be
invertible, these laws only constrain the half-braiding after precomposition with them. The
centre `Functor.RelativeCenter F` of `F` (the relative centre `Z(F)` of
Gainutdinov–Haferkamp–Schweigert) has as objects the pairs of an object of `D` and a half-braiding
relative to `F` on it, and as morphisms the morphisms of `D` commuting with the half-braidings.

For `F` the identity functor the half-braidings relative to `F` are Mathlib's `HalfBraiding`s,
which satisfy the compatibility with the unit automatically. For a lax monoidal functor whose unit
`ε` is not invertible, this compatibility is an additional condition.

Following Mathlib's `Center`, this file makes `Functor.RelativeCenter F` a monoidal category,
with tensor product computed in `D`: the half-braiding `RelativeHalfBraiding.tensor` of `X ⊗ Y`
moves `Y` and then `X`, and the unit is `𝟙_ D` with the half-braiding
`RelativeHalfBraiding.tensorUnit` given by the unitors. The coherence laws are transported along
the faithful forgetful functor `Functor.RelativeCenter.forget F` to `D` with
`Monoidal.induced`, which also makes this functor monoidal, with identity tensorator and unit;
it reflects isomorphisms. Nothing here uses rigidity, linearity or a strong monoidal
structure on `F`.

The relative centre is where the coefficients of Davydov–Yetter cohomology of a tensor functor
live; for fusion categories of nonzero global dimension the vanishing of this cohomology in
positive degrees is Ocneanu rigidity.

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

public section

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
  /-- Applying the tensorator `μ` and then moving `X` past `F.obj (U ⊗ U')` agrees with moving `X`
  past `F.obj U` and then past `F.obj U'` and then applying `μ`. -/
  monoidal : ∀ U U', X ◁ μ F U U' ≫ (β (U ⊗ U')).hom =
      (α_ _ _ _).inv ≫ (β U).hom ▷ F.obj U' ≫ (α_ _ _ _).hom ≫ F.obj U ◁ (β U').hom ≫
        (α_ _ _ _).inv ≫ μ F U U' ▷ X := by
    cat_disch
  /-- Applying the unit `ε` and then moving `X` past `F.obj (𝟙_ C)` agrees, up to unitors, with
  applying `ε` on the other side of `X`. -/
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

/-- Two half-braidings relative to `F` on the same object agree if their components do. -/
@[ext]
theorem ext {X : D} {b b' : F.RelativeHalfBraiding X} (h : ∀ U, (b.β U).hom = (b'.β U).hom) :
    b = b' := by
  obtain ⟨β, _, _, _⟩ := b
  obtain ⟨β', _, _, _⟩ := b'
  obtain rfl : β = β' := funext fun U ↦ Iso.ext (h U)
  rfl

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
  (rfl)

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
  (rfl)

@[simp]
theorem tensorUnit_β_inv (U : C) :
    ((tensorUnit F).β U).inv = (ρ_ (F.obj U)).hom ≫ (λ_ (F.obj U)).inv :=
  (rfl)

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

/-- An isomorphism in the centre of `F` built from an isomorphism of the underlying objects whose
forward map commutes with the half-braidings; its inverse is `e.inv`. -/
@[expose, simps]
def isoMk {X Y : F.RelativeCenter} (e : X.obj ≅ Y.obj)
    (comm : ∀ U, e.hom ▷ F.obj U ≫ (Y.halfBraiding.β U).hom =
      (X.halfBraiding.β U).hom ≫ F.obj U ◁ e.hom) : X ≅ Y where
  hom := ⟨e.hom, comm⟩
  inv := ⟨e.inv, fun U ↦ (CommSq.horiz_inv (f := MonoidalCategory.whiskerRightIso e (F.obj U))
    (i := MonoidalCategory.whiskerLeftIso (F.obj U) e) ⟨comm U⟩).w⟩
  hom_inv_id := by ext; exact e.hom_inv_id
  inv_hom_id := by ext; exact e.inv_hom_id

instance isIso_of_f_isIso {X Y : F.RelativeCenter} (f : X ⟶ Y) [IsIso f.f] : IsIso f :=
  (isoMk (asIso f.f) f.comm).isIso_hom

section

variable (F)

/-- The forgetful functor from the centre of `F` to the target of `F`. -/
@[expose, simps]
def forget : F.RelativeCenter ⥤ D where
  obj X := X.obj
  map f := f.f

/-- The forgetful functor from the centre of `F` is faithful. -/
instance : (forget F).Faithful where
  map_injective h := ext _ _ h

/-- The forgetful functor from the centre of `F` reflects isomorphisms. -/
instance : (forget F).ReflectsIsomorphisms where
  reflects f i := by
    have : IsIso f.f := i
    exact isIso_of_f_isIso f

end

@[reassoc]
private theorem whiskerLeft_comm (X : F.RelativeCenter) {Y₁ Y₂ : F.RelativeCenter} (f : Y₁ ⟶ Y₂)
    (U : C) :
    (X.obj ◁ f.f) ▷ F.obj U ≫ ((X.halfBraiding.tensor Y₂.halfBraiding).β U).hom =
      ((X.halfBraiding.tensor Y₁.halfBraiding).β U).hom ≫ F.obj U ◁ X.obj ◁ f.f := by
  simp only [RelativeHalfBraiding.tensor_β_hom]
  calc
    _ = 𝟙 _ ⊗≫ X.obj ◁ (f.f ▷ F.obj U ≫ (Y₂.halfBraiding.β U).hom) ⊗≫
          (X.halfBraiding.β U).hom ▷ Y₂.obj ⊗≫ 𝟙 _ := by
      monoidal
    _ = 𝟙 _ ⊗≫ X.obj ◁ (Y₁.halfBraiding.β U).hom ⊗≫
          ((X.obj ⊗ F.obj U) ◁ f.f ≫ (X.halfBraiding.β U).hom ▷ Y₂.obj) ⊗≫ 𝟙 _ := by
      rw [f.comm]; monoidal
    _ = _ := by rw [whisker_exchange]; monoidal

@[reassoc]
private theorem whiskerRight_comm {X₁ X₂ : F.RelativeCenter} (f : X₁ ⟶ X₂) (Y : F.RelativeCenter)
    (U : C) :
    f.f ▷ Y.obj ▷ F.obj U ≫ ((X₂.halfBraiding.tensor Y.halfBraiding).β U).hom =
      ((X₁.halfBraiding.tensor Y.halfBraiding).β U).hom ≫ F.obj U ◁ f.f ▷ Y.obj := by
  simp only [RelativeHalfBraiding.tensor_β_hom]
  calc
    _ = 𝟙 _ ⊗≫ (f.f ▷ (Y.obj ⊗ F.obj U) ≫ X₂.obj ◁ (Y.halfBraiding.β U).hom) ⊗≫
          (X₂.halfBraiding.β U).hom ▷ Y.obj ⊗≫ 𝟙 _ := by
      monoidal
    _ = 𝟙 _ ⊗≫ X₁.obj ◁ (Y.halfBraiding.β U).hom ⊗≫
          (f.f ▷ F.obj U ≫ (X₂.halfBraiding.β U).hom) ▷ Y.obj ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; monoidal
    _ = _ := by rw [f.comm]; monoidal

/-- The monoidal operations on the centre of `F`, computed in the target: the tensor product of
the underlying objects carries the half-braiding `RelativeHalfBraiding.tensor`, and the unit `𝟙_ D`
carries `RelativeHalfBraiding.tensorUnit`. -/
instance : MonoidalCategoryStruct F.RelativeCenter where
  -- Instance bodies are exposed, so the private commutation lemmas enter through tactic proofs.
  tensorObj X Y := ⟨X.obj ⊗ Y.obj, X.halfBraiding.tensor Y.halfBraiding⟩
  whiskerLeft X _ _ f := ⟨X.obj ◁ f.f, by exact whiskerLeft_comm X f⟩
  whiskerRight f Y := ⟨f.f ▷ Y.obj, by exact whiskerRight_comm f Y⟩
  tensorHom f g := ⟨f.f ⊗ₘ g.f, fun U ↦ by
    rw [tensorHom_def, comp_whiskerRight_assoc, whiskerLeft_comm, whiskerRight_comm_assoc,
      MonoidalCategory.whiskerLeft_comp]⟩
  tensorUnit := ⟨𝟙_ D, RelativeHalfBraiding.tensorUnit F⟩
  associator X Y Z := isoMk (α_ X.obj Y.obj Z.obj) fun U ↦ by
    simp only [RelativeHalfBraiding.tensor_β_hom]; monoidal
  leftUnitor X := isoMk (λ_ X.obj) fun U ↦ by
    simp only [RelativeHalfBraiding.tensor_β_hom, RelativeHalfBraiding.tensorUnit_β_hom]
    monoidal
  rightUnitor X := isoMk (ρ_ X.obj) fun U ↦ by
    simp only [RelativeHalfBraiding.tensor_β_hom, RelativeHalfBraiding.tensorUnit_β_hom]
    monoidal

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

/-- The centre of a lax monoidal functor is a monoidal category, with tensor product, unit and
structure isomorphisms computed in the target. Its coherence laws are transported along the
faithful functor `forget F`, which preserves all the monoidal operations on the nose. -/
instance : MonoidalCategory F.RelativeCenter :=
  Monoidal.induced (forget F)
    { μIso _ _ := Iso.refl _
      εIso := Iso.refl _
      -- Each law holds by definition once the identity structure isomorphisms are cancelled. The
      -- objects `(forget F).obj X` and `X.obj` agree only up to unfolding `forget`, so the
      -- coherence laws are first restated in terms of `X.obj`, where `simp` can cancel the
      -- identities.
      whiskerLeft_eq _ _ _ _ := ((Category.id_comp _).trans (Category.comp_id _)).symm
      whiskerRight_eq _ _ := ((Category.id_comp _).trans (Category.comp_id _)).symm
      tensorHom_eq _ _ := ((Category.id_comp _).trans (Category.comp_id _)).symm
      associator_eq X Y Z := by
        change (α_ X.obj Y.obj Z.obj).hom =
          (𝟙 _ ≫ (𝟙 _ ⊗ₘ 𝟙 _)) ≫ (α_ X.obj Y.obj Z.obj).hom ≫ (𝟙 _ ⊗ₘ 𝟙 _) ≫ 𝟙 _
        simp
      leftUnitor_eq X := by
        change (λ_ X.obj).hom = (𝟙 _ ≫ (𝟙 _ ⊗ₘ 𝟙 _)) ≫ (λ_ X.obj).hom
        simp
      rightUnitor_eq X := by
        change (ρ_ X.obj).hom = (𝟙 _ ≫ (𝟙 _ ⊗ₘ 𝟙 _)) ≫ (ρ_ X.obj).hom
        simp }

section

variable (F)

/-- The forgetful functor from the centre of `F` is monoidal, with identity tensorator and unit. -/
instance : (forget F).Monoidal :=
  -- The transport data is recovered by unification with the `MonoidalCategory` instance above.
  Monoidal.fromInducedMonoidal (forget F) _

@[simp] lemma forget_ε : ε (forget F) = 𝟙 _ := rfl
@[simp] lemma forget_η : OplaxMonoidal.η (forget F) = 𝟙 _ := rfl

variable {F}

@[simp] lemma forget_μ (X Y : F.RelativeCenter) : μ (forget F) X Y = 𝟙 _ := rfl
@[simp] lemma forget_δ (X Y : F.RelativeCenter) : OplaxMonoidal.δ (forget F) X Y = 𝟙 _ := rfl

end

end RelativeCenter

end Functor

end CategoryTheory

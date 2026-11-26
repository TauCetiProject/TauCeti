/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.SingleObj

/-!
# Pointwise algebraic structures on functors to a single-object category

For a category `C` and a commutative monoid `M`, functors `C ⥤ SingleObj M` form a commutative
monoid under pointwise multiplication (`(F * G).map f = F.map f * G.map f`, which respects
composition in `SingleObj M` where `a ≫ b = b * a`). When `M` is a commutative group,
`C ⥤ SingleObj M` is a commutative group (in particular, `A`-valued groupoid characters when `C` is
a groupoid).

## Main declarations

* `CategoryTheory.SingleObj.eqToHom_as_one`: every equality morphism in `SingleObj M` is `1`.
* `CategoryTheory.SingleObj.isIso_iff_isUnit`: a morphism in `SingleObj M` is an isomorphism
  if and only if it is a unit in `M`.
* `CategoryTheory.SingleObj.functor_ext`: extensionality on morphisms for `C ⥤ SingleObj M`.
* `CategoryTheory.SingleObj.functorOne`, `functorCommMonoid`, `functorCommGroup`: pointwise
  `One`, `CommMonoid`, and `CommGroup` instances on `C ⥤ SingleObj M`.
* `CategoryTheory.SingleObj.whiskerRightMonoidHom`: postcomposition by `SingleObj.mapHom M N φ` as
  a `MonoidHom`.
-/

public section

universe v₁ u₁ w₁ w₂

namespace CategoryTheory.SingleObj

section Monoid

variable {C : Type u₁} [Category.{v₁} C] {M : Type w₁} [Monoid M]

/-- Every equality morphism in `SingleObj M` is `1`. -/
theorem eqToHom_as_one {x y : SingleObj M} (p : x = y) :
    (eqToHom p : x ⟶ y) = (1 : M) := by cases p; rfl

/-- A morphism in `SingleObj M` is an isomorphism if and only if it is a unit in `M`. -/
theorem isIso_iff_isUnit {x y : SingleObj M} (f : x ⟶ y) :
    IsIso f ↔ IsUnit (f : M) :=
  (CategoryTheory.isUnit_iff_isIso (toEnd M (f : M))).symm.trans (MulEquiv.isUnit_map (toEnd M))

/-- Two functors into `SingleObj M` are equal if they agree on every morphism. -/
@[ext 1100] theorem functor_ext {F G : C ⥤ SingleObj M}
    (h : ∀ {X Y : C} (f : X ⟶ Y), F.map f = G.map f) : F = G :=
  CategoryTheory.Functor.ext (fun _ ↦ rfl) fun _ _ f ↦ by simpa using h f

/-- The trivial functor `C ⥤ SingleObj M`, sending every morphism to `1`. -/
instance functorOne : One (C ⥤ SingleObj M) where
  one := { obj := fun _ ↦ SingleObj.star M, map := fun _ ↦ (1 : M)
           map_id := fun _ ↦ rfl, map_comp := fun _ _ ↦ (one_mul (1 : M)).symm }

@[simp] theorem functor_one_obj (X : C) : (1 : C ⥤ SingleObj M).obj X = SingleObj.star M := (rfl)
@[simp] theorem functor_one_map {X Y : C} (f : X ⟶ Y) :
    (1 : C ⥤ SingleObj M).map f = (1 : M) := (rfl)

end Monoid

section CommMonoid

variable {C : Type u₁} [Category.{v₁} C] {M : Type w₁} [CommMonoid M]

/-- Pointwise multiplication of functors into `SingleObj M` for a commutative monoid `M`. -/
instance functorMul : Mul (C ⥤ SingleObj M) where
  mul F G := { obj := fun _ ↦ SingleObj.star M, map := fun f ↦ (F.map f : M) * (G.map f : M)
               map_id := fun _ ↦ by simp [SingleObj.id_as_one]
               map_comp := fun _ _ ↦ by simp [SingleObj.comp_as_mul, mul_mul_mul_comm] }
@[simp] theorem functor_mul_obj (F G : C ⥤ SingleObj M) (X : C) :
    (F * G).obj X = SingleObj.star M := (rfl)
@[simp] theorem functor_mul_map (F G : C ⥤ SingleObj M) {X Y : C} (f : X ⟶ Y) :
    (F * G).map f = (F.map f : M) * (G.map f : M) := (rfl)

/-- Pointwise natural-number powers of functors into `SingleObj M`. -/
instance functorNatPow : Pow (C ⥤ SingleObj M) ℕ where
  pow F n := { obj := fun _ ↦ SingleObj.star M, map := fun f ↦ (F.map f : M) ^ n
               map_id := fun _ ↦ by simp [SingleObj.id_as_one]
               map_comp := fun _ _ ↦ by simp [SingleObj.comp_as_mul, mul_pow] }
@[simp] theorem functor_pow_obj (F : C ⥤ SingleObj M) (n : ℕ) (X : C) :
    (F ^ n).obj X = SingleObj.star M := (rfl)
@[simp] theorem functor_pow_map (F : C ⥤ SingleObj M) (n : ℕ) {X Y : C} (f : X ⟶ Y) :
    (F ^ n).map f = (F.map f : M) ^ n := (rfl)

instance functorCommMonoid : CommMonoid (C ⥤ SingleObj M) where
  mul_assoc _ _ _ := functor_ext fun _ ↦ mul_assoc _ _ _
  one_mul _ := functor_ext fun _ ↦ one_mul _
  mul_one _ := functor_ext fun _ ↦ mul_one _
  npow n F := F ^ n
  npow_zero _ := functor_ext fun _ ↦ pow_zero _
  npow_succ _ _ := functor_ext fun _ ↦ pow_succ _ _
  mul_comm _ _ := functor_ext fun _ ↦ mul_comm _ _

/-- Postcomposing functors into `SingleObj M` with `SingleObj.mapHom M N φ` as a monoid
homomorphism `(C ⥤ SingleObj M) →* (C ⥤ SingleObj N)`. -/
def whiskerRightMonoidHom {N : Type w₂} [CommMonoid N] (φ : M →* N) :
    (C ⥤ SingleObj M) →* (C ⥤ SingleObj N) where
  toFun F := F ⋙ SingleObj.mapHom M N φ
  map_one' := functor_ext fun _ ↦ φ.map_one
  map_mul' _ _ := functor_ext fun _ ↦ φ.map_mul _ _
@[simp] theorem whiskerRightMonoidHom_apply {N : Type w₂} [CommMonoid N] (φ : M →* N)
    (F : C ⥤ SingleObj M) : whiskerRightMonoidHom φ F = F ⋙ SingleObj.mapHom M N φ := (rfl)
@[simp] theorem whiskerRightMonoidHom_apply_map {N : Type w₂} [CommMonoid N] (φ : M →* N)
    (F : C ⥤ SingleObj M) {X Y : C} (f : X ⟶ Y) :
    (whiskerRightMonoidHom φ F).map f = φ (F.map f) := (rfl)

end CommMonoid

section CommGroup

variable {C : Type u₁} [Category.{v₁} C] {G : Type w₁} [CommGroup G]

/-- Pointwise inversion of functors into `SingleObj G` for a commutative group `G`. -/
instance functorInv : Inv (C ⥤ SingleObj G) where
  inv F := { obj := fun _ ↦ SingleObj.star G, map := fun f ↦ (F.map f : G)⁻¹
             map_id := fun _ ↦ by simp [SingleObj.id_as_one]
             map_comp := fun _ _ ↦ by simp [SingleObj.comp_as_mul, mul_comm] }
@[simp] theorem functor_inv_obj (F : C ⥤ SingleObj G) (X : C) :
    F⁻¹.obj X = SingleObj.star G := (rfl)
@[simp] theorem functor_inv_map (F : C ⥤ SingleObj G) {X Y : C} (f : X ⟶ Y) :
    F⁻¹.map f = (F.map f : G)⁻¹ := (rfl)

/-- Pointwise division of functors into `SingleObj G` for a commutative group `G`. -/
instance functorDiv : Div (C ⥤ SingleObj G) where
  div F H := { obj := fun _ ↦ SingleObj.star G, map := fun f ↦ (F.map f : G) / (H.map f : G)
               map_id := fun _ ↦ by simp [SingleObj.id_as_one]
               map_comp := fun _ _ ↦ by simp [SingleObj.comp_as_mul, mul_div_mul_comm] }
@[simp] theorem functor_div_obj (F H : C ⥤ SingleObj G) (X : C) :
    (F / H).obj X = SingleObj.star G := (rfl)
@[simp] theorem functor_div_map (F H : C ⥤ SingleObj G) {X Y : C} (f : X ⟶ Y) :
    (F / H).map f = (F.map f : G) / (H.map f : G) := (rfl)

/-- Pointwise integer powers of functors into `SingleObj G` for a commutative group `G`. -/
instance functorIntPow : Pow (C ⥤ SingleObj G) ℤ where
  pow F n := { obj := fun _ ↦ SingleObj.star G, map := fun f ↦ (F.map f : G) ^ n
               map_id := fun _ ↦ by simp [SingleObj.id_as_one]
               map_comp := fun _ _ ↦ by simp [SingleObj.comp_as_mul, mul_zpow] }
@[simp] theorem functor_zpow_obj (F : C ⥤ SingleObj G) (n : ℤ) (X : C) :
    (F ^ n).obj X = SingleObj.star G := (rfl)
@[simp] theorem functor_zpow_map (F : C ⥤ SingleObj G) (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    (F ^ n).map f = (F.map f : G) ^ n := (rfl)

instance functorCommGroup : CommGroup (C ⥤ SingleObj G) where
  zpow n F := F ^ n
  zpow_zero' _ := functor_ext fun _ ↦ zpow_zero _
  zpow_succ' n F := functor_ext fun f ↦ DivInvMonoid.zpow_succ' n (F.map f)
  zpow_neg' n F := functor_ext fun f ↦ DivInvMonoid.zpow_neg' n (F.map f)
  div_eq_mul_inv _ _ := functor_ext fun _ ↦ div_eq_mul_inv _ _
  inv_mul_cancel _ := functor_ext fun _ ↦ inv_mul_cancel _

end CommGroup

end CategoryTheory.SingleObj

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Groupoid.VertexGroup
public import Mathlib.CategoryTheory.SingleObj

/-!
# One-object categories: opposite monoids, essential smallness, and pointwise functor structures

For a monoid `M`, the one-object category `SingleObj M` has the elements of `M` as endomorphisms
of its object `∗`, composed by `f ≫ g = g * f`. Reversing the multiplication is the same as
reversing the composition: `SingleObj Mᵐᵒᵖ` is isomorphic to the opposite category
`(SingleObj M)ᵒᵖ`, a morphism `op a` going to `a.op`. The category `SingleObj M` is also
essentially small as soon as `M` is small, since it has one object. For a group `G`, the vertex
group of `SingleObj Gᵐᵒᵖ` is identified with `G` (`CategoryTheory.SingleObj.vertexGroupOpMulEquiv`).

For a category `C` and a commutative monoid `M`, functors `C ⥤ SingleObj M` form a commutative
monoid under pointwise multiplication (`(F * G).map f = F.map f * G.map f`, which respects
composition in `SingleObj M` where `a ≫ b = b * a`). When `M` is a commutative group,
`C ⥤ SingleObj M` is a commutative group (in particular, `A`-valued groupoid characters when `C` is
a groupoid).

## Main declarations

* `CategoryTheory.SingleObj.mulOppositeEquiv M : SingleObj Mᵐᵒᵖ ≌ (SingleObj M)ᵒᵖ`, with the
  computation lemmas `mulOppositeEquiv_functor_obj`, `mulOppositeEquiv_functor_map`,
  `mulOppositeEquiv_inverse_obj` and `mulOppositeEquiv_inverse_map`.
* The instance `EssentiallySmall.{w} (SingleObj M)` for a `w`-small monoid `M`.
* `CategoryTheory.SingleObj.eqToHom_as_one`: every equality morphism in `SingleObj M` is `1`.
* `CategoryTheory.SingleObj.isIso_iff_isUnit`: a morphism in `SingleObj M` is an isomorphism
  if and only if it is a unit in `M`.
* `CategoryTheory.SingleObj.vertexGroupOpMulEquiv`: group isomorphism identifying the vertex
  group of `SingleObj Gᵐᵒᵖ` with `G`.
* `CategoryTheory.SingleObj.functor_ext`: extensionality on morphisms for `C ⥤ SingleObj M`.
* `CategoryTheory.SingleObj.functorOne`, `functorCommMonoid`, `functorCommGroup`: pointwise
  `One`, `CommMonoid`, and `CommGroup` instances on `C ⥤ SingleObj M`.
* `CategoryTheory.SingleObj.whiskerRightMonoidHom`: postcomposition by `SingleObj.mapHom M N φ` as
  a `MonoidHom`.
-/

public section

universe v₁ u₁ w w₁ w₂

namespace CategoryTheory.SingleObj

section Opposite

open Opposite

variable (M : Type*) [Monoid M]

/-- The isomorphism of categories `SingleObj Mᵐᵒᵖ ≌ (SingleObj M)ᵒᵖ`: a morphism `op a` goes to
`a.op`. -/
def mulOppositeEquiv : SingleObj Mᵐᵒᵖ ≌ (SingleObj M)ᵒᵖ where
  functor :=
    { obj _ := op (SingleObj.star M)
      map f := Quiver.Hom.op (X := SingleObj.star M) (Y := SingleObj.star M) (MulOpposite.unop f)
      map_id _ := rfl
      map_comp _ _ := rfl }
  inverse :=
    { obj _ := SingleObj.star Mᵐᵒᵖ
      map f := (MulOpposite.op f.unop : Mᵐᵒᵖ)
      map_id _ := rfl
      map_comp _ _ := rfl }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

variable {M}

/-- The functor of `mulOppositeEquiv M` sends the object to `op ∗`. -/
@[simp]
theorem mulOppositeEquiv_functor_obj (X : SingleObj Mᵐᵒᵖ) :
    (mulOppositeEquiv M).functor.obj X = op (SingleObj.star M) :=
  (rfl)

/-- The functor of `mulOppositeEquiv M` sends `op a` to `a.op`. -/
@[simp]
theorem mulOppositeEquiv_functor_map {X Y : SingleObj Mᵐᵒᵖ} (f : X ⟶ Y) :
    (mulOppositeEquiv M).functor.map f =
      Quiver.Hom.op (X := SingleObj.star M) (Y := SingleObj.star M) (MulOpposite.unop f) :=
  (rfl)

/-- The inverse of `mulOppositeEquiv M` sends the object to `∗`. -/
@[simp]
theorem mulOppositeEquiv_inverse_obj (X : (SingleObj M)ᵒᵖ) :
    (mulOppositeEquiv M).inverse.obj X = SingleObj.star Mᵐᵒᵖ :=
  (rfl)

/-- The inverse of `mulOppositeEquiv M` sends `a.op` to `op a`. -/
@[simp]
theorem mulOppositeEquiv_inverse_map {X Y : (SingleObj M)ᵒᵖ} (f : X ⟶ Y) :
    (mulOppositeEquiv M).inverse.map f = (MulOpposite.op f.unop : Mᵐᵒᵖ) :=
  (rfl)

/-- A one-object category is essentially small as soon as its endomorphism monoid is small. -/
instance [Small.{w} M] : EssentiallySmall.{w} (SingleObj M) :=
  have : Small.{w} (SingleObj M) := inferInstanceAs (Small.{w} Unit)
  have : LocallySmall.{w} (SingleObj M) := ⟨fun _ _ ↦ inferInstanceAs (Small.{w} M)⟩
  essentiallySmall_of_small_of_locallySmall _

end Opposite

section Monoid

variable {C : Type u₁} [Category.{v₁} C] {M : Type w₁} [Monoid M]

/-- Every equality morphism in `SingleObj M` is `1`. -/
theorem eqToHom_as_one {x y : SingleObj M} (p : x = y) :
    (eqToHom p : x ⟶ y) = (1 : M) := by cases p; rfl

/-- A morphism in `SingleObj M` is an isomorphism if and only if it is a unit in `M`. -/
theorem isIso_iff_isUnit {x y : SingleObj M} (f : x ⟶ y) :
    IsIso f ↔ IsUnit (f : M) :=
  (CategoryTheory.isUnit_iff_isIso (toEnd M (f : M))).symm.trans (MulEquiv.isUnit_map (toEnd M))

/-- The vertex group of `SingleObj Gᵐᵒᵖ` at its unique object is canonically isomorphic to `G`. -/
def vertexGroupOpMulEquiv (G : Type*) [Group G] :
    (SingleObj.star Gᵐᵒᵖ ⟶ SingleObj.star Gᵐᵒᵖ) ≃* G where
  toFun m := MulOpposite.unop m
  invFun g := MulOpposite.op g
  left_inv := MulOpposite.op_unop
  right_inv := MulOpposite.unop_op
  map_mul' _ _ := by
    rw [Groupoid.vertexGroup_mul, SingleObj.comp_as_mul, MulOpposite.unop_mul]

/-- `vertexGroupOpMulEquiv` acts by `MulOpposite.unop`. -/
@[simp] theorem vertexGroupOpMulEquiv_apply {G : Type*} [Group G]
    (m : SingleObj.star Gᵐᵒᵖ ⟶ SingleObj.star Gᵐᵒᵖ) :
    vertexGroupOpMulEquiv G m = MulOpposite.unop m := (rfl)

/-- The inverse of `vertexGroupOpMulEquiv` acts by `MulOpposite.op`. -/
@[simp] theorem vertexGroupOpMulEquiv_symm_apply {G : Type*} [Group G] (g : G) :
    (vertexGroupOpMulEquiv G).symm g = MulOpposite.op g := (rfl)

/-- Two functors into `SingleObj M` are equal if they agree on every morphism. -/
@[ext 1100] theorem functor_ext {F G : C ⥤ SingleObj M}
    (h : ∀ {X Y : C} (f : X ⟶ Y), F.map f = G.map f) : F = G :=
  CategoryTheory.Functor.ext (fun _ ↦ rfl) fun _ _ f ↦ by simpa using h f

/-- The trivial functor `C ⥤ SingleObj M`, sending every morphism to `1`. -/
instance functorOne : One (C ⥤ SingleObj M) where
  one := (Functor.const C).obj (SingleObj.star M)

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
  pow F n := F ⋙ SingleObj.mapHom M M (powMonoidHom n)
@[simp] theorem functor_pow_obj (F : C ⥤ SingleObj M) (n : ℕ) (X : C) :
    (F ^ n).obj X = SingleObj.star M := (rfl)
@[simp] theorem functor_pow_map (F : C ⥤ SingleObj M) (n : ℕ) {X Y : C} (f : X ⟶ Y) :
    (F ^ n).map f = (F.map f : M) ^ n := (rfl)

instance functorCommMonoid : CommMonoid (C ⥤ SingleObj M) where
  mul_assoc _ _ _ := functor_ext fun _ ↦ by simp only [functor_mul_map, mul_assoc]
  one_mul _ := functor_ext fun _ ↦ by simp only [functor_mul_map, functor_one_map, one_mul]
  mul_one _ := functor_ext fun _ ↦ by simp only [functor_mul_map, functor_one_map, mul_one]
  npow n F := F ^ n
  npow_zero _ := functor_ext fun _ ↦ by simp only [functor_pow_map, pow_zero, functor_one_map]
  npow_succ _ _ := functor_ext fun _ ↦ by
    simp only [functor_pow_map, functor_mul_map, pow_succ]
  mul_comm _ _ := functor_ext fun _ ↦ by simp only [functor_mul_map]; exact mul_comm _ _

/-- Postcomposing functors into `SingleObj M` with `SingleObj.mapHom M N φ` as a monoid
homomorphism `(C ⥤ SingleObj M) →* (C ⥤ SingleObj N)`. -/
def whiskerRightMonoidHom {N : Type w₂} [CommMonoid N] (φ : M →* N) :
    (C ⥤ SingleObj M) →* (C ⥤ SingleObj N) where
  toFun F := F ⋙ SingleObj.mapHom M N φ
  map_one' := functor_ext fun _ ↦ by
    simp only [Functor.comp_map, SingleObj.mapHom_apply_map, functor_one_map, map_one]
  map_mul' _ _ := functor_ext fun _ ↦ by
    simp only [Functor.comp_map, SingleObj.mapHom_apply_map, functor_mul_map, map_mul]
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
  inv F := F ⋙ SingleObj.mapHom G G invMonoidHom
@[simp] theorem functor_inv_obj (F : C ⥤ SingleObj G) (X : C) :
    F⁻¹.obj X = SingleObj.star G := (rfl)
@[simp] theorem functor_inv_map (F : C ⥤ SingleObj G) {X Y : C} (f : X ⟶ Y) :
    F⁻¹.map f = (F.map f : G)⁻¹ := (rfl)

/-- Pointwise division of functors into `SingleObj G` for a commutative group `G`. -/
instance functorDiv : Div (C ⥤ SingleObj G) where
  div F H := F * H⁻¹
/-- Pointwise division of functors into `SingleObj G` is multiplication by the pointwise
inverse. -/
theorem functor_div_eq_mul_inv (F H : C ⥤ SingleObj G) : F / H = F * H⁻¹ := (rfl)
@[simp] theorem functor_div_obj (F H : C ⥤ SingleObj G) (X : C) :
    (F / H).obj X = SingleObj.star G := (rfl)
@[simp] theorem functor_div_map (F H : C ⥤ SingleObj G) {X Y : C} (f : X ⟶ Y) :
    (F / H).map f = (F.map f : G) / (H.map f : G) := by
  rw [functor_div_eq_mul_inv]
  simp only [functor_mul_map, functor_inv_map, div_eq_mul_inv]

/-- Pointwise integer powers of functors into `SingleObj G` for a commutative group `G`. -/
instance functorIntPow : Pow (C ⥤ SingleObj G) ℤ where
  pow F n := F ⋙ SingleObj.mapHom G G (zpowGroupHom n)
@[simp] theorem functor_zpow_obj (F : C ⥤ SingleObj G) (n : ℤ) (X : C) :
    (F ^ n).obj X = SingleObj.star G := (rfl)
@[simp] theorem functor_zpow_map (F : C ⥤ SingleObj G) (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    (F ^ n).map f = (F.map f : G) ^ n := (rfl)

instance functorCommGroup : CommGroup (C ⥤ SingleObj G) where
  zpow n F := F ^ n
  zpow_zero' _ := functor_ext fun _ ↦ by simp only [functor_zpow_map, zpow_zero, functor_one_map]
  zpow_succ' _ _ := functor_ext fun _ ↦ by
    simp only [functor_zpow_map, functor_mul_map, zpow_natCast, Nat.succ_eq_add_one, pow_succ]
  zpow_neg' _ _ := functor_ext fun _ ↦ by
    simp only [functor_zpow_map, functor_inv_map, DivInvMonoid.zpow_neg']
  div_eq_mul_inv _ _ := functor_ext fun _ ↦ by
    simp only [functor_div_map, functor_mul_map, functor_inv_map, div_eq_mul_inv]
  inv_mul_cancel _ := functor_ext fun _ ↦ by
    simp only [functor_mul_map, functor_inv_map, inv_mul_cancel, functor_one_map]

end CommGroup

end CategoryTheory.SingleObj

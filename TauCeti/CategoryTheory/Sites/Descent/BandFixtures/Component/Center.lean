/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.CategoryTheory.Center.Basic
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.SingleObj

/-!
# The centre of a disjoint union of copies of a one-object groupoid

Let `G` be a commutative group and `I` a type. The groupoid `Discrete I × SingleObj G` is a
disjoint union, indexed by `I`, of copies of the one-object groupoid of `G`. A profile
`a : I → G` gives the central endomorphism of its identity functor acting by `a i` on the object
`(i, ⋆)` (`BandFixtures.componentCenter`); it is a unit of the categorical centre, with inverse the
pointwise inverse profile (`BandFixtures.componentCenterUnit`), and every centre unit arises from a
unique profile: the units of the centre are the profiles (`BandFixtures.componentCenterEquiv`).

These are the fibres of the constant pseudofunctors used to test central sections of gerbes: for
`I = Bool` the profile `(1, 2)` of `C₃` acts differently on the two components, so no single
coefficient represents it.

## Main definitions

In the namespace `CategoryTheory.Pseudofunctor.BandFixtures`:

* `componentCenter a`: the central endomorphism with component `(𝟙, a i)` at `(i, ⋆)`.
* `componentCenterUnit a`: the corresponding unit of the centre.
* `componentCenterEquiv I G : (I → G) ≃* (CatCenter (Discrete I × SingleObj G))ˣ`.

## References

* [The Stacks Project, Definition 8.11.1 (06NZ)](https://stacks.math.columbia.edu/tag/06NZ)
* [The Stacks Project, Lemma 8.11.8 (0CJY)](https://stacks.math.columbia.edu/tag/0CJY)
-/

public section

universe u v

open CategoryTheory

namespace CategoryTheory.Pseudofunctor.BandFixtures

variable {I : Type u} {G : Type v}

/-- A central endomorphism of `Discrete I × SingleObj G` is determined by its group components. -/
theorem catCenter_ext_discrete_prod_singleObj [Monoid G]
    {z w : CatCenter (Discrete I × SingleObj G)}
    (h : ∀ x : Discrete I × SingleObj G, (z.app x).2 = (w.app x).2) : z = w :=
  CatCenter.ext _ _ fun x ↦ Prod.hom_ext (Subsingleton.elim _ _) (h x)

section CommMonoid

variable [CommMonoid G]

/-- The **centre of a profile** `a : I → G`: the natural endomorphism of the identity of
`Discrete I × SingleObj G` with component `(𝟙, a i)` at an object over the label `i`. It is natural
because `G` is commutative. -/
def componentCenter (a : I → G) : CatCenter (Discrete I × SingleObj G) :=
  .of
    { app x := (𝟙 x.1, (a x.1.as : SingleObj.star G ⟶ SingleObj.star G))
      naturality x y f := by
        obtain ⟨⟨i⟩, ⟨⟩⟩ := x
        obtain ⟨⟨j⟩, ⟨⟩⟩ := y
        obtain rfl : i = j := Discrete.eq_of_hom f.1
        refine Prod.hom_ext (Subsingleton.elim _ _) ?_
        simp only [Functor.id_obj, Functor.id_map, prod_comp_snd, SingleObj.comp_as_mul]
        exact mul_comm _ _ }

/-- The component of the centre of a profile at an object over the label `i` is `(𝟙, a i)`. -/
theorem componentCenter_app (a : I → G) (x : Discrete I × SingleObj G) :
    (componentCenter a).app x = (𝟙 x.1, (a x.1.as : SingleObj.star G ⟶ SingleObj.star G)) :=
  (rfl)

/-- The group component of the centre of a profile at an object over `i` is `a i`. -/
@[simp]
theorem componentCenter_app_snd (a : I → G) (x : Discrete I × SingleObj G) :
    ((componentCenter a).app x).2 = (a x.1.as : SingleObj.star G ⟶ SingleObj.star G) :=
  (rfl)

/-- The centre of the pointwise product of profiles is the product of their centres. -/
@[simp]
theorem componentCenter_mul (a b : I → G) :
    componentCenter (a * b) = componentCenter a * componentCenter b :=
  catCenter_ext_discrete_prod_singleObj fun x ↦ by
    simp [CatCenter.mul_app', SingleObj.comp_as_mul]

/-- The centre of the trivial profile is the identity. -/
@[simp]
theorem componentCenter_one : componentCenter (1 : I → G) = 1 :=
  catCenter_ext_discrete_prod_singleObj fun _ ↦ by
    simp [CatCenter.app_one, SingleObj.id_as_one]

end CommMonoid

section CommGroup

variable [CommGroup G]

/-- The **centre unit of a profile** `a`, with inverse the centre of the pointwise inverse
profile. -/
def componentCenterUnit (a : I → G) : (CatCenter (Discrete I × SingleObj G))ˣ :=
  MonoidHom.toHomUnits
    { toFun := componentCenter, map_one' := componentCenter_one, map_mul' := componentCenter_mul } a

@[simp]
theorem val_componentCenterUnit (a : I → G) : (componentCenterUnit a).val = componentCenter a :=
  (rfl)

theorem val_inv_componentCenterUnit (a : I → G) :
    (componentCenterUnit a)⁻¹.val = componentCenter a⁻¹ :=
  (rfl)

/-- The inverse of the centre unit of a profile is the centre unit of the inverse profile. -/
@[simp]
theorem componentCenterUnit_inv (a : I → G) :
    (componentCenterUnit a)⁻¹ = componentCenterUnit a⁻¹ :=
  Units.ext (val_inv_componentCenterUnit a)

/-- The centre unit of the pointwise product of profiles is the product of their centre units. -/
@[simp]
theorem componentCenterUnit_mul (a b : I → G) :
    componentCenterUnit (a * b) = componentCenterUnit a * componentCenterUnit b :=
  Units.ext (componentCenter_mul a b)

/-- The centre unit of the trivial profile is the identity. -/
@[simp]
theorem componentCenterUnit_one : componentCenterUnit (1 : I → G) = 1 :=
  Units.ext componentCenter_one

variable (I G) in
/-- **The centre units of `Discrete I × SingleObj G` are the profiles** `I → G`, for a commutative
group `G`. The inverse reads the group component of a centre unit at each object `(i, ⋆)`. -/
def componentCenterEquiv : (I → G) ≃* (CatCenter (Discrete I × SingleObj G))ˣ where
  toFun := componentCenterUnit
  invFun z i := (z.val.app (⟨i⟩, SingleObj.star G)).2
  left_inv _ := rfl
  right_inv _ := Units.ext <| catCenter_ext_discrete_prod_singleObj fun ⟨⟨_⟩, ⟨⟩⟩ ↦ rfl
  map_mul' := componentCenterUnit_mul

@[simp]
theorem componentCenterEquiv_apply (a : I → G) :
    componentCenterEquiv I G a = componentCenterUnit a :=
  (rfl)

/-- The inverse of `componentCenterEquiv` reads the group component at `(i, ⋆)`. -/
@[simp]
theorem componentCenterEquiv_symm_apply (z : (CatCenter (Discrete I × SingleObj G))ˣ) (i : I) :
    (componentCenterEquiv I G).symm z i = (z.val.app (⟨i⟩, SingleObj.star G)).2 :=
  (rfl)

end CommGroup

end CategoryTheory.Pseudofunctor.BandFixtures

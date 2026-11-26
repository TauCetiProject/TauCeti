/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import TauCeti.CategoryTheory.Sites.Descent.Band.Center

/-!
# Central sections of a constant pseudofunctor

For a category `D`, the constant pseudofunctor `BandFixtures.constant C D` on `C` has every fibre
`D` and every pullback functor the identity (Mathlib's `Functor.toPseudofunctor'` of the constant
functor at `D`). A unit `z` of the categorical centre of `D` is then a central section over every
`U`, with value `z` at every arrow `V ⟶ U` (`BandFixtures.constantSection`), and every central
section is of this form: the units of the centre of `D` are the central sections over `U`
(`BandFixtures.constantSectionsEquiv`), the inverse evaluating a section at the identity of `U`.
Restriction along any arrow keeps the centre unit. No topology or terminal object is used.

## Main definitions

In the namespace `CategoryTheory.Pseudofunctor.BandFixtures`:

* `constant C D`: the constant pseudofunctor on `C` with fibre `D`.
* `constantSection U z`: the central section over `U` with value `z` at every arrow.
* `constantSectionsEquiv C D U : (CatCenter D)ˣ ≃* IntrinsicBandSections (constant C D) U`.

## Main results

* `constant_obj`, `constant_map`, `constant_mapId`, `constant_mapComp`: every fibre of
  `constant C D` is `D`, every pullback functor is the identity, and the unit and composition
  isomorphisms are identities.
* `val_constantSection`, `restrict_constantSection`: the value at every arrow is `z`, and
  restriction gives the constant section of the same `z`.
* `val_eq_val_id`: a central section has the same value at every arrow as at the identity.
* `constantSectionsEquiv_apply`, `constantSectionsEquiv_symm_apply`: the forward map is
  `constantSection`, the inverse is the value at the identity arrow.

## References

* [The Stacks Project, Lemma 8.11.8 (06NY)](https://stacks.math.columbia.edu/tag/06NY): the
  central sections `ZF(U)` computed here for the constant pseudofunctor are those of this lemma.
-/

public section

universe v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.BandFixtures

variable (C : Type u) [Category.{v} C] (D : Type u') [Category.{v'} D]

/-- The **constant pseudofunctor** on `C` with fibre `D`: every fibre is `D` and every pullback
functor is the identity. -/
@[expose]
def constant : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'} :=
  ((Functor.const Cᵒᵖ).obj (Cat.of D)).toPseudofunctor'

variable {C D}

-- Not `@[simp]`: `simp` would rewrite the fibre inside the types of central sections, so the
-- left-hand sides of `constantSectionsEquiv_apply` and similar lemmas would not be in normal form.
/-- The fibres of the constant pseudofunctor are `D`. -/
theorem constant_obj (X : LocallyDiscrete Cᵒᵖ) : (constant C D).obj X = Cat.of D :=
  rfl

/-- The pullback functors of the constant pseudofunctor are the identity. -/
@[simp]
theorem constant_map {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) :
    (constant C D).map f = 𝟙 (Cat.of D) :=
  rfl

/-- The unit isomorphisms of the constant pseudofunctor are identities. -/
@[simp]
theorem constant_mapId (X : LocallyDiscrete Cᵒᵖ) : (constant C D).mapId X = Iso.refl _ :=
  rfl

/-- The composition isomorphisms of the constant pseudofunctor are identities. -/
@[simp]
theorem constant_mapComp {X Y Z : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (constant C D).mapComp f g = Iso.refl _ :=
  rfl

/-- The **constant section** over `U` of a unit `z` of the centre of `D`: the central section of
the constant pseudofunctor with value `z` at every arrow `V ⟶ U`. -/
def constantSection (U : C) (z : (CatCenter D)ˣ) : IntrinsicBandSections (constant C D) U :=
  IntrinsicBandSections.ofCompatible (fun _ _ ↦ z)
    ((isPullbackCompatible_iff _).2 fun _ _ _ _ _ ↦ rfl)

/-- The value of a constant section at every arrow is its centre unit. -/
@[simp]
theorem val_constantSection (U : C) (z : (CatCenter D)ˣ) (V : C) (f : V ⟶ U) :
    (constantSection U z).val V f = z :=
  IntrinsicBandSections.val_ofCompatible _ _ V f

/-- Restriction of a constant section along any arrow is the constant section of the same
centre unit. -/
@[simp]
theorem restrict_constantSection {U V : C} (f : V ⟶ U) (z : (CatCenter D)ˣ) :
    IntrinsicBandSections.restrict f (constantSection U z) = constantSection V z :=
  IntrinsicBandSections.ext fun W a x ↦ by
    simp only [IntrinsicBandSections.val_restrict, val_constantSection]

/-- A central section of the constant pseudofunctor has the same value at every arrow `V ⟶ U` as
at the identity of `U`. -/
theorem val_eq_val_id {U : C} (s : IntrinsicBandSections (constant C D) U) {V : C} (f : V ⟶ U) :
    s.val V f = s.val U (𝟙 U) :=
  Units.ext <| CatCenter.ext _ _ fun x ↦ by
    have h := IntrinsicBandSections.map_app s (𝟙 U) f x
    rw [constant_map, Category.comp_id] at h
    -- `h` still applies `(𝟙 (Cat.of D)).toFunctor`, which is `𝟭 D` (`Cat.Hom.id_toFunctor`), but
    -- `rw` cannot remove it: `x` lies in the fibre `(constant C D).obj _`, which is `D` only by
    -- `constant_obj`, so `exact` closes the goal by unfolding
    exact h.symm

variable (C D) in
/-- **The central sections of a constant pseudofunctor** over `U` are the units of the centre of
its fibre: the forward map is `constantSection`, the inverse evaluates at the identity of `U`. -/
def constantSectionsEquiv (U : C) : (CatCenter D)ˣ ≃* IntrinsicBandSections (constant C D) U where
  toFun := constantSection U
  invFun s := s.val U (𝟙 U)
  left_inv z := val_constantSection U z U (𝟙 U)
  right_inv s := Subtype.ext <| funext₂ fun V f ↦
    (val_constantSection U _ V f).trans (val_eq_val_id s f).symm
  map_mul' z w := IntrinsicBandSections.ext fun V f x ↦ by
    simp only [IntrinsicBandSections.val_mul, val_constantSection]
    -- the two sides multiply `z` and `w` in `(CatCenter D)ˣ` and in the centre units of the fibre
    -- `(constant C D).obj _`, which is `D` by `constant_obj`
    rfl

@[simp]
theorem constantSectionsEquiv_apply (U : C) (z : (CatCenter D)ˣ) :
    constantSectionsEquiv C D U z = constantSection U z :=
  (rfl)

@[simp]
theorem constantSectionsEquiv_symm_apply (U : C) (s : IntrinsicBandSections (constant C D) U) :
    (constantSectionsEquiv C D U).symm s = s.val U (𝟙 U) :=
  (rfl)

end CategoryTheory.Pseudofunctor.BandFixtures

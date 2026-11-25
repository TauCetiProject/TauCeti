/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import TauCeti.CategoryTheory.Sites.Descent.BandCenter

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
* `constantSectionsEquiv U : (CatCenter D)ˣ ≃* IntrinsicBandSections (constant C D) U`.

## Main results

* `val_constantSection`, `restrict_constantSection`: the value at every arrow is `z`, and
  restriction gives the constant section of the same `z`.
* `constantSectionsEquiv_apply`, `constantSectionsEquiv_symm_apply`: the forward map is
  `constantSection`, the inverse is the value at the identity arrow.

## References

* [The Stacks Project, Definition 8.11.1 (06NZ)](https://stacks.math.columbia.edu/tag/06NZ)
* [The Stacks Project, Lemma 8.11.8 (0CJY)](https://stacks.math.columbia.edu/tag/0CJY)
-/

@[expose] public section

universe v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.BandFixtures

variable (C : Type u) [Category.{v} C] (D : Type u') [Category.{v'} D]

/-- The **constant pseudofunctor** on `C` with fibre `D`: every fibre is `D` and every pullback
functor is the identity. -/
def constant : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'} :=
  ((Functor.const Cᵒᵖ).obj (Cat.of D)).toPseudofunctor'

variable {C D}

/-- The fibres of the constant pseudofunctor are `D`. -/
theorem constant_obj (V : C) : (constant C D).obj (.mk (op V)) = Cat.of D :=
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

/-- The value at the identity arrow determines a central section of the constant pseudofunctor: by
compatibility with pullback along `f`, which is the identity functor, the value at `f` is the value
at the identity. -/
theorem val_eq_val_id {U : C} (s : IntrinsicBandSections (constant C D) U) {V : C} (f : V ⟶ U) :
    s.val V f = s.val U (𝟙 U) :=
  Units.ext <| CatCenter.ext _ _ fun x ↦ by
    have h := IntrinsicBandSections.map_app s (𝟙 U) f x
    rw [Category.comp_id] at h
    exact h.symm

variable (C D) in
/-- **The central sections of a constant pseudofunctor** over `U` are the units of the centre of
its fibre: the forward map is `constantSection`, the inverse evaluates at the identity of `U`. -/
def constantSectionsEquiv (U : C) : (CatCenter D)ˣ ≃* IntrinsicBandSections (constant C D) U where
  toFun := constantSection U
  invFun s := s.val U (𝟙 U)
  left_inv z := val_constantSection U z U (𝟙 U)
  right_inv s := IntrinsicBandSections.ext fun _ f _ ↦ by
    erw [val_constantSection, val_eq_val_id s f]
  map_mul' _ _ := IntrinsicBandSections.ext fun _ _ _ ↦ by
    simp only [val_constantSection, IntrinsicBandSections.val_mul]
    rfl

@[simp]
theorem constantSectionsEquiv_apply (U : C) (z : (CatCenter D)ˣ) :
    constantSectionsEquiv C D U z = constantSection U z :=
  rfl

@[simp]
theorem constantSectionsEquiv_symm_apply (U : C) (s : IntrinsicBandSections (constant C D) U) :
    (constantSectionsEquiv C D U).symm s = s.val U (𝟙 U) :=
  rfl

end CategoryTheory.Pseudofunctor.BandFixtures

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.OverClass
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Morphisms over a base into a fibre product over that base

Let `X` and `Y` be objects over `S`, and let `P` with projections `fst` and `snd` be a pullback of
their structure morphisms, itself over `S` so that `fst` is a morphism over `S`. For every object
`T` over `S`, the morphisms `T ⟶ P` over `S` are then exactly the pairs of morphisms `T ⟶ X` and
`T ⟶ Y` over `S`. This is the universal property of the fibre product in the `OverClass`
vocabulary, where morphisms over `S` are recorded by `HomIsOver` rather than as morphisms of the
bundled category `Over S`.

For schemes, with `T = Spec K` over `S = Spec K`, it says that the `K`-points of a fibre product
over `Spec K` are the pairs of `K`-points of the factors.

## Main declarations

* `CategoryTheory.homIsOver_snd_of_comm`: in a commuting square of two structure morphisms over
  `S`, the second projection is a morphism over `S` once the first one is.
* `CategoryTheory.IsPullback.homIsOverEquiv`: morphisms over `S` into the fibre product are pairs
  of morphisms over `S` into the factors.
-/

public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {S P X Y : C} [OverClass P S] [OverClass X S]
  [OverClass Y S] {fst : P ⟶ X} {snd : P ⟶ Y} [HomIsOver fst S]

/-- In a commuting square of two structure morphisms over `S`, the second projection is a
morphism over `S` once the first one is. -/
theorem homIsOver_snd_of_comm (h : fst ≫ (X ↘ S) = snd ≫ (Y ↘ S)) : HomIsOver snd S :=
  ⟨by rw [← h, comp_over]⟩

namespace IsPullback

/-- In a pullback square of two structure morphisms over `S`, the second projection is a
morphism over `S` once the first one is. -/
theorem homIsOver_snd (h : IsPullback fst snd (X ↘ S) (Y ↘ S)) : HomIsOver snd S :=
  homIsOver_snd_of_comm h.w

variable (T : C) [OverClass T S]

/-- Morphisms `T ⟶ P` over `S` into a fibre product over `S` are the pairs of morphisms
`T ⟶ X` and `T ⟶ Y` over `S`, by composition with the two projections. -/
noncomputable def homIsOverEquiv (h : IsPullback fst snd (X ↘ S) (Y ↘ S)) :
    {p : T ⟶ P // HomIsOver p S} ≃
      {a : T ⟶ X // HomIsOver a S} × {b : T ⟶ Y // HomIsOver b S} where
  toFun p :=
    have := p.2
    have := h.homIsOver_snd
    (⟨p.1 ≫ fst, inferInstance⟩, ⟨p.1 ≫ snd, inferInstance⟩)
  invFun ab :=
    have := ab.1.2
    have := ab.2.2
    ⟨h.lift ab.1.1 ab.2.1 (by rw [comp_over, comp_over]),
      ⟨by rw [← comp_over fst S, h.lift_fst_assoc, comp_over]⟩⟩
  left_inv p := Subtype.ext (h.hom_ext (h.lift_fst _ _ _) (h.lift_snd _ _ _))
  right_inv ab := Prod.ext (Subtype.ext (h.lift_fst _ _ _)) (Subtype.ext (h.lift_snd _ _ _))

variable {T} (h : IsPullback fst snd (X ↘ S) (Y ↘ S))

/-- The first component of `homIsOverEquiv` is composition with the first projection. -/
@[simp]
theorem coe_homIsOverEquiv_apply_fst (p : {p : T ⟶ P // HomIsOver p S}) :
    ((homIsOverEquiv T h p).1 : T ⟶ X) = p.1 ≫ fst :=
  (rfl)

/-- The second component of `homIsOverEquiv` is composition with the second projection. -/
@[simp]
theorem coe_homIsOverEquiv_apply_snd (p : {p : T ⟶ P // HomIsOver p S}) :
    ((homIsOverEquiv T h p).2 : T ⟶ Y) = p.1 ≫ snd :=
  (rfl)

/-- The inverse of `homIsOverEquiv` is the lift through the pullback. -/
theorem coe_homIsOverEquiv_symm_apply
    (ab : {a : T ⟶ X // HomIsOver a S} × {b : T ⟶ Y // HomIsOver b S}) :
    ((homIsOverEquiv T h).symm ab : T ⟶ P) =
      h.lift ab.1.1 ab.2.1 (by have := ab.1.2; have := ab.2.2; rw [comp_over, comp_over]) :=
  (rfl)

end IsPullback

end CategoryTheory

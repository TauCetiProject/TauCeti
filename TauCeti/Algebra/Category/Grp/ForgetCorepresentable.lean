/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable

/-!
# Evaluation of morphisms from the integers

This file records evaluation at `1` and naturality for
`AddCommGrpCat.uliftZMultiplesAddEquiv`, the additive equivalence between morphisms from the
integers and elements of an abelian group.
-/

public section

open CategoryTheory

universe w

namespace AddCommGrpCat

/-- `AddCommGrpCat.uliftZMultiplesAddEquiv` evaluates a morphism out of `ℤ` at `1`; this holds by
definition. -/
lemma uliftZMultiplesAddEquiv_apply_eq {G : AddCommGrpCat.{w}}
    (f : AddCommGrpCat.of (ULift ℤ) ⟶ G) : G.uliftZMultiplesAddEquiv f = f ⟨1⟩ :=
  (rfl)

/-- `AddCommGrpCat.uliftZMultiplesAddEquiv` is natural in the target group: composing with
`g : G ⟶ G'` applies `g` to the value at `1`. -/
lemma uliftZMultiplesAddEquiv_comp {G G' : AddCommGrpCat.{w}}
    (f : AddCommGrpCat.of (ULift ℤ) ⟶ G) (g : G ⟶ G') :
    G'.uliftZMultiplesAddEquiv (f ≫ g) = g (G.uliftZMultiplesAddEquiv f) := by
  rw [uliftZMultiplesAddEquiv_apply_eq, uliftZMultiplesAddEquiv_apply_eq,
    ConcreteCategory.comp_apply]

/-- The identity of `ℤ` corresponds to `1` under `AddCommGrpCat.uliftZMultiplesAddEquiv`. -/
lemma uliftZMultiplesAddEquiv_id :
    (AddCommGrpCat.of (ULift.{w} ℤ)).uliftZMultiplesAddEquiv (𝟙 _) = ⟨1⟩ :=
  uliftZMultiplesAddEquiv_apply_eq _

/-- The morphism out of `ℤ` corresponding to an element `g` under
`AddCommGrpCat.uliftZMultiplesAddEquiv` sends `1` to `g`. -/
lemma uliftZMultiplesAddEquiv_symm_apply_one {G : AddCommGrpCat.{w}} (g : G) :
    G.uliftZMultiplesAddEquiv.symm g ⟨1⟩ = g :=
  (uliftZMultiplesAddEquiv_apply_eq _).symm.trans (AddEquiv.apply_symm_apply _ _)

end AddCommGrpCat
